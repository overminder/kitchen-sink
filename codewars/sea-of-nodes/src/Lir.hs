{-# LANGUAGE TemplateHaskell, RankNTypes #-}

module Lir where

import Control.Monad.Representable.State
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import qualified Data.Text as T
import qualified Data.Map as M
import Control.Lens

-- SSA IR.

data Reg
  = RegV Int (Maybe T.Text)
  | RegP T.Text
  deriving (Show, Eq, Ord)

newtype Label = LAnonymous Int
  deriving (Show, Eq, Ord)

data Lir
  = LAdd Reg Reg Reg
  | LLt Reg Reg Reg
  | LMovI Reg Int
  | LMovR Reg Reg

  | LPhi Reg [Reg]

  | LJnz Reg Label Label
  | LJmp Label
  | LRet Reg
  deriving (Show, Eq, Ord)

data LBlock = LBlock
  { _lbLabel :: !Label
  , _lbPhis :: [Lir]
  , _lbBody :: [Lir]
  , _lbExit :: !Lir
  } deriving (Show)

data LGraph = LGraph
  { _lgNodes :: M.Map Label LBlock
  , _lgUniqueGen :: !Int
  } deriving (Show)

data LDefUse = LDefUse
  { _lDef :: [Reg]
  , _lUse :: [Reg]
  } deriving (Show)

makeLenses ''LDefUse

type DUTuple = ([Reg], [Reg])

duTuple :: Functor f => (LDefUse -> f LDefUse) -> DUTuple -> f DUTuple
duTuple f (ds, us) = fmap (\(LDefUse ds' us') -> (ds', us')) (f $ LDefUse ds us)

irJumpsTo :: Functor f => ([Label] -> f [Label]) -> Lir -> f Lir
irJumpsTo f = \case
  LJnz r lt lf -> fmap (\[lt', lf'] -> LJnz r lt' lf') (f [lt, lf])
  LJmp lbl -> fmap (\[lbl'] -> LJmp lbl') (f [lbl])
  x@_ -> fmap (\[] -> x) (f [])

irDefUse :: Functor f => (LDefUse -> f LDefUse) -> Lir -> f Lir
irDefUse = defUse'.duTuple

defUse' :: Functor f => (DUTuple -> f DUTuple) -> Lir -> f Lir
defUse' mkF = mkL . \case
  LAdd d a b -> (\([d'], [a', b']) -> LAdd d' a' b', ([d], [a, b]))
  LLt d a b -> (\([d'], [a', b']) -> LLt d' a' b', ([d], [a, b]))
  LMovI d i -> (\([d'], []) -> LMovI d' i, ([d], []))
  LMovR d s -> (\([d'], [s']) -> LMovR d' s', ([d], [s]))
  LPhi d ss -> (\([d'], ss') -> LPhi d' ss', ([d], ss))
  LJnz s t f -> (\([], [s']) -> LJnz s' t f, ([], [s]))
  LJmp x -> (\([], []) -> LJmp x, ([], []))
  LRet s -> (\([], [s']) -> LRet s', ([], [s]))
  where
    mkL (setDU, getDU) = fmap setDU (mkF getDU)


makeLenses ''LBlock
makeLenses ''LGraph

emptyLGraph :: LGraph
emptyLGraph = LGraph M.empty 1

insertBlock :: LBlock -> LGraph -> LGraph
insertBlock b = lgNodes %~ M.insert (b ^. lbLabel) b

mkUnique :: LGraph -> (Int, LGraph)
mkUnique g = (g ^. lgUniqueGen, g & lgUniqueGen +~ 1)

appendBody :: Lir -> LBlock -> LBlock
appendBody ir = lbBody %~ (++ [ir])

predLabels :: Label -> LGraph -> [Label]
predLabels label g = map (^. lbLabel) . filter isSucc . M.elems $ g ^. lgNodes
  where
    isSucc :: LBlock -> Bool
    isSucc b = label `elem` b ^. lbExit.irJumpsTo

mkUnique' :: MonadState s m => Lens s s LGraph LGraph -> m Int
mkUnique' s2g = do
  (i, g) <- uses s2g mkUnique
  s2g .= g
  return i

isExit :: Lir -> Bool
isExit = \case
  LJnz {} -> True
  LJmp {} -> True
  LRet {} -> True
  _ -> False

instance Pretty Reg where
  pretty = \case
    RegV i name -> (text . maybe "$t_" T.unpack) name <> int i
    RegP s -> text (T.unpack s)

instance Pretty Label where
  pretty = \case
    LAnonymous i -> text "L" <> int i

instance Pretty Lir where
  pretty = \case
    LAdd d a b -> simpl "add" (map pretty [d, a, b])
    LLt d a b -> simpl "lt" (map pretty [d, a, b])
    LMovI d i -> simpl "mov" [pretty d, pretty i]
    LMovR d s -> simpl "mov" (map pretty [d, s])
    LPhi d ss -> simpl "phi" (map pretty (d:ss))

    LJnz r t f -> simpl "jnz" [pretty r, pretty t, pretty f]
    LJmp d -> simpl "jmp" [pretty d]
    LRet r -> simpl "ret" [pretty r]

    where
      commaSep :: [Doc] -> Doc
      commaSep = hcat . punctuate comma

      simpl tag xs = text tag <+> commaSep xs

instance Pretty LBlock where
  pretty b = pretty (b ^. lbLabel) <+> text "{"
    <$$> (indent 2 . vsep . map pretty $ b ^. lbPhis ++ b ^. lbBody ++ [b ^. lbExit])
    <$$> text "}"

instance Pretty LGraph where
  pretty g = vsep (g ^. lgNodes . to (map pretty . M.elems))
