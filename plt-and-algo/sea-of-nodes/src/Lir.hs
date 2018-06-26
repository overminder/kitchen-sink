{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE UndecidableInstances #-}

module Lir where

import           Control.Lens
import           Control.Monad                     (unless)
import           Control.Monad.Representable.State (MonadState)
import           Control.Monad.Trans.State         (evalState)
import qualified Data.Map                          as M
import           Data.Maybe                        (fromMaybe, mapMaybe)
import qualified Data.Set                          as S
import qualified Data.Text                         as T
import           Text.PrettyPrint.ANSI.Leijen      hiding ((<$>))

-- SSA IR.

data Reg
  = RegV Int (Maybe T.Text)
  | RegP T.Text
  deriving (Show, Eq, Ord)

newtype Label = LAnonymous Int
  deriving (Show, Eq, Ord)

data LOperand
  = LoAtom LValue
  | LoArith LArithOp LValue LValue
  | LoPhi [(LValue, Label)]
  deriving (Show, Eq, Ord)

data LArithOp
  = LAdd
  | LLt
  deriving (Show, Eq, Ord)

data LValue
  = LvReg Reg
  | LvLit Int
  deriving (Show, Eq, Ord)

data LBlock = LBlock
  { _lbLabel :: Label
  , _lbDefs  :: M.Map Reg LOperand
  , _lbExit  :: LBranch
  } deriving (Show)

-- Not necessarily SSA. Used for graph building and trace reconstruction.
data LTraceBlock = LTraceBlock
  { _ltbFirst :: Label
  , _ltbMid :: [(Reg, LOperand)]
  , _ltbLast :: LBranch
  } deriving (Show, Eq, Ord)

data LBranch
  = LJnz LValue Label Label
  | LJmp Label
  | LRet LValue
  deriving (Show, Eq, Ord)

data LGraph = LGraph
  { _lgDefs      :: M.Map Reg Label
  , _lgEntry     :: Label
  , _lgBlocks    :: M.Map Label LBlock
  , _lgUniqueGen :: !Int
  } deriving (Show)

data LDefUse = LDefUse
  { _lDef :: [Reg]
  , _lUse :: [LValue]
  } deriving (Show)

-- Erased. Useful for analysis.
data Lir
  = LirFirst Label
  | LirMid Reg LOperand
  | LirLast LBranch
  deriving (Show)

makeLenses ''LGraph
makeLenses ''LBlock

makeLenses ''LTraceBlock
makeLenses ''LDefUse

class IsLOperand a where
  lOperand :: a -> LOperand

class IsLValue a where
  lValue :: a -> LValue

instance IsLValue LValue where
  lValue = id

instance IsLValue a => IsLOperand a where
  lOperand = LoAtom . lValue

instance IsLValue Reg where
  lValue = LvReg

instance IsLValue Int where
  lValue = LvLit

irDefUse :: Lens' Lir LDefUse
irDefUse f = \case
  LirFirst label -> fmap (lhs $ \[] [] -> LirFirst label) (rhs [] [])
  LirMid d ss -> fmap (lhs $ \[d'] ss' -> LirMid d' (ss & opUses .~ ss'))
    (rhs [d] (ss ^. opUses))
  LirLast br -> fmap (lhs $ \[] ss' -> LirLast (br & branchUses .~ ss'))
    (rhs [] (br ^. branchUses))
  where
    lhs g (LDefUse ds us) = g ds us
    rhs ds us = f (LDefUse ds us)


lvReg :: Lens' LValue [Reg]
lvReg f = \case
  LvReg r -> fmap (\[r'] -> LvReg r') (f [r])
  LvLit i -> fmap (\[] -> LvLit i) (f [])

opUses :: Lens' LOperand [LValue]
opUses f = \case
  LoAtom v -> fmap (\[v'] -> LoAtom v') (f [v])
  LoArith aop v1 v2 -> fmap (\[v1', v2'] -> LoArith aop v1' v2') (f [v1, v2])
  LoPhi vls -> fmap (\vs' -> LoPhi (setFsts vs' vls)) (f (map fst vls))
  where
    setFsts xs ys = zip xs (map snd ys)

branchJumpsTo :: Lens' LBranch [Label]
branchJumpsTo f = \case
  LJnz r lt lf -> fmap (\[lt', lf'] -> LJnz r lt' lf') (f [lt, lf])
  LJmp lbl -> fmap (\[lbl'] -> LJmp lbl') (f [lbl])
  LRet r -> fmap (\[] -> LRet r) (f [])

branchUses :: Lens' LBranch [LValue]
branchUses f = \case
  LJnz r lt lf -> fmap (\[r'] -> LJnz r' lt lf) (f [r])
  LJmp lbl -> fmap (\[] -> LJmp lbl) (f [])
  LRet r -> fmap (\[r'] -> LRet r') (f [r])

emptyLGraph :: LGraph
emptyLGraph = LGraph M.empty (error "emptyLGraph.entry") M.empty 1

mkUnique :: LGraph -> (Int, LGraph)
mkUnique g = (g ^. lgUniqueGen, g & lgUniqueGen +~ 1)

mkUnique' :: MonadState s m => Lens s s LGraph LGraph -> m Int
mkUnique' s2g = do
  (i, g) <- uses s2g mkUnique
  s2g .= g
  return i

putBlock :: LBlock -> LGraph -> LGraph
putBlock b = putDefs . (lgBlocks %~ M.insert label b)
  where
    label = b ^. lbLabel
    putDefs = lgDefs %~ M.union (M.fromList (zip (b ^. lbDefs.to M.keys) (repeat label)))

newLabel :: LGraph -> (Label, LGraph)
newLabel g = (LAnonymous label, g')
  where
    (label, g') = mkUnique g

-- Could also cache the predecessors.
predLabels :: Label -> LGraph -> [Label]
predLabels label g = preds
  where
    preds = g ^. lgBlocks.to (M.keys . M.filter jumpsToB)
    jumpsToB b' = label `elem` (b' ^. lbExit.branchJumpsTo)

instance Pretty Reg where
  pretty = \case
    RegV i name -> (text . maybe "$t_" T.unpack) name <> int i
    RegP s -> text (T.unpack s)

instance Pretty Label where
  pretty (LAnonymous i) = text "L" <> int i

instance Pretty LValue where
  pretty = \case
    LvReg r -> pretty r
    LvLit i -> pretty i

instance Pretty LOperand where
  pretty = \case
    LoArith lop a b -> pretty a <+> aOpToS lop <+> pretty b
    LoAtom a -> pretty a
    LoPhi ss -> text "phi" <+> commaSep (map pretty ss)
    where
      aOpToS = text . \case
        LAdd -> "+"
        LLt -> "<"

commaSep :: [Doc] -> Doc
commaSep = hcat . punctuate comma

instance Pretty LBranch where
  pretty = \case
    LJnz r t f -> simpl "jnz" [pretty r, pretty t, pretty f]
    LJmp d -> simpl "jmp" [pretty d]
    LRet r -> simpl "ret" [pretty r]
    where
      simpl tag xs = text tag <+> commaSep xs

instance Pretty Lir where
  pretty = \case
    LirFirst label -> pretty label <> colon
    LirMid d s -> prettyAssign d s
    LirLast ir -> pretty ir
    where
      prettyAssign a b = pretty a <+> equals <+> pretty b

instance Pretty LTraceBlock where
  pretty (LTraceBlock label body exit)
    = prettyBody label (map (uncurry LirMid) body ++ [LirLast exit])

bfsBlocks :: LGraph -> [LBlock]
bfsBlocks g = go [g ^. lgEntry] S.empty
  where
    go workList visited = case workList of
      [] -> []
      x:xs | S.member x visited -> go xs visited
           | otherwise ->
             let b = g ^. lgBlocks.to (M.! x)
                 succs = b ^. lbExit.branchJumpsTo
             in b : go (xs ++ succs) (S.insert x visited)

instance Pretty LGraph where
  pretty = vsep . map pretty . bfsBlocks

-- Topological sort by DFS.
-- Doesn't need an temp set since we don't have cycles in the non-phi definitions.
topSortDefs :: M.Map Reg LOperand -> [(Reg, LOperand)]
topSortDefs m = evalState (mapM_ go (M.keys m) *> use _2) (S.empty, [])
  where
    go r = do
      visited <- uses _1 (S.member r)
      unless visited $ do
        -- The definition could be outside of this block if that's the case we just
        -- treat the lop as having no uses.
        let
          mbLop = M.lookup r m
          lopUses = fromMaybe [] ((^. opUses) <$> mbLop)
        _1 %= S.insert r
        mapM_ go (mapMaybe valueToReg lopUses)
        maybe (return ()) (\lop -> _2 %= ((r, lop):)) mbLop

    valueToReg (LvReg r) = Just r
    valueToReg _ = Nothing

instance Pretty LBlock where
  pretty b = prettyBody (b ^. lbLabel)
    (defsToIr phis ++ (lirMid . reverse . topSortDefs) nonPhis ++ [b ^. lbExit.to LirLast])
    where
      (phis, nonPhis) = M.partition isPhi (b ^. lbDefs)
      isPhi = \case { LoPhi {} -> True; _ -> False }
      defsToIr = lirMid . M.toList
      lirMid = map (uncurry LirMid)

prettyBody :: Label -> [Lir] -> Doc
prettyBody label irs = pretty label <+> text "{"
  <$$> (indent 2 . vsep . map pretty $ irs)
  <$$> text "}"
