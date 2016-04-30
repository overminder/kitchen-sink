{-# LANGUAGE TemplateHaskell #-}

module Lir where

import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import qualified Data.Text as T
import qualified Data.Map as M
import Control.Lens

-- SSA IR.

data Reg
  = RegV Int
  | RegP T.Text
  deriving (Show, Eq, Ord)

data Label
  = LAnonymous Int
  deriving (Show, Eq, Ord)

data Lir
  = LAdd Reg Reg Reg
  | LLt Reg Reg Reg
  | LMovI Reg Int
  | LMovR Reg Reg

  | LJnz Reg Label Label
  | LJmp Label
  | LRet Reg
  deriving (Show, Eq, Ord)

data LBlock = LBlock
  { _lbLabel :: !Label
  , _lbBody :: [Lir]
  , _lbExit :: !Lir
  } deriving (Show)

data LGraph = LGraph
  { _lgNodes :: M.Map Label LBlock
  , _lgUniqueGen :: !Int
  } deriving (Show)

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


isExit :: Lir -> Bool
isExit = \case
  LJnz {} -> True
  LJmp {} -> True
  LRet {} -> True
  _ -> False

instance Pretty Reg where
  pretty = \case
    RegV i -> text "v" <> int i
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
    LJnz r t f -> simpl "jnz" [pretty r, pretty t, pretty f]
    LJmp d -> simpl "jmp" [pretty d]
    LRet r -> simpl "ret" [pretty r]

    where
      commaSep :: [Doc] -> Doc
      commaSep = hcat . punctuate comma

      simpl tag xs = text tag <+> commaSep xs

instance Pretty LBlock where
  pretty b = pretty (b ^. lbLabel) <+> text "{"
    <$$> (indent 2 . vsep . map pretty $ b ^. lbBody ++ [b ^. lbExit])
    <$$> text "}"

instance Pretty LGraph where
  pretty g = vsep (g ^. lgNodes . to (map pretty . M.elems))
