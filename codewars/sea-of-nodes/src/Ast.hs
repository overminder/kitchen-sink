{-# LANGUAGE OverloadedStrings #-}

module Ast
  ( module Ast
  , module Text.PrettyPrint.ANSI.Leijen
) where

import qualified Data.Text as T
import Data.String (IsString(..))
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import qualified Text.PrettyPrint.ANSI.Leijen as P

-- A simple imperative AST.

type Var = T.Text

prettyVar :: T.Text -> Doc
prettyVar = text . T.unpack

data Stmt
  = SAssign Var Expr
  | SRet Expr
  | SSeq [Stmt]
  | SIf Expr Stmt Stmt
  | SWhile Expr Stmt
  deriving (Show, Eq)

instance Pretty Stmt where
  pretty = \case
    SAssign v e -> prettyVar v <+> equals <+> pretty e
    SRet e -> text "return" <+> pretty e
    SSeq ss -> text "{" <$$> (indent kIndentLevel . vsep . map pretty $ ss) <$$> text "}"
    SIf e t f -> text "if" <+> pretty e
      P.<+> text "then" <+> pretty t
      P.<$> text "else" <+> pretty f
    SWhile e s -> text "while" <+> pretty e <+> text "do" <+> pretty s

kIndentLevel :: Int
kIndentLevel = 2

data Expr
  = EArith ArithOp Expr Expr
  | EVar Var
  | ELit Int
  deriving (Show, Eq)

instance IsString Expr where
  fromString = EVar . fromString

instance Pretty Expr where
  pretty = \case
    EArith op e1 e2 -> prettyP e1 <+> pretty op <+> prettyP e2
    EVar v -> prettyVar v
    ELit i -> int i

-- | Adds parenthesis to non-atomic exprs.
prettyP :: Expr -> Doc
prettyP e = mightAddParen (pretty e)
  where
    needsParen = \case
      EVar _ -> False
      ELit _ -> False
      EArith {} -> True

    mightAddParen = if needsParen e then parens else id

data ArithOp
  = AAdd
  | ALt
  deriving (Show, Eq)

instance Pretty ArithOp where
  pretty = text . \case
    AAdd -> "+"
    ALt -> "<"

(!+) :: Expr -> Expr -> Expr
(!+) = EArith AAdd

(!<) :: Expr -> Expr -> Expr
(!<) = EArith ALt

simpleBlock :: Stmt
simpleBlock = SSeq [
  SAssign "a" (ELit 1),
  SAssign "b" (ELit 2),
  SAssign "c" ("a" !+ "b" !+ "a"),
  SAssign "a" ("c" !+ "b"), -- Dead
  SAssign "b" ("c" !+ "b"),
  SRet "b"
  ]

simpleLoop :: Stmt
simpleLoop = SSeq [
  SAssign "i" (ELit 0),
  SAssign "s" (ELit 0),
  SWhile ("i" !< ELit 100) $
  SSeq [ SAssign "s" ("s" !+ "i")
       , SAssign "i" ("i" !+ ELit 1)
       ],
  SRet "s"
  ]
