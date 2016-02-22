module Lang where

import Data.String (IsString(..))

type Name = String

data Stmt
  = SWhile Expr Stmt
  | SIf Expr Stmt Stmt
  | SRet Expr
  | SExpr Expr
  | SDef Name Expr
  | SBlock [Stmt]
  | SPrimPrint Expr
  deriving (Show)

instance IsString Expr where
  fromString = EVar

data Expr
  = EVar Name
  | ELit Int
  | ECall Expr [Expr]
  | EPrimLt Expr Expr
  | EPrimAdd Expr Expr
  deriving (Show)

data Function = Function Name [Name] Stmt
  deriving (Show)

