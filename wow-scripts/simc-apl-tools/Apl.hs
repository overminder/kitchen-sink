module Apl where

data AplStmt
  = SVar String Exp
  deriving (Show, Eq)

data Exp
  = EVar String
  | EInt Int
  | EProp Exp String
  | EBOp BRator Exp Exp
  | EUOp URator Exp
  deriving (Show, Eq)

data BRator
  = BRPlus | BRMinus | BRRem | BRMult
  | BRAnd | BROr
  | BRGt | BRLt
  deriving (Show, Eq)

data URator = URNot | URFloor
  deriving (Show, Eq)

