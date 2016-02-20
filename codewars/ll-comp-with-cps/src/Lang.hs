module Lang where


data Stmt
  = SWhile Expr Stmt
  | SIf Expr Stmt Stmt
  | SRet Expr
  | SExpr Expr
  | SDef Name Expr
  deriving (Show)

data Expr
  = EVar Name
  | ELit Int
  | ECall Expr [Expr]
  | EPrimOp PrimOp [Expr]
  deriving (Show)

data PrimOp
  = PrimPrint
  deriving (Show)

data Function = Function Name [Name] Stmt
