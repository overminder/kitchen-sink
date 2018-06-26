module CEK where

import qualified Data.Map as M

type Name = String

-- Or, code
data Expr
  -- x
  = EVar Name
  -- M_1 M_2
  | EAp Expr Expr
  -- \x. M
  | ELam Lam
  -- W
  | EValue Value
  deriving (Show, Eq)

data Lam = Lam Name Expr
  deriving (Show, Eq)

data Value 
  = VInt Int
  -- clos(\x. M, E)
  | VClo Lam Env
  deriving (Show, Eq)

type Env = M.Map Name Value

data Frame
  -- (O M_2 E)
  = FApFunc Expr Env
  -- (W O)
  | FApArg Value
  deriving (Show, Eq)

type Kont = [Frame]
type CEK = (Expr, Env, Kont)

data HaltReason
  = NoSuchTransition
  | Ret Value
  | UnboundVar Name
  deriving (Show, Eq)

type MachM = Either HaltReason

lookupName :: Name -> Env -> MachM Value
lookupName x e = maybe (Left ub) Right (M.lookup x e) 
 where
  ub = UnboundVar x

emptyEnv :: Env
emptyEnv = M.empty

emptyKont :: Kont
emptyKont = []

step :: CEK -> MachM CEK
step = \case
  (EVar x, e, k) -> do
    w <- lookupName x e
    pure (EValue w, e, k)

  (EAp m1 m2, e, k) ->
    pure (m1, e, (FApFunc m2 e):k)

  (ELam lam, e, k) ->
    pure (EValue (VClo lam e), e, k)

  (EValue w, e1, (FApFunc m e2):k) ->
    pure (m, e2, (FApArg w):k)

  (EValue w, e1, (FApArg (VClo (Lam x m) e2)):k) ->
    pure (m, M.insert x w e2, k)

  (EValue w, e, []) ->
    Left (Ret w)

  _ ->
    Left NoSuchTransition

steps :: CEK -> (CEK, HaltReason)
steps = go
 where
  go cek = case step cek of
    Left e -> (cek, e)
    Right cek' -> go cek'

evalSteps :: CEK -> Maybe Value
evalSteps = fromR . steps
 where
  fromR = \case
    (_, Ret x) -> Just x
    _ -> Nothing

