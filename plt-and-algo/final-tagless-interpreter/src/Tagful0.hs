module Tagful0
    ( here
    , before
    , add
    , lambda
    , eval
    ) where

-- Initial-style tagful implementation.

type Ix = Int
type Val = Int

data Term a where
  TVar :: Ix -> Term Val
  TAdd :: Term Val -> Term Val -> Term Val
  TLambda :: Term a -> Term (Ix -> a)

eval :: Term a -> [Val] -> a
eval (TVar ix) env = env !! ix
eval (TAdd a b) env = eval a env + eval b env
eval (TLambda b) env = \ a -> eval b (a:env)

here = TVar 0
before :: Term Val -> Term Val
before (TVar v) = TVar (v + 1)
add = TAdd
lambda = TLambda


