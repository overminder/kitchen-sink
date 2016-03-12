{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}

module Expr where

import Data.String (IsString(..))
import qualified Data.Map as M
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Class
import Control.Monad (forM)

type Name = String

data Expr
  = Lit Int
  | Var Name
  | Lam [Name] Expr
  | IntAdd Expr Expr  -- Unchecked.
  | IntLt Expr Expr  -- Unchecked
  | LetRec [(Name, Expr)] Expr
  | Ap Expr [Expr]  -- Unchecked
  | If Expr Expr Expr  -- Unchecked
  | IsInt Expr
  | IsFn Expr Int
  | Abort
  deriving (Show)

instance IsString Expr where fromString = Var

-- Values represented as heap nodes.
data Node
  = NInt Int
  | NClosure [Name] Env Expr
  deriving (Show)

type Env = M.Map Name Node

type EvalM a = ReaderT Env Maybe a

mkInt :: Int -> EvalM Node
mkInt = return . NInt

mkBool :: Bool -> EvalM Node
mkBool = \case
  True -> mkInt 1
  False -> mkInt 0

mkClosure :: [Name] -> Expr -> EvalM Node
mkClosure args body = do
  env <- ask
  return (NClosure args env body)

eval :: Expr -> EvalM Node
eval = \case
  Lit i -> mkInt i
  Lam vs e -> mkClosure vs e
  Var v -> do
    Just n <- asks (M.lookup v)
    return n
  IntAdd a b -> intOp (+) id a b
  IntLt a b -> intOp (<) b2i a b
  LetRec bs body -> do
    -- Tying the knot?
    let extend bs' = (M.fromList bs' `M.union`)
    rec bs' <- withReaderT (extend bs') $ forM bs $ \(v, e) -> do
          n <- eval e
          return (v, n)
    withReaderT (extend bs') $ eval body
  Ap f as -> do
    ans <- mapM eval as
    NClosure argNames env body <- eval f
    let env' = M.fromList (zip argNames ans) `M.union` env
    withReaderT (const env') $ eval body
  If c t f -> do
    NInt b <- eval c
    if b == 1
      then eval t
      else eval f
  IsInt e -> do
    n <- eval e
    case n of
      NInt _ -> mkBool True
      _ -> mkBool False
  IsFn e arity -> do
    n <- eval e
    case n of
      NClosure args _ _ -> mkBool (length args == arity)
      _ -> mkBool False
  Abort -> lift Nothing


b2i :: Bool -> Int
b2i b = if b then 1 else 0

intOp :: (Int -> Int -> a) -> (a -> Int) -> Expr -> Expr -> EvalM Node
intOp op f a b = do
  NInt av <- eval a
  NInt bv <- eval b
  mkInt (f (av `op` bv))


fiboMain :: Expr
fiboMain = LetRec [("fibo", fibo), ("main", main)] main
  where
    fibo = Lam ["n"] $ If (IntLt "n" (Lit 2))
      "n"
      (IntAdd
       (Ap "fibo" [IntAdd "n" (Lit (-1))])
       (Ap "fibo" [IntAdd "n" (Lit (-2))]))
    main = Ap "fibo" [Lit 10]
