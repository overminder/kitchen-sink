{-# LANGUAGE OverloadedStrings #-}

-- | Let's say we want to write an interpreter.
module Lib where

import           Control.Applicative (liftA2)
import           Control.Monad       (join)
import           Data.Foldable       (foldrM)
import qualified Data.Map            as M
import           Data.Maybe          (fromJust)
import           Data.String         (IsString (..))


-- | With the terms defined as:
type Var = String

data Term
  = TLit Int
  | TVar Var
  | TAdd Term Term
  | TLam Var Term
  | TAp Term Term
  | TLetRec [(Var, Term)] Term
  | TLet [(Var, Term)] Term
  deriving (Show)

instance IsString Term where
  fromString = TVar

-- | And the evaluation environment defined as:

type Env = M.Map Var Value

emptyEnv :: Env
emptyEnv = M.empty

data Value
  = VInt Int
  | VLam (Value -> Maybe Value)

instance Show Value where
  show (VInt i) = show i
  show (VLam _) = "<Lambda>"

-- | And the evaluation defined as:

eval :: Env -> Term -> Maybe Value
eval g t = case t of
  TLit i -> pure $ VInt i
  TVar n -> M.lookup n g
  TAdd t1 t2 -> join (liftA2 (binIntOp (+)) (go t1) (go t2))
  TLam n t -> pure $ VLam $ \ v -> eval (M.insert n v g) t
  TAp f a -> join (liftA2 apply (go f) (go a))
  TLetRec bs t -> eval (bindAllRec g bs) t
  TLet bs t -> bindAll g bs >>= (`eval` t)
  where
    go = eval g

    binIntOp :: (Int -> Int -> Int) -> Value -> Value -> Maybe Value
    binIntOp op (VInt a) (VInt b) = pure $ VInt (op a b)
    binIntOp _ _ _ = Nothing

    apply :: Value -> Value -> Maybe Value
    apply (VLam f) a = f a
    apply _ _ = Nothing

    -- | This is where tying the knot happens.
    -- Still, this is not a good enough example as we are forced to use
    -- `fromJust` here and abandoning error handling, or it will be too strict.
    -- Can we do better?
    bindAllRec :: Env -> [(Var, Term)] -> Env
    bindAllRec g bs = let ns = map fst bs
                          vs = map (fromJust . eval g' . snd) bs
                          g' = (`M.union` g) . M.fromList . zip ns $ vs
                       in g'

    bindAll :: Env -> [(Var, Term)] -> Maybe Env
    bindAll g bs = (`M.union` g) <$> foldrM (bindOne g) g bs

    bindOne :: Env -> (Var, Term) -> Env -> Maybe Env
    bindOne g (n, t) g' = eval g t >>= \ v -> pure (M.insert n v g')

sample :: Term
sample = TLetRec
  [ ("i", "s" `TAp` "k" `TAp` "k")
  , ("s", TLam "f" $ TLam "g" $ TLam "x" (("f" `TAp` "x") `TAp` ("g" `TAp` "x")))
  , ("k", TLam "x" $ TLam "y" "x")
  ] "i" `TAp` (TLit 42)

runSample = print (eval emptyEnv sample)
