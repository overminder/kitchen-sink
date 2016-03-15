{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TemplateHaskell #-}

module Expr where

import Control.Lens
import Control.Arrow (second)
import Data.String (IsString(..))
import qualified Data.Map as M
import Control.Monad.Trans.RWS
import Control.Monad.Trans.Class
import Control.Monad (forM, (<=<))

type Name = String

data Expr
  -- | Core forms
  = Lit Int
  | Var Name
  | Lam [Name] Expr
  | LetRec [(Name, Expr)] Expr

  -- | Typed ops
  | IntAdd Expr Expr  -- Unchecked.
  | IntLt Expr Expr  -- Unchecked
  | Ap Expr [Expr]  -- Unchecked
  | If Expr Expr Expr  -- Unchecked

  -- | Guards
  | IsInt Expr
  | IsFn Expr Int

  -- | XXX
  | Abort
  deriving (Show)

instance IsString Expr where fromString = Var

-- Values represented as heap nodes.
data Node
  = NInt Int
  | NClosure [Name] Env Expr

  -- | Used by LetRec to represent boxes.
  | NIndirect (Maybe NodeId)
  deriving (Show)

newtype NodeId
  = NodeId Int
  deriving (Show, Eq, Ord)

type Env = M.Map Name NodeId

data Heap = Heap {
  _hSpace :: M.Map NodeId Node,
  _hNextId :: Int
}

makeLenses ''Heap

emptyHeap :: Heap
emptyHeap = Heap M.empty 1

-- Make a fresh dangling NodeId.
freshNodeId :: EvalM NodeId
freshNodeId = NodeId <$> use hNextId <* (hNextId += 1)

setNode :: NodeId -> Node -> EvalM ()
setNode nid n = hSpace %= M.insert nid n

derefNode0 :: NodeId -> EvalM Node
derefNode0 = lift <=< (uses hSpace . M.lookup)

derefNode :: NodeId -> EvalM Node
derefNode n = do
  n' <- derefNode0 n
  case n' of
    NIndirect (Just n'') -> derefNode n''
    _ -> return n'

type EvalM a = RWST Env () Heap Maybe a

mkInt :: Int -> EvalM NodeId
mkInt = mkNode <=< (return . NInt)

mkBool :: Bool -> EvalM NodeId
mkBool = \case
  True -> mkInt 1
  False -> mkInt 0

mkClosure :: [Name] -> Expr -> EvalM NodeId
mkClosure args body = do
  env <- ask
  mkNode (NClosure args env body)

mkNode :: Node -> EvalM NodeId
mkNode n = do
  nid <- freshNodeId
  setNode nid n
  return nid

withR :: (r -> r') -> RWST r' w s m a -> RWST r w s m a
withR f = withRWST (\r s -> (f r, s))

-- Without following the indirections.
eval :: Expr -> EvalM NodeId
eval = \case
  Lit i -> mkInt i
  Lam vs e -> mkClosure vs e
  Var v ->
    do Just n <- asks (M.lookup v)
       return n
  IntAdd a b -> intOp (+) id a b
  IntLt a b -> intOp (<) b2i a b
  LetRec bs body ->
    do ns <- forM bs $ \(v, e) ->
         do n <- mkNode (NIndirect Nothing)
            return (v, (n, e))
       let extend xs = (M.fromList (map (second fst) xs) `M.union`)
       withR (extend ns) $
             do nvals <- forM ns $ \(_, (n, e)) ->
                  do n' <- NIndirect . Just <$> eval e
                     return (n, n')
                mapM_ (uncurry setNode) nvals
                eval body
  Ap f as -> do
    ans <- mapM eval as
    NClosure argNames env body <- derefNode =<< eval f
    let env' = M.fromList (zip argNames ans) `M.union` env
    withR (const env') $ eval body
  If c t f -> do
    NInt b <- derefNode =<< eval c
    if b == 1
      then eval t
      else eval f
  IsInt e -> do
    n <- derefNode =<< eval e
    case n of
      NInt _ -> mkBool True
      _ -> mkBool False
  IsFn e arity -> do
    n <- derefNode =<< eval e
    case n of
      NClosure args _ _ -> mkBool (length args == arity)
      _ -> mkBool False
  Abort -> lift Nothing


b2i :: Bool -> Int
b2i b = if b then 1 else 0

intOp :: (Int -> Int -> a) -> (a -> Int) -> Expr -> Expr -> EvalM NodeId
intOp binOp f a b = do
  NInt av <- derefNode =<< eval a
  NInt bv <- derefNode =<< eval b
  mkInt (f (av `binOp` bv))


fiboMain :: Expr
fiboMain = LetRec [("fibo", fibo), ("main", main)] (Ap "main" [])
  where
    fibo = Lam ["n"] $ If (IntLt "n" (Lit 2))
      "n"
      (IntAdd
       (Ap "fibo" [IntAdd "n" (Lit (-1))])
       (Ap "fibo" [IntAdd "n" (Lit (-2))]))
    main = Lam [] $ Ap "fibo" [Lit 10]

evalMain :: Expr -> Maybe Node
evalMain e = fst <$> evalRWST (derefNode =<< eval e) M.empty emptyHeap
