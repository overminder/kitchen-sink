{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE TemplateHaskell #-}

module PEval where

import           Expr

import           Control.Lens
import           Control.Monad.Trans.RWS
import qualified Data.Map                as M

-- Like Eval.Node, but is instead more concerned about the abstract value information.
data PNode
  = PInt { _iValue :: Maybe Int
         }
  | PClosure { _cArity :: Maybe Int
             , _cExpr  :: Maybe ([Name], Expr)
             , _cEnv   :: Maybe PEnv
             }
  | PUnknown
  deriving (Show)

newtype PNodeId
  = PNodeId Int
  deriving (Show, Eq, Ord)

type PEnv = M.Map Name PNodeId

mkInt :: Int -> PEvalM PNodeId
mkInt i = undefined

peval :: Expr -> PEvalM Expr
peval (Lit e) = undefined
peval (Var e) = undefined
peval (Lam e1 e2) = undefined
peval (LetRec e1 e2) = undefined
peval (IntAdd e1 e2) = undefined
peval (IntLt e1 e2) = undefined
peval (Ap e1 e2) = undefined
peval (If e1 e2 e3) = undefined
peval (IsInt e) = undefined
peval (IsFn e1 e2) = undefined
peval Abort = undefined

data PHeap = PHeap {
  _hSpace  :: M.Map PNodeId PNode,
  _hNextId :: Int
}

type PEvalM = RWST PEnv () PHeap Maybe

makeLenses ''PNode
makeLenses ''PHeap

