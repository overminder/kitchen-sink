{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}

module Ast2Lir
  ( ast2Lir
  ) where

import           Control.Lens
import           Control.Monad.Trans.RWS
import qualified Data.Map                as M
import           Data.Maybe              (fromMaybe)
import qualified Data.Text               as T

import           Ast
import           Lir                     hiding (mkUnique, newLabel)
import qualified Lir

type Env = M.Map Var Reg

data Ast2LirS = Ast2LirS
  { _mGraph :: LGraph
  , _mEntry :: Label
  , _mBody  :: [(Reg, LOperand)]
  , _mEnv   :: Env
  } deriving (Show)

makeLenses ''Ast2LirS

type Ast2LirM = RWS () [LTraceBlock] Ast2LirS

ast2Lir :: Stmt -> (LGraph, [LTraceBlock])
ast2Lir s = (lirS ^. mGraph, w)
  where
    (lirS, w) = execRWS (ast2Lir' s) () emptyState
    emptyState = Ast2LirS emptyLGraph (error "mEntry") (error "mBody") M.empty

ast2Lir' :: Stmt -> Ast2LirM ()
ast2Lir' s = do
  startLabel <- newLabel
  prepareNewBlockOf startLabel
  mGraph.lgEntry .= startLabel
  goS s

goS :: Stmt -> Ast2LirM ()
goS = \case
  SRet e -> do
    r <- goE e
    finishBlock (LRet r)

  SAssign v e -> do
    src <- goE e
    dst <- lookupEnvOrDefine v
    emit (dst, lOperand src)

  SSeq ss -> mapM_ goS ss

  SIf e t f -> do
    r <- lValue <$> goE e
    labelT <- newLabel
    labelF <- newLabel
    labelDone <- newLabel
    finishBlockWithNewLabel (LJnz r labelT labelF) labelT
    -- True
    goS t
    finishBlockWithNewLabel (LJmp labelDone) labelF
    -- False
    goS f
    finishBlockWithNewLabel (LJmp labelDone) labelDone
    -- Done

  SWhile e s -> do
    labelCheck <- newLabel
    labelBody <- newLabel
    labelDone <- newLabel
    finishBlockWithNewLabel (LJmp labelCheck) labelCheck
    r <- lValue <$> goE e
    finishBlockWithNewLabel (LJnz r labelBody labelDone) labelBody
    goS s
    finishBlockWithNewLabel (LJmp labelCheck) labelDone


goE :: Expr -> Ast2LirM LValue
goE = \case
  ELit i -> return (LvLit i)
  EVar v -> lValue <$> lookupEnvOrFail v
  EArith aop e1 e2 -> do
    r1 <- goE e1
    r2 <- goE e2
    dst <- mkRegV
    let
      lop = case aop of
              AAdd -> LAdd
              ALt -> LLt
    emit (dst, LoArith lop r1 r2)
    return (lValue dst)

lookupEnv :: Var -> Ast2LirM (Maybe Reg)
lookupEnv v = uses mEnv (M.lookup v)

lookupEnvOrFail :: Var -> Ast2LirM Reg
lookupEnvOrFail v = fromMaybe (error $ "Undefined variable: " ++ T.unpack v) <$> lookupEnv v

lookupEnvOrDefine :: Var -> Ast2LirM Reg
lookupEnvOrDefine v = maybe define return =<< lookupEnv v
  where
    define = do
      r <- (`RegV` Just v) <$> mkUnique
      mEnv %= M.insert v r
      return r

mkUnique :: Ast2LirM Int
mkUnique = Lir.mkUnique' mGraph

mkRegV :: Ast2LirM Reg
mkRegV = (`RegV` Nothing) <$> mkUnique

emit :: (Reg, LOperand) -> Ast2LirM ()
emit ir = mBody %= (++ [ir])

finishBlock :: LBranch -> Ast2LirM ()
finishBlock branchIr = finishBlockWithNewLabel branchIr =<< newLabel

finishBlockWithNewLabel :: LBranch -> Label -> Ast2LirM ()
finishBlockWithNewLabel exit label = do
  entry <- use mEntry
  body <- use mBody
  tell [LTraceBlock entry body exit]
  prepareNewBlockOf label

newLabel :: Ast2LirM Label
newLabel = do
  (lbl, g) <- uses mGraph Lir.newLabel
  mGraph .= g
  return lbl

prepareNewBlockOf :: Label -> Ast2LirM ()
prepareNewBlockOf lbl = do
  mEntry .= lbl
  mBody .= []
