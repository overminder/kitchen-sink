{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}

module Ast2Lir
  ( ast2Lir
  ) where

import           Control.Lens
import           Control.Monad.Trans.State
import qualified Data.Map                  as M
import           Data.Maybe                (fromMaybe)
import qualified Data.Text                 as T

import           Ast
import           Lir                       hiding (mkUnique, newLabel)
import qualified Lir

type Env = M.Map Var Reg

data Ast2LirS = Ast2LirS
  { _mGraph :: LGraph
  , _mEntry :: Label' 'Region
  , _mBody  :: [Label' 'Prim]
  , _mEnv   :: Env
  } deriving (Show)

makeLenses ''Ast2LirS

type Ast2LirM = State Ast2LirS

ast2Lir :: Stmt -> LGraph
ast2Lir s = execState (ast2Lir' s) emptyState ^. mGraph
  where
    emptyState = Ast2LirS emptyLGraph (error "mEntry") (error "mBody") M.empty

ast2Lir' :: Stmt -> Ast2LirM ()
ast2Lir' s = do
  startLabel <- newLabel
  prepareNewBlockOf startLabel
  mGraph.lgStart .= startLabel
  goS s

goS :: Stmt -> Ast2LirM ()
goS = \case
  SRet e -> do
    r <- lValue <$> goE e
    here <- use mEntry
    finishBlock (LRet here r)

  SAssign v e -> do
    src <- goE e
    dst <- lookupEnvOrDefine v
    here <- use mEntry
    emit (lAssign here dst src)

  SSeq ss -> mapM_ goS ss

  SIf e t f -> do
    r <- lValue <$> goE e
    labelT <- newLabel
    labelF <- newLabel
    labelDone <- newLabel
    here <- use mEntry
    finishBlockWithNewLabel (LJnz here r labelT labelF) labelT
    -- True
    goS t
    finishBlockWithNewLabel (LJmp labelT labelDone) labelF
    -- False
    goS f
    finishBlockWithNewLabel (LJmp labelF labelDone) labelDone
    -- Done

  SWhile e s -> do
    labelCheck <- newLabel
    labelBody <- newLabel
    labelDone <- newLabel
    here <- use mEntry
    finishBlockWithNewLabel (LJmp here labelCheck) labelCheck
    r <- lValue <$> goE e
    finishBlockWithNewLabel (LJnz labelCheck r labelBody labelDone) labelBody
    goS s
    finishBlockWithNewLabel (LJmp labelBody labelCheck) labelDone


goE :: Expr -> Ast2LirM Reg
goE = \case
  ELit i -> do
    r <- mkRegV
    here <- use mEntry
    emit (lAssign here r i)
    return r
  EVar v -> lookupEnvOrFail v
  EArith aop e1 e2 -> do
    r1 <- lValue <$> goE e1
    r2 <- lValue <$> goE e2
    dst <- mkRegV
    let
      lop = case aop of
              AAdd -> LAdd
              ALt -> LLt
    here <- use mEntry
    emit (LPrim here dst (LoArith lop r1 r2))
    return dst

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

emit :: Lir' 'Prim -> Ast2LirM ()
emit ir = do
  irLabel <- emitAny ir
  mBody %= (++ [irLabel])

emitAny :: Lir' a -> Ast2LirM (Label' a)
emitAny ir = do
  irLabel <- newLabel
  mGraph %= putIr irLabel ir
  return irLabel

finishBlock :: Lir' 'Exit -> Ast2LirM ()
finishBlock ir = finishBlockWithNewLabel ir =<< newLabel

finishBlockWithNewLabel :: Lir' 'Exit -> Label' 'Region -> Ast2LirM ()
finishBlockWithNewLabel exit label = do
  exitLabel <- emitAny exit
  entry <- use mEntry
  block <- LSeq <$> use mBody <*> pure exitLabel
  mGraph %= putIr entry block
  prepareNewBlockOf label

newLabel :: Ast2LirM (Label' a)
newLabel = do
  (lbl, g) <- uses mGraph Lir.newLabel
  mGraph .= g
  return lbl

prepareNewBlockOf :: Label' 'Region -> Ast2LirM ()
prepareNewBlockOf lbl = do
  mEntry .= lbl
  mBody .= []
