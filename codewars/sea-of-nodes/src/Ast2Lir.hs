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
  , _mBody  :: [Lir' 'Prim]
  , _mEnv   :: Env
  } deriving (Show)

makeLenses ''Ast2LirS

type Ast2LirM = State Ast2LirS

ast2Lir :: Stmt -> LGraph
ast2Lir s = execState (ast2Lir' s) emptyState ^. mGraph
  where
    emptyState = Ast2LirS emptyLGraph undefined undefined M.empty

ast2Lir' :: Stmt -> Ast2LirM ()
ast2Lir' s = do
  prepareNewBlockOf =<< newLabel
  goS s

goS :: Stmt -> Ast2LirM ()
goS = \case
  SRet e -> do
    r <- lValue <$> goE e
    lbl <- newLabel
    finishBlock (LRet lbl r)

  SAssign v e -> do
    src <- goE e
    dst <- lookupEnvOrDefine v
    lbl <- newLabel
    emit (lAssign lbl dst src)

  SSeq ss -> mapM_ goS ss

  SIf e t f -> do
    r <- lValue <$> goE e
    labelT <- newLabel
    labelF <- newLabel
    labelDone <- newLabel
    lbl <- newLabel
    finishBlockWithNewLabel (LJnz lbl r labelT labelF) labelT
    -- True
    goS t
    lbl' <- newLabel
    finishBlockWithNewLabel (LJmp lbl' labelDone) labelF
    -- False
    goS f
    lbl'' <- newLabel
    finishBlockWithNewLabel (LJmp lbl'' labelDone) labelDone
    -- Done

  SWhile e s -> do
    labelCheck <- newLabel
    labelBody <- newLabel
    labelDone <- newLabel
    lbl <- newLabel
    finishBlockWithNewLabel (LJmp lbl labelCheck) labelCheck
    r <- lValue <$> goE e
    lbl' <- newLabel
    finishBlockWithNewLabel (LJnz lbl' r labelBody labelDone) labelBody
    goS s
    lbl'' <- newLabel
    finishBlockWithNewLabel (LJmp lbl'' labelCheck) labelDone


goE :: Expr -> Ast2LirM Reg
goE = \case
  ELit i -> do
    r <- mkRegV
    lbl <- newLabel
    emit (lAssign lbl r i)
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
    lbl <- newLabel
    emit (LPrim lbl dst (LoArith lop r1 r2))
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
emit ir = mBody %= (++ [ir])

finishBlock :: Lir' 'Exit -> Ast2LirM ()
finishBlock ir = finishBlockWithNewLabel ir =<< newLabel

finishBlockWithNewLabel :: Lir' 'Exit -> Label' 'Region -> Ast2LirM ()
finishBlockWithNewLabel exit label = do
  entry <- use mEntry
  block <- LSeq <$> use mBody <*> pure exit
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
