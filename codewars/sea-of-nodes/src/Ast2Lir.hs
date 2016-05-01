{-# LANGUAGE TemplateHaskell #-}

module Ast2Lir
  ( ast2Lir
  ) where

import Control.Lens
import Control.Monad.Trans.State
import qualified Data.Map as M
import qualified Data.Text as T
import Data.Maybe (fromMaybe)

import Ast
import Lir hiding (mkUnique)
import qualified Lir

type Env = M.Map Var Reg

data Ast2LirS = Ast2LirS
  { _mGraph :: LGraph
  , _mEntry :: Label
  , _mBody :: [Lir]
  , _mEnv :: Env
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
    r <- goE e
    finishBlock (LRet r)

  SAssign v e -> do
    src <- goE e
    dst <- lookupEnvOrDefine v
    emit (LMovR dst src)

  SSeq ss -> mapM_ goS ss

  SIf e t f -> do
    r <- goE e
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
    r <- goE e
    finishBlockWithNewLabel (LJnz r labelBody labelDone) labelBody
    goS s
    finishBlockWithNewLabel (LJmp labelCheck) labelDone


goE :: Expr -> Ast2LirM Reg
goE = \case
  ELit i -> do
    r <- mkRegV
    emit (LMovI r i)
    return r
  EVar v -> lookupEnvOrFail v
  EArith aop e1 e2 -> do
    r1 <- goE e1
    r2 <- goE e2
    dst <- mkRegV
    let mkIr = case aop of
                 AAdd -> LAdd
                 ALt -> LLt
    emit (mkIr dst r1 r2)
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

emit :: Lir -> Ast2LirM ()
emit ir | isExit ir = error $ "emit: " ++ show ir ++ " is an exit instruction."
        | otherwise = mBody %= (++ [ir])

finishBlock :: Lir -> Ast2LirM ()
finishBlock ir = finishBlockWithNewLabel ir =<< newLabel

finishBlockWithNewLabel :: Lir -> Label -> Ast2LirM ()
finishBlockWithNewLabel ir label = do
  block <- LBlock <$> use mEntry <*> pure [] <*> use mBody <*> pure ir
  mGraph %= insertBlock block
  prepareNewBlockOf label

newLabel :: Ast2LirM Label
newLabel = LAnonymous <$> mkUnique

prepareNewBlockOf :: Label -> Ast2LirM ()
prepareNewBlockOf lbl = do
  mEntry .= lbl
  mBody .= []
