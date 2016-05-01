{-# LANGUAGE TemplateHaskell #-}

module Vn
  ( lvn
  , gvn
  ) where

-- Local/global value numbering.

import Control.Lens
import Control.Monad ((<=<), forM_)
import Control.Monad.Trans.RWS
import qualified Data.Map as M

import Lir hiding (mkUnique)

data VnS = VnS
  { _vnGraph :: LGraph -- As an unique source.
  , _vnRegNumbers :: M.Map Label (M.Map Reg Reg)
  , _vnPhis :: M.Map Label (M.Map Reg [Reg])  -- Will be moved back once everything is done
  } deriving (Show)

makeLenses ''VnS

emptyVnS :: LGraph -> VnS
emptyVnS g = VnS g M.empty M.empty

type VnM = RWS Label () VnS

lvn :: Label -> LGraph -> LGraph
lvn label g = fst $ evalRWS (lvn' label *> use vnGraph) undefined (emptyVnS g)

gvn :: LGraph -> LGraph
gvn g = fst $ evalRWS gvn' undefined (emptyVnS g)
  where
    gvn' = do
      -- Number each block
      mapM_ lvn' (M.keys (g ^. lgNodes))
      -- populate phis
      blockPhis <- use vnPhis
      forM_ (M.toList blockPhis) $ \(label, phis) ->
        forM_ (M.toList phis) $ \(d, ss) ->
          vnGraph.lgNodes.at label %= fmap (lbPhis %~ (++ [LPhi d ss]))
      use vnGraph

-- Inplace.
lvn' :: Label -> VnM ()
lvn' label = do
  b <- uses (vnGraph.lgNodes) (M.! label)
  b' <- withLabel label (goB b)
  vnGraph.lgNodes %= M.insert label b'

withLabel :: Label -> VnM a -> VnM a
withLabel label = withRWS (const (label,))

goB :: LBlock -> VnM LBlock
goB (LBlock entry phis body exit) = do
  body' <- mapM goIr body
  exit' <- goIr exit
  return (LBlock entry phis body' exit')

goIr :: Lir -> VnM Lir
goIr ir = do
  let du = ir ^. irDefUse
  uses' <- mapM irUse (du ^. lUse)
  defs' <- mapM irDef (du ^. lDef)
  let
    du' = du & (lUse .~ uses') . (lDef .~ defs')
    ir' = ir & irDefUse .~ du'
  return ir'

irUse :: Reg -> VnM Reg
irUse r = go =<< view id
  where
    go :: Label -> VnM Reg
    go label = do
      r' <- lookupReg label r
      maybe (goR label) return r'

    goR :: Label -> VnM Reg
    goR label = do
      g <- use vnGraph
      let ps = predLabels label g
      case ps of
        [p] ->
          -- Only one predecessor, shouldn't need a phi.
          -- XXX: Am I right?
          go p
        [] ->
          -- Entry reached.
          error $ "Undefined variable: " ++ show r
        _ -> do
          -- Create a phi here.
          r' <- mkRegV label r
          putPhi label r' []
          -- Find the definition recursively
          ss <- mapM go ps
          -- And fill the phi
          putPhi label r' ss
          return r'

    putPhi :: Label -> Reg -> [Reg] -> VnM ()
    putPhi label d ss = vnPhis %= M.insertWith M.union label (M.singleton d ss)

irDef :: Reg -> VnM Reg
irDef = number

number :: Reg -> VnM Reg
number r = do
  label <- view id
  mkRegV label r

mkRegV :: Label -> Reg -> VnM Reg
mkRegV label r = do
  r' <- (`replaceRegVNumber` r) <$> mkUnique
  vnRegNumbers %= M.insertWith M.union label (M.singleton r r')
  return r'

mkUnique :: VnM Int
mkUnique = mkUnique' vnGraph

replaceRegVNumber :: Int -> Reg -> Reg
replaceRegVNumber i (RegV _ name) = RegV i name
replaceRegVNumber _ r = error $ "replaceRegVNumber: not a RegV: " ++ show r

lookupReg :: Label -> Reg -> VnM (Maybe Reg)
lookupReg label r = uses vnRegNumbers (M.lookup r <=< M.lookup label)
