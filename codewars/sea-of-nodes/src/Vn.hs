{-# LANGUAGE TemplateHaskell #-}

module Vn
  ( lvn
  , gvn
  ) where

-- Local/global value numbering.

-- import Debug.Trace
import           Control.Applicative     ((<|>))
import           Control.Arrow           (first)
import           Control.Lens
import           Control.Monad           (forM_, void)
import           Control.Monad.Trans.RWS
import qualified Data.Map                as M
import           Data.Maybe              (fromMaybe)
import qualified Data.Set                as S

import           Lir                     hiding (mkUnique)

data VnS = VnS
  { _vnGraph          :: LGraph -- As an unique source.
  , _vnBlocks         :: M.Map Label LBlock -- Blocks that are being built
  , _vnCurrentDefs    :: M.Map Reg (M.Map Label LValue)
    -- ^ Non-SSA def tracker. XXX: We should also include this in the graph repr.
  , _vnIncompletePhis :: [(Reg, Label, Reg, Label)]  -- (phi def & label, use & label)
  } deriving (Show)

makeLenses ''VnS

emptyVnS :: LGraph -> VnS
emptyVnS g = VnS g M.empty M.empty []

data VnR = VnR
  { _vnrLabel :: Label
    -- ^ Which block are we currently in
  , _vnrPreds :: M.Map Label [Label]
    -- ^ Cached predecessors
  }

makeLenses ''VnR

type VnM = RWS VnR () VnS

emptyVnR :: VnR
emptyVnR = VnR (error "VnR.label") (error "VnR.preds")

lvn :: [LTraceBlock] -> LGraph -> LGraph
lvn [b] g = fst $ evalRWS (lvn' b *> finishGraph *> use vnGraph) emptyVnR (emptyVnS g)
lvn _ _ = error "lvn: more than 1 block"

gvn :: [LTraceBlock] -> LGraph -> LGraph
gvn irss g = fst $ evalRWS gvn' vnR (emptyVnS g)
  where
    -- Implicitly assumes the first block to be the graph entry.
    start:_ = irss
    blockMap = M.fromList (map (\b -> (b ^. ltbFirst, b)) irss)
    reachableLabels = dfsTB [start ^. ltbFirst] S.empty
    reachableBlocks = map (blockMap M.!) reachableLabels
    dfsTB workList visited = case workList of
      [] -> []
      w:ws | S.member w visited -> dfsTB ws visited
           | otherwise -> w : dfsTB (succs w ++ ws) (S.insert w visited)
    succs label = blockMap ^. at label.lensJust.ltbLast.branchJumpsTo
    preds = foldr buildPreds M.empty . concatMap predPairs $ reachableBlocks
    predPairs (LTraceBlock entry _ exit) = zip (exit ^. branchJumpsTo) (repeat entry)
    buildPreds (k, v) = M.insertWith (++) k [v]

    vnR = emptyVnR & vnrPreds .~ preds

    lensJust :: Lens' (Maybe a) a
    lensJust f = fmap Just . f . fromMaybe (error "lensJust: Nothing")

    gvn' = do
      -- Number each block.
      mapM_ lvn' reachableBlocks
      -- Resolve incomplete blocks
      finishGraph
      -- Return
      use vnGraph

finishGraph :: VnM ()
finishGraph = do
  -- Resolve incomplete phis
  iphis <- use vnIncompletePhis
  forM_ iphis $ \(d, dl, u, ul) -> do
    -- Must have a def here.
    vl <- findCompletedDef u ul
    patchPhi dl d vl
  -- And fill the blocks.
  bs <- use vnBlocks
  forM_ (M.elems bs) $ \b -> vnGraph %= putBlock b

ensureBlock :: Label -> VnM ()
ensureBlock label =
  vnBlocks.at label %= (<|> Just (LBlock label M.empty undefined))

lvn' :: LTraceBlock -> VnM ()
lvn' (LTraceBlock label body exit) = do
  ensureBlock label
  -- Partial.
  withLabel label $ do
    mapM_ goMid body
    goExit exit

withLabel :: Label -> VnM a -> VnM a
withLabel label = withRWS . curry . first $ vnrLabel .~ label

goMid :: (Reg, LOperand) -> VnM ()
goMid (d, lop) = do
  uses' <- mapM irUse (lop ^. opUses)
  let lop' = lop & opUses .~ uses'
  void $ irDef d lop'

goExit :: LBranch -> VnM ()
goExit br = do
  uses' <- mapM irUse (br ^. branchUses)
  let br' = br & branchUses .~ uses'
  label <- view vnrLabel
  vnBlocks.at label %= fmap (lbExit .~ br')

-- Callable after all the blocks are filled.
findCompletedDef :: Reg -> Label -> VnM (LValue, Label)
findCompletedDef r = go
  where
    go :: Label -> VnM (LValue, Label)
    go label = do
      mbV <- lookupCurrentDef label r
      maybe (goR label) return ((,label) <$> mbV)

    goR :: Label -> VnM (LValue, Label)
    goR label = do
      Just [p] <- view $ vnrPreds.at label
      (v, _) <- go p
      -- Return the immediate predecessor that the phi value comes from.
      return (v, label)

irUse :: LValue -> VnM LValue
irUse v@(LvLit _) = return v
irUse (LvReg r) = go =<< view vnrLabel
  where
    go :: Label -> VnM LValue
    go label = maybe (goR label) return =<< lookupCurrentDef label r

    goR :: Label -> VnM LValue
    goR label = do
      mbPs <- view $ vnrPreds.at label
      case mbPs of
        Nothing ->
          -- This label is unreachable.
          error $ "irUse.goR: no preds: " ++ show label
        Just [p] ->
          -- Only one predecessor, shouldn't need a phi.
          go p
        Just [] ->
          -- Entry reached.
          error $ "Undefined variable: " ++ show r
        Just ps -> do
          -- Create a phi here.
          r' <- freshlyPointed label r
          setPhi label r' []
          -- This would create excessive phis. Clean them up in the finish-phi phase.
          forM_ ps $ \p -> vnIncompletePhis %= ((r', label, r, p):)
          -- And don't forget to ask the predecessors to prepare their definition as well.
          mapM_ go ps
          return (LvReg r')

    setPhi :: Label -> Reg -> [(LValue, Label)] -> VnM ()
    setPhi label d vls = putSSADef label d (LoPhi vls)

irDef :: Reg -> LOperand -> VnM Reg
irDef r lop = do
  label <- view vnrLabel
  r' <- freshlyPointed label r
  putSSADef label r' lop
  return r'

-- Make and return a fresh value, and point the given value to that fresh value
-- in the currentDef.
freshlyPointed :: Label -> Reg -> VnM Reg
freshlyPointed label r = do
  r' <- (`replaceRegVNumber` r) <$> mkUnique
  let v = lValue r'
  vnCurrentDefs.at r %= Just . maybe (M.singleton label v) (M.insert label v)
  -- putSSADef label r (lOperand r')
  return r'

putSSADef :: Label -> Reg -> LOperand -> VnM ()
putSSADef label r lop =
  vnBlocks.at label %= fmap (lbDefs %~ M.insert r lop)

patchPhi :: Label -> Reg -> (LValue, Label) -> VnM ()
patchPhi label r vl =
  vnBlocks.at label %= fmap (lbDefs %~ M.insertWith patch r (LoPhi [vl]))
  where
    patch (LoPhi vs) (LoPhi vs') = LoPhi (vs ++ vs')
    patch _ old = error $ "patchPhi: not a phi: " ++ show old

mkUnique :: VnM Int
mkUnique = mkUnique' vnGraph

replaceRegVNumber :: Int -> Reg -> Reg
replaceRegVNumber i (RegV _ name) = RegV i name
replaceRegVNumber _ r = error $ "replaceRegVNumber: not a RegV: " ++ show r

lookupCurrentDef :: Label -> Reg -> VnM (Maybe LValue)
lookupCurrentDef label r = uses vnCurrentDefs (go r)
  where
    go r0 m = M.lookup label =<< M.lookup r0 m
