{-# LANGUAGE TemplateHaskell #-}

module Vn
  ( lvn
  , gvn
  ) where

-- Local/global value numbering.

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
  { _vnGraph        :: LGraph -- As an unique source.
  , _vnBlocks       :: M.Map Label LBlock -- Blocks that being built
  , _vnSealedBlocks :: S.Set Label
  } deriving (Show)

makeLenses ''VnS

emptyVnS :: LGraph -> VnS
emptyVnS g = VnS g M.empty S.empty

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
    vnR = emptyVnR & vnrPreds .~ (foldr buildPreds M.empty . concatMap predPairs) irss
    predPairs (LTraceBlock entry _ exit) = zip (exit ^. branchJumpsTo) (repeat entry)
    buildPreds (k, v) = M.insertWith (++) k [v]
    gvn' = do
      -- Number each block.
      mapM_ lvn' irss
      -- Resolve incomplete blocks
      finishGraph
      -- Return
      use vnGraph

finishGraph :: VnM ()
finishGraph = do
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
  vnSealedBlocks %= S.insert label

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

irUse :: LValue -> VnM LValue
irUse v@(LvLit _) = return v
irUse (LvReg r) = go =<< view vnrLabel
  where
    go :: Label -> VnM LValue
    go label = do
      mbV' <- lookupValue label r
      case mbV' of
        Nothing -> do
          sealed <- uses vnSealedBlocks $ S.member label
          if sealed
            then goR label
            else do
              -- Create phi.
              r' <- freshlyPointed label r
              setPhi label r' []
              return (lValue r')
        Just v' -> return v'

    goR :: Label -> VnM LValue
    goR label = do
      Just ps <- view $ vnrPreds.at label
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
          r' <- freshlyPointed label r
          setPhi label r' []
          -- Find the definition recursively
          ss <- mapM go ps
          -- And fill the phi
          setPhi label r' ss
          return (LvReg r')

    setPhi :: Label -> Reg -> [LValue] -> VnM ()
    setPhi label d ss = putDef label d (LoPhi ss)

irDef :: Reg -> LOperand -> VnM Reg
irDef r lop = do
  label <- view vnrLabel
  r' <- freshlyPointed label r
  putDef label r' lop
  return r'

-- Make and return a fresh value, and point the given value to that fresh value.
freshlyPointed :: Label -> Reg -> VnM Reg
freshlyPointed label r = do
  r' <- (`replaceRegVNumber` r) <$> mkUnique
  putDef label r (lOperand r')
  return r'

putDef :: Label -> Reg -> LOperand -> VnM ()
putDef label r lop = vnBlocks.at label %= fmap (lbDefs %~ M.insert r (simplify lop))
  where
    simplify (LoArith aop (LvLit a) (LvLit b)) = LoAtom (LvLit (denoteOp aop a b))
    simplify x@_ = x

    denoteOp = \case
      LAdd -> (+)
      LLt -> \a b -> if a < b then 1 else 0

mkUnique :: VnM Int
mkUnique = mkUnique' vnGraph

replaceRegVNumber :: Int -> Reg -> Reg
replaceRegVNumber i (RegV _ name) = RegV i name
replaceRegVNumber _ r = error $ "replaceRegVNumber: not a RegV: " ++ show r

lookupValue :: Label -> Reg -> VnM (Maybe LValue)
lookupValue label r = do
  mbB <- use (vnBlocks.at label)
  return $ maybe Nothing (go r . (^. lbDefs)) mbB
  where
    go r0 m = case M.lookup r0 m of
      Nothing -> Nothing
      Just (LoAtom v@(LvReg r')) -> Just (fromMaybe v (go r' m))
      Just (LoAtom v) -> Just v
      Just _ -> Nothing --error $ "lookupValue: not a value: " ++ show lop
