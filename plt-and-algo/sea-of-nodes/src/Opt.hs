{-# LANGUAGE TemplateHaskell #-}

module Opt
  ( opt
  , cfold
  ) where

import Debug.Trace
import           Control.Applicative       ((<|>))
import           Control.Lens
import           Control.Monad             (when, forM_)
import qualified Data.List as L
import           Control.Monad.Trans.State
import qualified Data.Map                  as M

import           Lir

data CFoldS = CFoldS
  { _cfGraph :: LGraph
  , _cfChanged :: Bool
  }

makeLenses ''CFoldS

type CFoldM = State CFoldS

opt :: LGraph -> LGraph
opt = (^. cfGraph) . cfold

pattern JustLvLit i = Just (LoAtom (LvLit i))

-- Constant propagation and folding
cfold :: LGraph -> CFoldS
cfold g = execState (go (g ^. lgBlocks.to M.keys)) emptyS
  where
    emptyS = CFoldS g False

    go :: [Label] -> CFoldM ()
    go workList = case workList of
      [] -> return ()
      w:ws -> do
        changes <- goB w
        go (ws ++ changes)

    goB :: Label -> CFoldM [Label]
    goB label = do
      Just b <- use (cfGraph.lgBlocks.at label)
      changed <- foldr (goIr label) (return False) (M.toList (b ^. lbDefs))
      changed' <- goExit label (b ^. lbExit)
      -- Also simplify lbExit?
      if changed || changed'
        then do
          Just b' <- use (cfGraph.lgBlocks.at label)
          return (b' ^. lbExit.branchJumpsTo)
        else return []

    goExit label br = do
      let us = br ^. branchUses
      us' <- mapM simplifyValue us
      let br' = simplifyBranch (br & branchUses .~ us')
      let changed = br /= br'
      when changed $ do
        cfChanged .= True
        cfGraph.lgBlocks.at label %= fmap (lbExit .~ br')
        let killedDests = (br ^. branchJumpsTo) L.\\ (br' ^. branchJumpsTo)
        forM_ killedDests $ \dst -> do
          traceM $ "kill dest: " ++ show dst ++ ", here = " ++ show label
          -- Sync phis in those edges.
          -- XXX: Still needs DCE.
          let removePhi = \case
                LoPhi vls -> LoPhi . filter ((/= label) . snd) $ vls
                x@_ -> x
          cfGraph.lgBlocks.at dst %= fmap (lbDefs %~ M.map removePhi)
      return changed

    -- This could cause control flow changes. Need to sync phis in this case.
    simplifyBranch = \case
      LJnz (LvLit 0) _ f -> LJmp f
      LJnz (LvLit _) t _ -> LJmp t
      br@_ -> br

    goIr :: Label -> (Reg, LOperand) -> CFoldM Bool -> CFoldM Bool
    goIr label (r, lop) m = do
      mbLop' <- simplify lop
      case mbLop' of
        Nothing ->
          -- Cannot simplify further
          m
        Just lop' -> do
          let changed = lop' /= lop
          when changed $ do
            cfChanged .= True
            cfGraph.lgBlocks.at label %= fmap (lbDefs %~ M.insert r lop')
          c0 <- m
          return $ c0 || changed

    lookupValue :: Reg -> CFoldM LValue
    lookupValue r = do
      lop' <- lookupOperand r
      case lop' of
        Just (LoAtom a) -> return a
        _ -> return (lValue r)

    lookupOperand :: Reg -> CFoldM (Maybe LOperand)
    lookupOperand r = do
      Just label <- use $ cfGraph.lgDefs.at r
      Just b <- use $ cfGraph.lgBlocks.at label
      let Just lop = b ^. lbDefs.at r
      simplify lop

    simplifyValue v = case v of
      LvReg r -> lookupValue r
      LvLit _ -> pure v

    simplify :: LOperand -> CFoldM (Maybe LOperand)
    simplify o = case o of
      LoAtom (LvReg r) -> do
        mbOp <- lookupOperand r
        return (mbOp <|> Just (lOperand r))
      LoAtom (LvLit _) -> pure (Just o)
      LoPhi [(v, label)] -> Just . LoPhi . (\v' -> [(v', label)]) <$> simplifyValue v
      LoPhi _ -> pure Nothing  -- Could also simplify but need to take care of loops.
      LoArith aop a b -> do
        a' <- simplify (lOperand a)
        b' <- simplify (lOperand b)
        case (aop, a', b') of
          (LAdd, JustLvLit 0, _) -> pure (b' <|> Just (lOperand b))
          (LAdd, _, JustLvLit 0) -> pure (a' <|> Just (lOperand a))
          (_, JustLvLit alit, JustLvLit blit) ->
            pure . Just . lOperand $ denoteOp aop alit blit
          _ -> do
            av' <- simplifyValue a
            bv' <- simplifyValue b
            pure . Just $ LoArith aop av' bv'

    denoteOp = \case
      LAdd -> (+)
      LLt -> \a b -> if a < b then 1 else 0

data DceS = DceS
  { _dceGraph :: LGraph
  , _dceChanged :: Bool
  }

-- This should traditionally be a backward analysis.
dce :: LGraph -> DceS
dce g = undefined
