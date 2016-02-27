module CpsLint where

import           Cps

import           Control.Arrow (second)
import           Control.Lens
import qualified Data.List as L
import           Data.List     (mapAccumL, mapAccumR)
import qualified Data.Map      as M
import           Data.Maybe    (catMaybes)
import qualified Data.Set      as S

x86Regs :: [String]
x86Regs = words "rdi rsi rdx rcx r8 r9"

lsra :: [String] -> CFunction -> CFunction
lsra regNames f = f & (cfLabels %~ rewriteFwd go entryRegMap)
                    . (cfArgs .~ map snd allocedArgs)
                    . (cfEntry %~ mapContId (mapId entryRegMap))
  where
    entryRegMap = M.fromList allocedArgs
    regs = map RegId regNames
    allocedArgs = zip (f ^. cfArgs) regs
    go regMap stmt = let (regMap', _) = contOfStmt allocOut regMap stmt
                         stmt' = replaceWithRegs regMap' stmt
                     in (regMap', stmt')

    mapId regMap v = M.findWithDefault v v regMap
    replaceWithRegs = mapStmtId . mapId

    isReg (RegId _) = True
    isReg _ = False

    notGlobal (GlobalId _) = False
    notGlobal _ = True

    alloc ids regs = M.fromList (ids `zip` regs)

    -- Greedily alloc regs for unallocated vregs in the live-out of `k`.
    allocOut regMap k = let uses = S.filter notGlobal (k ^. ccUses)
                            uses' = S.map (\ v -> M.findWithDefault v v regMap) uses
                            (regUses, nonRegUses) = S.partition isReg uses'
                            regMap' = alloc (S.toList nonRegUses) (regs L.\\ S.toList regUses)
                        in (regMap' `M.union` regMap, k)


removeMoves :: CFunction -> CFunction
removeMoves = cfLabels %~ rewriteFwd go M.empty
  where
    go ids stmt = let (ids', stmt') = zapMove ids stmt
                   in (ids', mapStmtId (normalizeUses ids') stmt')

    zapMove ids s = case s of
      CDef u k d -> (addEq u d ids, CNop k)
      _ -> (ids, s)

    addEq u d ids = case M.lookup u ids of
      Nothing -> M.insert d u ids
      Just u' -> addEq d u' ids

    normalizeUses ids' v = M.findWithDefault v v ids'

removeNops :: CFunction -> CFunction
removeNops func = func & cfLabels %~ rewriteMb Bwd go M.empty
  where
    go redirs (lbl, s) = case s of
      CNop k -> (M.insert lbl (k ^. ccLabel) redirs, Nothing)
      _ -> (redirs, Just (lbl, mapStmtCont (derefLabel redirs) s))

    derefLabel redirs = ccLabel %~ deref redirs
    deref redirs lbl = case M.lookup lbl redirs of
      Nothing -> lbl
      Just lbl' -> deref redirs lbl'

type StmtMap = M.Map CLabel CStmt

rewriteFwd :: (a -> CStmt -> (a, CStmt)) -> a -> StmtMap -> StmtMap
rewriteFwd f = rewriteMb Fwd f'
  where
    f' a (l, s) = let (a', s') = f a s
             in (a', Just (l, s'))

data RewriteDir = Bwd | Fwd

-- Since the stmt list is already reversed.
dirToMapper :: RewriteDir -> (a -> b -> (a, c)) -> a -> [b] -> (a, [c])
dirToMapper Bwd = mapAccumL
dirToMapper Fwd = mapAccumR

rewriteMb :: RewriteDir -> (a -> (CLabel, CStmt) -> (a, Maybe (CLabel, CStmt))) -> a -> StmtMap -> StmtMap
rewriteMb dir f a = M.fromList . catMaybes . snd . dirToMapper dir f a . M.toList

values :: ([b] -> [c]) -> [(a, b)] -> [(a, c)]
values f ab = zip as (f bs)
  where
    (as, bs) = unzip ab


