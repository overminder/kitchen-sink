module CpsLint where

import           Cps

import           Control.Arrow (second)
import           Control.Lens
import           Data.List     (mapAccumL, mapAccumR)
import qualified Data.Map      as M
import           Data.Maybe    (catMaybes)
import qualified Data.Set      as S

x86Regs = words "rax rdx rcx rbx rdi rsi";

lsra :: [String] -> CFunction -> CFunction
lsra regNames f = f & cfLabels %~ rewriteFwd go (alloc (f ^. cfArgs) (S.toList regs))
  where
    regs = S.fromList (map RegId regNames)
    go regMap stmt = let stmt' = replaceWithRegs regMap stmt
                         (regMap', _) = contOfStmt allocOut regMap stmt'
                         stmt'' = replaceWithRegs regMap' stmt'
                     in (regMap', stmt'')

    replaceWithRegs regMap = mapStmtId (\ v -> M.findWithDefault v v regMap)

    isReg (RegId _) = True
    isReg _ = False

    notGlobal (GlobalId _) = False
    notGlobal _ = True

    alloc ids regs = M.fromList (ids `zip` regs)

    allocOut regMap k = let uses = S.filter notGlobal (k ^. ccUses)
                            (regUses, nonRegUses) = S.partition (`M.member` regMap) uses
                            regMap' = alloc (S.toList nonRegUses) (S.toList (regs S.\\ regUses))
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


