{-# LANGUAGE RecursiveDo     #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections   #-}

module Cps where

import           Lang

import           Control.Lens
import           Control.Monad.State
import           Data.Foldable       (foldrM)
import qualified Data.Map            as M
import           Data.Maybe          (fromMaybe)
import qualified Data.Set            as S

data Id
  = Id Int
  | GlobalId Name
  | RegId String
  deriving (Show, Eq, Ord)

 -- CPS
newtype CLabel = CLabel Int
  deriving (Show, Eq, Ord)

data CFunction = CFunction {
  _cfName   :: Name,
  _cfArgs   :: [Id],
  _cfEntry  :: CCont,
  _cfLabels :: M.Map CLabel CStmt
} deriving (Show)


data CStmt
  = CRet Id
  | CPrimLt Id Id CCont CCont
  | CDef Id CCont Id
  | CPrimPrint Id CCont
  | CCall Id [Id] CCont Id
  | CPrimAdd Id Id CCont Id
  | CLit Int CCont Id
  | CNop CCont
    -- Assumes we always restore the same id to the same slot.
  | CSpill Id CCont
  | CRestore Id CCont
  deriving (Show)

type VarMap = M.Map Name Id

type CpsM = State CpsState

data CCont = CCont {
  _ccLabel :: CLabel,
  _ccUses  :: S.Set Id
} deriving (Show)

data CpsState = CpsState {
  _csVarMap    :: VarMap,
  _csNextId    :: Int,
  _csNextLabel :: Int,
  _csLabels    :: M.Map CLabel CStmt
} deriving (Show)

makeLenses ''CpsState
makeLenses ''CFunction
makeLenses ''CCont

runCps :: Function -> CFunction
runCps f = evalState (cpsFunction f) emptyCpsState

cpsFunction :: Function -> CpsM CFunction
cpsFunction (Function name args body) = do
  argIds <- mapM (idForName Use . LocalName) args
  k <- cpsStmt body (error "cpsFunction: no return")
  lbls <- use csLabels
  return (CFunction name argIds k lbls)

cpsStmt :: Stmt -> CCont -> CpsM CCont
cpsStmt s k = case s of
  SRet e -> do
    v <- newId
    k' <- addCStmt (CRet v)
    cpsExpr e v k'
  SBlock ss -> foldrM cpsStmt k ss
  SDef n e -> do
    r <- idForName Def (LocalName n)
    cpsExpr e r k
  SWhile (EPrimLt lhs rhs) b -> do
    lhsId <- newId
    rhsId <- newId
    -- Can we compile it without recursive do?
    rec kBody <- cpsStmt b kLhs
        kLt <- addCStmt (CPrimLt lhsId rhsId kBody k)
        kRhs <- cpsExpr rhs rhsId kLt
        kLhs <- cpsExpr lhs lhsId kRhs
    return kLhs
  SIf (EPrimLt lhs rhs) t f -> do
    lhsId <- newId
    rhsId <- newId
    kT <- cpsStmt t k
    kF <- cpsStmt f k
    kLt <- addCStmt (CPrimLt lhsId rhsId kT kF)
    kRhs <- cpsExpr rhs rhsId kLt
    cpsExpr lhs lhsId kRhs
  _ -> error $ "cpsStmt: " ++ show s

cpsExpr :: Expr -> Id -> CCont -> CpsM CCont
cpsExpr e r k = case e of
  EVar n -> do
    id <- idForName Use n
    addCStmt (CDef id k r)
  ECall f as -> do
    fr <- newId
    ars <- mapM (const newId) as
    kCall <- addCStmt (CCall fr ars k r)
    kArgs <- foldrM (uncurry cpsExpr) kCall (zip as ars)
    cpsExpr f fr kArgs
  ELit i -> addCStmt (CLit i k r)
  EPrimAdd e1 e2 -> do
    r1 <- newId
    r2 <- newId
    k' <- addCStmt (CPrimAdd r1 r2 k r)
    k2 <- cpsExpr e2 r2 k'
    cpsExpr e1 r1 k2
  _ -> error $ "cpsExpr: " ++ show e

addCStmt :: CStmt -> CpsM CCont
addCStmt s = do
  lbl <- newCLabel
  let k = CCont lbl (usesOfStmt s)
  csLabels %= M.insert lbl s
  return $ syncUses s k

usesOfStmt :: CStmt -> S.Set Id
usesOfStmt s = case s of
  CRet _ -> S.empty
  CDef id k r -> k ^. ccUses
  CCall _ _ k _ -> k ^. ccUses
  CLit _ k _ -> k ^. ccUses
  CPrimLt _ _ t f -> S.union (t ^. ccUses) (f ^. ccUses)
  CPrimAdd _ _ k _ -> k ^. ccUses

mapStmtId :: (Id -> Id) -> CStmt -> CStmt
mapStmtId f s = mapK $ case s of
  CRet r -> CRet (f r)
  CDef id k r -> CDef (f id) k (f r)
  CCall f' as k r -> CCall (f f') (map f as) k (f r)
  CLit i k r -> CLit i k (f r)
  CPrimLt a b t f' -> CPrimLt (f a) (f b) t f'
  CPrimAdd a b k r -> CPrimAdd (f a) (f b) k (f r)
  CNop k -> CNop k
  where
    mapK = mapStmtCont (mapContId f)

mapContId :: (Id -> Id) -> CCont -> CCont
mapContId f = ccUses %~ S.map f

-- XXX: Use lens?
mapStmtCont :: (CCont -> CCont) -> CStmt -> CStmt
mapStmtCont f = snd . contOfStmt (\() -> ((),) . f) ()

-- This is basically lens...
contOfStmt :: (a -> CCont -> (a, CCont)) -> a -> CStmt -> (a, CStmt)
contOfStmt f a s = case s of
  CRet _ -> (a, s)
  CDef u k d -> let (a', k') = f a k in (a', CDef u k' d)
  CCall f' as k r -> let (a', k'') = f a k in (a', CCall f' as k'' r)
  CLit i k r -> let (a', k') = f a k in (a', CLit i k' r)
  CPrimLt a' b t f' -> let (a'', t') = f a t
                           (a''', f'') = f a'' f'
                       in (a''', CPrimLt a' b t' f'')
  CPrimAdd a' b k r -> let (a'', k') = f a k in (a'', CPrimAdd a' b k' r)
  CNop k -> let (a', k') = f a k in (a', CNop k')

newCLabel :: CpsM CLabel
newCLabel = uses csNextLabel CLabel <* (csNextLabel += 1)

data UseOrDef = Use | Def

idForName :: UseOrDef -> ScopedName -> CpsM Id
idForName _ (GlobalName n) = return $ GlobalId n
idForName uod (LocalName n) = case uod of
  Use -> do
    mbId <- uses csVarMap $ M.lookup n
    case mbId of
      Nothing -> newIdForName n
      Just id -> return id
  Def -> newIdForName n
  where
    newIdForName n = do
      id <- newId
      csVarMap %= M.insert n id
      return id

newId :: CpsM Id
newId = uses csNextId Id <* (csNextId += 1)

syncUses :: CStmt -> CCont -> CCont
syncUses s = case s of
  CDef u _ d -> removeUse d . addUse u
  CRet v -> addUse v
  CCall f as _ r -> removeUse r . addUses (f:as)
  CLit _ _ r -> removeUse r
  CPrimLt lhs rhs _ _ -> addUses [lhs, rhs]
  CPrimAdd a b _ r -> removeUse r . addUses [a, b]
  _ -> error $ "syncUses: " ++ show s

removeUse :: Id -> CCont -> CCont
removeUse id = ccUses %~ S.delete id

addUse :: Id -> CCont -> CCont
addUse id = ccUses %~ S.insert id

addUses :: [Id] -> CCont -> CCont
addUses = foldr ((.) . addUse) id

emptyCpsState :: CpsState
emptyCpsState = CpsState {
  _csVarMap = M.empty,
  _csNextId = 0,
  _csNextLabel = 0,
  _csLabels = M.empty
}
