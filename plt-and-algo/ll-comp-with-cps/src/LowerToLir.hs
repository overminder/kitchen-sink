module LowerToLir where

import Control.Monad.State
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe (fromJust, isNothing)
import Control.Lens
import Lang
import Lir

type LowerM = State LBlockBuilderState

lowerToLir :: Function -> LowerM LFunction
lowerToLir (Function _name args body) = do
  moveFromArgRegs =<< mapM regForName args
  lowerStmt body
  use bsFunction

lowerStmt :: Stmt -> LowerM ()
lowerStmt = \case
  SBlock ss -> mapM_ lowerStmt ss
  SExpr e -> void $ lowerExpr e
  SDef v e -> do
    re <- lowerExpr e
    dst <- regForName v
    emits [MovRR dst re]
  SRet e -> do
    re <- lowerExpr e
    emits [MovRR (PhysicalReg rax) re]
  SIf (EPrimLt a b) t f -> do
    ra <- lowerExpr a
    rb <- lowerExpr b
    lblT <- newLabel
    lblF <- newLabel
    lblOk <- newLabel
    emits [CmpRR ra rb]
    emits [Jcc GE lblT lblF]
    emits [Label lblT]
    lowerStmt t
    emits [J lblOk] >> emits [Label lblF]
    lowerStmt f
    emits [J lblOk] >> emits [Label lblOk]
  SPrimPrint e -> do
    r <- lowerExpr e
    lblOk <- newLabel
    emits (moveToArgRegs [r])
    emits [CallL (LNamed "primPrintInt") lblOk]
    emits [Label lblOk]

regForName :: Name -> LowerM LReg
regForName name = do
  mbR <- uses bsVarMap $ M.lookup name
  case mbR of
    Just r -> return r
    Nothing -> do
      r <- freshReg
      bsVarMap %= M.insert name r
      return r

freshReg :: LowerM LReg
freshReg = do
  g <- use bsVirtualGen
  bsVirtualGen .= g + 1
  return $ VirtualReg g

lowerExpr :: Expr -> LowerM LReg
lowerExpr = \case
  EVar v -> regForName v
  ELit i -> do
    r <- freshReg
    emits [MovRI r (I32 i)]
    return r
  ECall f args -> do
    rf <- lowerExpr f
    r <- freshReg
    lblOk <- newLabel
    emits =<< moveToArgRegs =<< mapM lowerExpr args
    emits [CallR rf lblOk
           Label lblOk,
           MovRR r (PhysicalReg rax)]
    return r
  EPrimAdd a b -> do
    ra <- lowerExpr a
    rb <- lowerExpr b
    r <- freshReg
    emits [MovRR r ra, AddRR r rb]
    return r

emits :: [Lir a] -> LowerM ()
emits irs = bsIrTrace %= (++ (map UntypedLir irs))

moveToArgRegs :: [LReg] -> [Lir 'Mid]
moveToArgRegs = zipWith (MovRR . PhysicalReg) kArgRegs

moveFromArgRegs :: [LReg] -> [Lir 'Mid]
moveFromArgRegs rs = zipWith (MovRR . PhysicalReg) rs kArgRegs

newLabel :: LowerM LBlockId
newLabel = do
  bid <- uses bsBlockIdGen LBlockId
  bsBlockIdGen += 1
  return bid

finishBlock :: LowerM LBlockId
finishBlock = do
  b <- uses bsCurrent (buildBlock . fromJust)
  newB <- newBlock
  bsFunction.fBlocks %= M.insert (b ^. bId) b
  bsFunction.fEdges %= S.insert (b ^. bId, newB ^. bbId)
  return (b ^. bId)

buildBlock :: LBlockBuilder -> LBlock
buildBlock bb = LBlock
  { _bArgs = []
  , _bId = bb ^. bbId
  , _bLastIr = fromJust (bb ^. bbLastIr)
  , _bIrs = bb ^. bbIrs
  }

ensureBlock :: LowerM ()
ensureBlock = do
  absent <- uses bsCurrent isNothing
  when absent $ do
    b <- newBlock
    bsCurrent .= Just b

newBlock :: LowerM LBlockBuilder
newBlock = emptyBuilder <$> newLabel

-- XXX: Hard-coded IDs.

firstBlockId :: LBlockId
firstBlockId = LBlockId 0

emptyBuilderState :: LBlockBuilderState
emptyBuilderState = LBlockBuilderState 0 M.empty 1 Nothing emptyLFunction

emptyBuilder :: LBlockId -> LBlockBuilder
emptyBuilder bid = LBlockBuilder bid [] Nothing

emptyLFunction :: LFunction
emptyLFunction = LFunction M.empty S.empty firstBlockId

unsafeFromJust :: Lens' (Maybe a) a
unsafeFromJust = anon (error "unsafeFromJust: Nothing") (\_ -> False)
