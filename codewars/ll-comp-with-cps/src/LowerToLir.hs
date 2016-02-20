module LowerToLir where

import Control.Monad.State
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Lens
import Lang
import Lir

type LowerM = State LFrame

lowerToLir :: Function -> LowerM LFunction
lowerToLir (Function _name _args _body) = return undefined

regForName :: Name -> LowerM LReg
regForName name = do
  mbR <- uses frVarMap $ M.lookup name
  case mbR of
    Just r -> return r
    Nothing -> do
      r <- freshReg
      frVarMap %= M.insert name r
      return r

freshReg :: LowerM LReg
freshReg = do
  g <- use frVirtualGen
  frVirtualGen .= g + 1
  return $ VirtualReg g

lowerExpr :: Expr -> LowerM LReg
lowerExpr = \case
  EVar v -> regForName v
  ELit i -> do
    r <- freshReg
    emit (MovRI r (I32 i))
    return r
  ECall f args -> do
    fr <- lowerExpr f
    rs <- mapM lowerExpr args
    forM_ (zip kArgRegs rs) $ \ (pr, vr) ->
      emit (MovRR (PhysicalReg pr) vr)
    emit (CallR fr)
    finishBlock
    return (PhysicalReg rax)
  EPrimOp pop args -> case pop of
    PrimPrint

emit :: Lir -> LowerM ()
emit ir = frCurrentBlock.bIrs %= (++ [ir])

finishBlock :: LowerM ()
finishBlock = do
  b <- use frCurrentBlock
  newB <- newBlock
  frFunction.fBlocks %= M.insert (b ^. bId) b
  frFunction.fEdges %= S.insert (b ^. bId, newB ^. bId)

newBlock :: LowerM LBlock
newBlock = do
  bid <- uses frBlockIdGen LBlockId
  frBlockIdGen += 1
  return $ LBlock bid [] []
