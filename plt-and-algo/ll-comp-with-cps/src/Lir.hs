{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}

module Lir where

import Control.Lens
import Text.Printf
import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Map as M

import Lang (Name)

-- A 64-bit x86_64 GP register.
newtype R64 = R64 String

instance Show R64 where
  show (R64 r) = '%' : r

data LReg
  = PhysicalReg R64
  | VirtualReg Int

instance Show LReg where
  show = \case
    PhysicalReg r -> show r
    VirtualReg v -> "%v" ++ show v

rax, rdx, rbx, rcx, rdi, rsi, r8, r9 :: R64
[rax, rdx, rbx, rcx, rdi, rsi, r8, r9] =
  map (R64 . ('r' :)) . words $ "ax dx bx cx di si 8 9"

kArgRegs :: [R64]
kArgRegs = [rdi, rsi, rdx, rcx, r8, r9]

data Pos = First | Mid | Last

data Lir (a :: Pos) where
  Label :: LBlockId -> Lir 'First
  MovRR :: LReg -> LReg -> Lir 'Mid
  MovRI :: LReg -> Imm -> Lir 'Mid
  AddRR :: LReg -> LReg -> Lir 'Mid
  CmpRR :: LReg -> LReg -> Lir 'Mid
  J :: LBlockId -> Lir 'Last
  Jcc :: Cond -> LBlockId -> LBlockId -> Lir 'Last
  CallR :: LReg -> LBlockId -> Lir 'Last
  CallL :: Label -> LBlockId -> Lir 'Last
  Ret :: Lir 'Last

data UntypedLir = UntypedLir (forall a. Lir a)

deriving instance Show UntypedLir

-- To GNU Syntax.
instance Show (Lir a) where
  show = \case
    Label bid -> show bid ++ ":"
    MovRR dst src -> showGas "mov" (showGasOp2 dst src)
    MovRI dst src -> showGas "mov" (showGasOp2 dst src)
    AddRR dst src -> showGas "add" (showGasOp2 dst src)
    Ret -> "ret"
    CallR r exit -> showGas "call" (show r) ++ exitComment [("exit", exit)]
    CallL lbl exit -> showGas "call" (show lbl) ++ exitComment [("exit", exit)]
    CmpRR dst src -> showGas "cmp" (showGasOp2 dst src)
    J lbl -> showGas "jmp" (show lbl)
    Jcc cond t f -> "j" ++ show cond ++ exitComment [("t", t), ("f", f)]

showGas :: String -> String -> String
showGas = printf "%-8s%s"

showGasOp2 :: (Show a, Show b) => a -> b -> String
showGasOp2 dst src = printf "%s, %s" (show src) (show dst)

exitComment :: [(String, LBlockId)] -> String
exitComment = (" ;; " ++) . L.intercalate ", " . map showComment
  where
    showComment (tag, lbl) = tag ++ " -> " ++ show lbl

data Cond = E | NE | L | LE | G | GE

instance Show Cond where
  show = \case
    E -> "e"
    NE -> "ne"
    L -> "l"
    LE -> "le"
    G -> "g"
    GE -> "ge"

data Imm
  = I32 Int
  | ILabel Label

instance Show Imm where
  show = ('$' :) . \case
    I32 i -> show i
    ILabel l -> show l

data Label
  = LNamed String
  | LInternal LBlockId

instance Show Label where
  show = \case
    LNamed s -> s
    LInternal bid -> show bid

newtype LBlockId = LBlockId Int
  deriving (Eq, Ord)

instance Show LBlockId where
  show (LBlockId i) = ".LBB" ++ show i

data LBlock = LBlock {
  _bId :: LBlockId,
  _bArgs :: [LReg],
  _bIrs :: [Lir 'Mid],
  _bLastIr :: Lir 'Last
} deriving (Show)

data LFunction = LFunction {
  _fBlocks :: M.Map LBlockId LBlock,
  _fEdges :: S.Set (LBlockId, LBlockId),
  _fEntry :: LBlockId
} deriving (Show)

data LBlockBuilderState = LBlockBuilderState {
  _bsVirtualGen :: Int,
  _bsVarMap :: M.Map Name LReg,
  _bsBlockIdGen :: Int,

  _bsIrTrace :: [UntypedLir],
  _bsCurrent :: Maybe LBlockBuilder,
  _bsFunction :: LFunction
} deriving (Show)

data LBlockBuilder = LBlockBuilder {
   _bbId :: LBlockId,
   _bbIrs :: [Lir 'Mid],
   _bbLastIr :: Maybe (Lir 'Last)
} deriving (Show)

makeLenses ''LBlock
makeLenses ''LFunction
makeLenses ''LBlockBuilderState
makeLenses ''LBlockBuilder
