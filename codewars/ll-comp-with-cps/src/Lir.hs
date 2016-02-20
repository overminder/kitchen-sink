{-# LANGUAGE TemplateHaskell #-}

module Lir where

import Control.Lens
import Text.Printf
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

data Lir
  = MovRR LReg LReg
  | MovRI LReg Imm
  | Ret
  | CallR LReg
  | CmpRR LReg LReg
  | Jcc Cond

-- To GNU Syntax.
instance Show Lir where
  show = \case
    MovRR dst src -> showGas "mov" (showGasOp2 dst src)
    Ret -> "ret"
    CallR r -> showGas "call" (show r)
    CmpRR dst src -> showGas "cmp" (showGasOp2 dst src)
    Jcc cond -> "j" ++ show cond

showGas :: String -> String -> String
showGas = printf "%-8s%s"

showGasOp2 :: (Show a, Show b) => a -> b -> String
showGasOp2 dst src = printf "%s, %s" (show src) (show dst)

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
  | ILabel LBlockId

instance Show Imm where
  show = ('$' :) . \case
    I32 i -> show i
    ILabel l -> show l

newtype LBlockId = LBlockId Int
  deriving (Eq, Ord)

instance Show LBlockId where
  show (LBlockId i) = ".LBB" ++ show i

data LBlock = LBlock {
  _bId :: LBlockId,
  _bArgs :: [LReg],
  _bIrs :: [Lir]
} deriving (Show)

data LFunction = LFunction {
  _fBlocks :: M.Map LBlockId LBlock,
  _fEdges :: S.Set (LBlockId, LBlockId),
  _fEntry :: LBlockId
} deriving (Show)

data LFrame = LFrame {
  _frVirtualGen :: Int,
  _frVarMap :: M.Map Name LReg,
  _frBlockIdGen :: Int,

  _frCurrentBlock :: LBlock,
  _frFunction :: LFunction
} deriving (Show)

makeLenses ''LBlock
makeLenses ''LFunction
makeLenses ''LFrame
