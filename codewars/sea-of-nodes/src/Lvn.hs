{-# LANGUAGE TemplateHaskell #-}

module Lvn where

-- Local value numbering.

import Control.Lens
import Control.Monad.Trans.State
import qualified Data.Map as M

import Ast
import Lir

data LvnS = LvnS
  { _lvnUniqueGen :: Int
  , _lvnVarMap :: M.Map Var Int
  } deriving (Show)

makeLenses ''LvnS

type LvnM = State LvnS


