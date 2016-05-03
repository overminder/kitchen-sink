module Lib
  ( ast2Lvn
  , ast2Gvn
  , pretty
  , parseAst
  ) where

import           Ast
import           Ast2Lir
import           Lir
import           Parser
import           Text.PrettyPrint.ANSI.Leijen (pretty)
import           Vn

ast2Lvn :: Stmt -> LGraph
ast2Lvn s = g'
  where
    (g, irs) = ast2Lir s
    g' = lvn irs g

ast2Gvn :: Stmt -> LGraph
ast2Gvn s = g'
  where
    (g, irs) = ast2Lir s
    g' = gvn irs g
