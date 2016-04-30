module Lib
    ( someFunc
    ) where

import Ast
import Ast2Lir
import Lir

someFunc :: IO ()
someFunc = putStrLn "someFunc"
