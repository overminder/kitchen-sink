module Lib
    ( someFunc
    ) where

import Ast
import Ast2Lir
import Lir
-- import Vn

someFunc :: IO ()
someFunc = putStrLn "someFunc"
