module Main where

import Lib

expr = lambda (lambda (add here (before here)))

main :: IO ()
main = print $ eval expr 1 2
