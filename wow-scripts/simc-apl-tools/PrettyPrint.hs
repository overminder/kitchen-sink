#!/usr/bin/env stack runghc --package pretty-simple

{- SimC APL contains too many long one-liner expressions.
   This tool aims to pretty print them.
 -}

module Main where

import Text.Pretty.Simple (pPrint)
import AplParse

main = do
  src <- getContents
  pPrint (pApl src)

