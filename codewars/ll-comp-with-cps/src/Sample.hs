{-# LANGUAGE OverloadedStrings #-}

module Sample where

import           Lang

idFunc :: Function
idFunc = Function "id" ["x"] (SRet "x")

sFunc :: Function
sFunc = Function "s" ["f", "g", "x"]
  (SRet (ECall "f" ["x", ECall "g" ["x"]]))

loopSum :: Function
loopSum = Function "loopSum" ["N"]
  (SBlock [ SDef "i" (ELit 0)
          , SDef "s" (ELit 0)
          , SWhile (EPrimLt "i" "N")
            (SBlock [ SDef "s" (EPrimAdd "s" "i")
                    , SDef "i" (EPrimAdd "i" (ELit 1))
                    ])
          , SRet "s"
          ])

recLoopSum :: Function
recLoopSum = Function "loopSum" ["N", "i", "s"]
  (SIf (EPrimLt "i" "N")
       (SRet (ECall "loopSum" ["N", EPrimAdd "i" (ELit 1), EPrimAdd "s" "i"]))
       (SRet "s"))
