module TestCEK where

import Test.Hspec

import CEK

testCek = describe "CEK" $ do
  it "halts on empty kont" $ do
    let w = VInt 0
    evalSteps (EValue w, emptyEnv, emptyKont) `shouldBe` Just w
