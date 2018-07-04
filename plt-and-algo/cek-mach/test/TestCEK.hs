module TestCEK where

import Test.Hspec

import CEK

testCek = describe "CEK" $ do
  it "halts on empty kont" $ do
    let w = VInt 0
    evalSteps (EValue w, emptyEnv, emptyKont) `shouldBe` Just w

  it "captures lambda env" $ do
    let
      lam = Lam "x" (EVar "x")
      clo = VClo lam emptyEnv
    evalSteps (ELam lam, emptyEnv, emptyKont) `shouldBe` Just clo

  it "id x = x" $ do
    let
      lam = Lam "x" (EVar "x")
      w = VInt 0
    evalSteps (EAp (ELam lam) (EValue w), emptyEnv, emptyKont) `shouldBe` Just w

  it "k x y = x" $ do
    let
      lam = Lam "x" (ELam (Lam "y" (EVar "x")))
      w0 = VInt 0
      w1 = VInt 1
    evalSteps (ELam lam `EAp` EValue w0 `EAp` EValue w1, emptyEnv, emptyKont) `shouldBe` Just w0

