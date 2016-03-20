{-# LANGUAGE OverloadedStrings #-}

module Expr where

import Data.String (IsString(..))

type Name = String

data Expr
  -- | Core forms
  = Lit Int
  | Var Name
  | Lam [Name] Expr
  | LetRec [(Name, Expr)] Expr

  -- | Typed ops
  | IntAdd Expr Expr  -- Unchecked.
  | IntLt Expr Expr  -- Unchecked
  | Ap Expr [Expr]  -- Unchecked
  | If Expr Expr Expr  -- Unchecked

  -- | Guards
  | IsInt Expr
  | IsFn Expr Int

  -- | XXX
  | Abort
  deriving (Show)

instance IsString Expr where fromString = Var

-- A sample Expr.
fiboMain :: Expr
fiboMain = LetRec [("fibo", fibo), ("+", intAdd), ("<", intLt)] main
  where
    fibo = Lam ["n"] $ If (Ap "<" ["n", Lit 2])
      "n"
      (Ap "+"
       [Ap "fibo" [Ap "+" ["n", Lit (-1)]],
        Ap "fibo" [Ap "+" ["n", Lit (-2)]]])
    main = Ap "fibo" [Lit 10]

    mkSafeOp bop = Lam ["x", "y"] $ intsOrFail ["x", "y"] (bop "x" "y")
    intAdd = mkSafeOp IntAdd
    intLt = mkSafeOp IntLt

    intOrFail p b = If (IsInt p) b Abort
    intsOrFail = flip (foldr intOrFail)
