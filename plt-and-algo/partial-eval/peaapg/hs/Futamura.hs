{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- Illustrate the 3 futamura projection with types:
-- + The langauge tycons are concrete
-- + The input/output types are abstract
--
-- Also see http://blog.sigfpe.com/2009/05/three-projections-of-doctor-futamura.html
-- And https://stackoverflow.com/a/45992581

module Futamura where

-- The target language

data Target a

-- A program written in the target langauge can be run directly
run :: Target a -> a
run = undefined

-- Target codegen helpers

-- We can generate code ourselves to patch the return value
instance Functor Target where
  fmap = undefined

-- We can generate code that return just a value
-- We can also generate code that run two programs and combine their results 
instance Applicative Target where
  pure = undefined
  (<*>) = undefined

-- The source language
data S a

-- The source has an abstract semantics
sem :: S a -> a
sem = undefined

-- Assuming that there's an interpreter for S, written in Target
intS :: Target (S a -> a)
intS = undefined

-- Now the different ways to evaluate S

-- Using the semantics directly
withSem :: S (i -> o) -> i -> o
withSem source = sem source

-- Running the interpreter directly
withInt :: S (i -> o) -> i -> o
withInt source = run intS source

-- Assuming that there's a specializer written in Target, from Target to Target
mixS :: Target (Target (i -> o) -> i -> Target o)
mixS = undefined

-- Another form of mixS that takes two inputs. Can be derived from mixS
-- from some preparations (in fact only needs pure)
mixS2 :: forall a b o. Target (Target (a -> b -> o) -> a -> b -> Target o)
mixS2 = pure $ \prog a b ->
  let prog' (a, b) = run prog a b
  in run mixS' (pure prog') (a, b)
 where
  -- mixS in curried form
  mixS' :: Target (Target ((a, b) -> o) -> (a, b) -> Target o)
  mixS' = mixS

-- Specialize the interpreter using mix to generate target program.
-- s is the static input while d is the dynamic input.
-- This is the first futamura projection
firstProj :: forall s d o. S (s -> d -> o) -> s -> Target (d -> o)
firstProj = run mixS2 intS

-- Self-apply mix to generate a compiler
-- (Hmm so the above types are actually correct...)
-- This is the second futamura projection
secondProj :: Target (S o -> Target o)
secondProj = run mixS mixS intS

-- Self-apply mix twice to generate a compiler-generator
-- This is a compiler generator because, say
-- * i is a S o, and Target (i -> o) is just an interpreter
-- * The resulting Target (i -> Target o) is clearly a compiler
-- This is the third futamura projection
thirdProj :: Target (Target (i -> o) -> Target (i -> Target o))
thirdProj = run mixS mixS mixS

-- Now see what we can do to use these proj
compFromCogen :: Target (S o -> Target o)
compFromCogen = run thirdProj intS

targetFromComp :: S o -> Target o
targetFromComp = run secondProj

