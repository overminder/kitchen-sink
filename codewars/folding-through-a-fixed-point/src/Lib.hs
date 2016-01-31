{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes, ExistentialQuantification #-}

module Lib where

import Control.Applicative

-- Consider the two following types
newtype Least f 
  = Least (forall r . (f r -> r) -> r)
    
data Greatest f 
  = forall s . Greatest (s -> f s) s

-- They each have a special non-recursive relationship with 'f' when
-- it is a 'Functor'
unwrap :: Functor f => Greatest f -> f (Greatest f)
unwrap (Greatest u s) = Greatest u <$> u s

wrap :: Functor f => f (Least f) -> Least f
wrap f = Least (\k -> k (fold k <$> f))

-- They each are closely tied to the notions of folding and unfolding
-- as well
fold :: (f r -> r) -> (Least f -> r)
fold k (Least g) = g k

unfold :: (s -> f s) -> (s -> Greatest f)
unfold = Greatest

-- It is the case that any "strictly positive" 
-- type in Haskell is representable using Least.

-- We first need the data type's "signature functor".
-- For instance, here is one for []
data ListF a x = Nil | Cons a x deriving Functor

-- Then we can map into and out of lists
listLeast :: [a] -> Least (ListF a)
listLeast l = Least $ \k -> k $ case l of
  []     -> Nil
  a : as -> Cons a (fold k (listLeast as))

leastList :: Least (ListF a) -> [a]
leastList = fold $ \case
  Nil       -> []
  Cons a as -> a : as

-- It is also the case that these types are representable using
-- Greatest.
listGreatest :: [a] -> Greatest (ListF a)
listGreatest = unfold $ \case
  []   -> Nil
  a:as -> Cons a as

greatestList :: Greatest (ListF a) -> [a]
greatestList (Greatest u s) = case u s of
  Nil       -> []
  Cons a s' -> a : greatestList (unfold u s')

-- Given all of these types are isomorphic, we ought to be able to go
-- directly from least to greatest fixed points and visa versa. Can
-- you write the functions which witness this last isomorphism
-- generally for any functor?
greatestLeast :: Functor f => Greatest f -> Least f
greatestLeast = fix2L . g2Fix 

leastGreatest :: Functor f => Least f -> Greatest f
leastGreatest = fix2G . l2Fix

-- Frankly, I don't understand what I'm writing - I was just trying to
-- match the types...
newtype Fix f = Fix { unFix :: f (Fix f) }

cata :: Functor f => (f a -> a) -> Fix f -> a
cata f = f . fmap (cata f) . unFix

ana :: Functor f => (a -> f a) -> a -> Fix f
ana f = Fix . fmap (ana f) . f

g2Fix :: Functor f => Greatest f -> Fix f
g2Fix (Greatest f a) = ana f a

fix2L :: Functor f => Fix f -> Least f
fix2L x = Least $ \ f -> cata f x

l2Fix :: Least f -> Fix f
l2Fix (Least k) = k Fix

fix2G :: Fix f -> Greatest f
fix2G f@(Fix _) = Greatest unFix f
