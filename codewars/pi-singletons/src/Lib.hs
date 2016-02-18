{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Lib where

import           Prelude    hiding (drop, head, map, replicate, tail, take,
                             zipWith, (++))

import           Data.Proxy

data Vec a n where
  VNil :: Vec a Zero
  VCons :: a -> Vec a n -> Vec a (Succ n)

-- promoted to type level by data kinds
data Nat = Zero | Succ Nat

data SNat (a :: Nat) where
  SZero :: SNat Zero
  SSucc :: SNat a -> SNat (Succ a)

type family (a :: Nat) :< (b :: Nat) :: Bool
type instance m :< Zero = False
type instance Zero :< Succ n = True
type instance (Succ m) :< (Succ n) = m :< n

type family (Add (a :: Nat) (b :: Nat)) :: Nat
type instance (Add Zero n) = n
type instance (Add (Succ m) n) = Add m (Succ n)
-- to be defined

type family (Sub (a :: Nat) (b :: Nat)) :: Nat
type instance (Sub m Zero) = m
type instance (Sub (Succ m) (Succ n)) = Sub m n

type family (Min (a :: Nat) (b :: Nat)) :: Nat
type instance (Min Zero n) = Zero
type instance (Min m Zero) = Zero
type instance (Min (Succ m) (Succ n)) = Succ (Min m n)

add :: (Add a b ~ c) => SNat a -> SNat b -> SNat c
add SZero b = b
add (SSucc a) b = a `add` (SSucc b)

addP :: (Add a b ~ c) => Proxy a -> Proxy b -> Proxy c
addP _ _ = Proxy :: Proxy (c :: Nat)

fromSNat :: SNat a -> Int
fromSNat SZero = 0
fromSNat (SSucc n) = 1 + fromSNat n

map :: (a -> b) -> Vec a n -> Vec b n
map f VNil = VNil
map f (VCons x xs) = VCons (f x) (map f xs)

index :: ((a :< b) ~ True) => SNat a -> Vec s b -> s
index SZero (VCons s _) = s
index (SSucc n) (VCons _ b) = index n b

replicate :: s -> SNat a -> Vec s a
replicate s SZero = VNil
replicate s (SSucc n) = VCons s $ replicate s n

-- Both vectors must be of equal length
zipWith :: (a -> b -> c) -> Vec a n -> Vec b n -> Vec c n
zipWith f VNil VNil = VNil
zipWith f (VCons a as) (VCons b bs) = VCons (f a b) $ zipWith f as bs

(++) :: Vec v m -> Vec v n -> Vec v (Add m n)
VNil ++ b = b
VCons a as ++ b = as ++ VCons a b

-- The semantics should match that of take for normal lists.
take :: SNat m -> Vec a n -> Vec a (Min m n)
take SZero _ = VNil
take _ VNil = VNil
take (SSucc n) (VCons a as) = VCons a $ take n as

-- The semantics should match that of drop for normal lists.
drop :: SNat m -> Vec a n -> Vec a (Sub n (Min m n))
drop SZero as = as
drop _ VNil = VNil
drop (SSucc n) (VCons a as) = drop n as
--
head :: Vec a (Succ n) -> a
head (VCons a _) = a
--
tail :: Vec a (Succ n) -> Vec a n
tail (VCons _ as) = as
