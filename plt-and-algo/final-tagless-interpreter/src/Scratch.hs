module Scratch where

import Prelude hiding (and, or)
import qualified Prelude as P

class Language r where
  here :: r (a, h) a
  before :: r h a -> r (any, h) a
  lambda :: r (a, h) b -> r h (a -> b)
  apply :: r h (a -> b) -> r h a -> r h b

  loop :: r h (a -> a) -> r h a

  int :: Int -> r h Int
  add :: r a Int -> r a Int -> r a Int
  mult :: r a Int -> r a Int -> r a Int
  down :: r a Int -> r a Int
  up :: r a Int -> r a Int
  gte :: r a Int -> r a Int -> r a Bool

  bool :: Bool -> r h Bool
  and :: r h Bool -> r h Bool -> r h Bool
  or :: r h Bool -> r h Bool -> r h Bool
  neg :: r h Bool -> r h Bool

  ifte :: r h Bool -> r h a -> r h a -> r h a

-- I could also have used (->)'s applicative instances.. That would
-- be more precise.
instance Language (->) where
  here = fst
  before f = f . snd
  lambda body h a = body (a, h)
  apply f a h = f h $ a h

  loop f = fix . f
   where
    fix f = let x = f x in x

  int = liftL
  add a b = liftL (+) `apply` a `apply` b
  mult a b = liftL (*) `apply` a `apply` b
  down i = liftL (+ (-1)) `apply` i
  up i = liftL (+ 1) `apply` i
  gte a b = liftL (>=) `apply` a `apply` b

  bool = liftL
  and a b = liftL (\ a b -> P.and [a, b]) `apply` a `apply` b
  or a b = liftL (\ a b -> P.or [a, b]) `apply` a `apply` b
  neg a = liftL not `apply` a

  ifte a b c = liftL (\ a b c -> if a then b else c) `apply` a `apply` b `apply` c

liftL = const

eval = ($ ())
