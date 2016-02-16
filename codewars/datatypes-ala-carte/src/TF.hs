{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE AllowAmbiguousTypes  #-}

module TF where

import           Data.Proxy

newtype Fix f = In { out :: f (Fix f) }

data Lit a = Lit Int
             deriving (Functor)

data Add a = Add a a
             deriving (Functor)

data (f :+: g) a = Inl (f a) | Inr (g a)
                   deriving (Functor)

type family Elem (f :: * -> *) (g :: * -> *) :: Maybe Path where
  Elem f f = 'Just 'Here
  Elem f (l :+: r) = Choose (Elem f l) (Elem f r)
  Elem f g = 'Nothing

type family Choose f g :: Maybe Path where
  Choose ('Just f) g = 'Just ('L f)
  Choose f ('Just g) = 'Just ('R g)
  Choose f g = 'Nothing

data Path = Here | L Path | R Path

class MakeInj (path :: Maybe Path) f g where
  mkInj :: Proxy path -> f a -> g a

instance MakeInj ('Just 'Here) f f where
  mkInj _ = id

instance MakeInj ('Just p) f l => MakeInj ('Just ('L p)) f (l :+: r) where
  mkInj _ = Inl . mkInj (Proxy :: Proxy ('Just p))

instance MakeInj ('Just p) f r => MakeInj ('Just ('R p)) f (l :+: r) where
  mkInj _ = Inr . mkInj (Proxy :: Proxy ('Just p))

type f :<: g = MakeInj (Elem f g) f g

inject :: (f :<: g) => f a -> g a
inject = mkInj (Proxy :: Proxy (Elem f g))

{-

lit :: (Lit :<: f) => Int -> Fix f
lit = inject . Lit

add :: (Add :<: f) => Fix f -> Fix f -> Fix f
add a = inject . Add a

expr :: Fix (Add :+: Lit)
expr = add (lit 5) (add (lit 7) (lit 30))
-}
