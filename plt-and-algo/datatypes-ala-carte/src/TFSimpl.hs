{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE AllowAmbiguousTypes  #-}

module TFSimpl where

import           Data.Proxy

data Nil = Nil

data (:+:) a b = a :+: b

type Tup3 = Int :+: String :+: Nil

tup3 :: Tup3
tup3 = 5 :+: "hai" :+: Nil

data Path = Inner Path | Here

data SPath (a :: Path) where
  SHere :: SPath Here
  SInner :: SPath a -> SPath (Inner a)

type family ExtractPath f g :: Maybe Path where
  ExtractPath f f = Just Here
  ExtractPath (g :+: h) f = Or (ExtractPath g f) (ExtractPath h f)
  ExtractPath f g = Nothing

type family Or (a :: Maybe Path) (b :: Maybe Path) :: Maybe Path where
  Or (Just a) b = Just a
  Or a (Just b) = Just b
  Or a b = Nothing

class Extract (p :: Maybe Path) f g where
  extract :: Proxy p -> f -> g

instance Extract (Just Here) (f :+: x) f where
  extract _ (f :+: _) = f

instance Extract (Just p) f g => Extract (Just (Inner p)) (x :+: f) g where
  extract p (_ :+: f) = extract (Proxy :: Proxy (Just p)) f

extract' :: (Extract (ExtractPath f g) f g) => f -> g
extract' = extract (Proxy :: Proxy (ExtractPath f g))
--instance BuildList (Just p) f g => BuildList (Just (Inner p)) (f :+: h) g where
--  build _ = . build (Proxy :: Proxy (Just (Inner p)))
