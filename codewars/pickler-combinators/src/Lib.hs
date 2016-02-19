{-# LANGUAGE TupleSections #-}

-- From http://research.microsoft.com/pubs/64036/picklercombinators.pdf

module Lib
    ( someFunc
    ) where

import Data.Char (isDigit)
import Data.Word (Word8)

newtype PU a = PU (String -> (String, a), a -> String -> String)

(<+>) :: PU a -> PU b -> PU (a, b)
PU (toA, fromA) <+> PU (toB, fromB) = PU (toAB, fromAB)
  where
    toAB s = let (s', a) = toA s
              in fmap (a,) (toB s')
    fromAB (a, b) = fromA a . fromB b

bimap :: PU a -> (a -> b) -> (b -> a) -> PU b
bimap (PU (toA, fromA)) a2b b2a = PU (fmap (fmap a2b) toA, fromA . b2a)

word8 :: PU Word8
word8 = PU (toB, fromB)
  where
    toB (b:bs) = (bs, fromIntegral $ fromEnum b)
    fromB b s = toEnum (fromIntegral b) : s

someFunc :: IO ()
someFunc = putStrLn "someFunc"
