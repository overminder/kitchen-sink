module HOAS where

import qualified Data.Map as M
import IdInt
import Lambda

data HOAS
  = HVar IdInt
  | HLam (HOAS -> HOAS)
  | HApp HOAS HOAS

nf :: LC IdInt -> LC IdInt
nf = toLC . nfh . fromLC

nfh :: HOAS
nfh = \case
  e@(HVar _) -> e
  HLam b -> HLam (nfh . b)
  HApp f a ->
    case whnf f of
      HLam b -> nfh (b a)
      f' -> HApp f' (nfh a)

whnf :: HOAS -> HOAS
whnf = \case
  e@(HVar _) -> e
  HLam b -> HLam b
  HApp f a ->
    case whnf f of
      HLam b -> whnf (b a)
      f' -> HApp f' a


