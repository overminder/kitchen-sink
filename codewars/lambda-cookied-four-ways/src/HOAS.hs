module HOAS where

import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import IdInt
import Lambda

data HOAS
  = HVar IdInt
  | HLam (HOAS -> HOAS)
  | HApp HOAS HOAS

-- How to define a show instance for this?
-- We might just use (show . toLC) ...

nf :: LC IdInt -> LC IdInt
nf = toLC . nfh . fromLC

nfh :: HOAS -> HOAS
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

fromLC :: LC IdInt -> HOAS
fromLC = from M.empty
  where
    from m = \case
      Var v -> fromMaybe (HVar v) (M.lookup v m)
      Lam v e -> HLam $ \x -> from (M.insert v x m) e
      App f a -> HApp (from m f) (from m a)

toLC :: HOAS -> LC IdInt
toLC = to firstBoundId
  where
    to n = \case
      HVar v -> Var v
      HLam b -> Lam n (to (succ n) (b (HVar n)))
      HApp f a -> App (to n f) (to n a)
