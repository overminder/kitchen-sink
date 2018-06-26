module IdInt where

import qualified Data.Map as M
import Control.Monad.State

import Lambda

newtype IdInt = IdInt Int
  deriving (Eq, Ord, Enum)

firstBoundId = IdInt 0

instance Show IdInt where
  show (IdInt i) = if i < 0
    then "f" ++ show (-i)
    else "x" ++ show i


toIdInt :: Ord v => LC v -> LC IdInt
toIdInt e = evalState (conv e) (0, fvmap)
  where
    fvmap = foldr (\(v, i) m -> M.insert v (IdInt (-i)) m) M.empty
                  (zip (freeVars e) [1..])

type M v a = State (Int, M.Map v IdInt) a

convVar :: Ord v => v -> M v IdInt
convVar v = do
  (i, m) <- get
  case M.lookup v m of
    Nothing -> do
      let ii = IdInt i
      put (i + 1, M.insert v ii m)
      pure ii
    Just ii -> pure ii

conv :: Ord v => LC v -> M v (LC IdInt)
conv = \case
  Var v -> Var <$> convVar v
  Lam v e -> Lam <$> convVar v <*> conv e
  App f a -> App <$> conv f <*> conv a
