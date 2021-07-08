module SignLattice where

import Data.Maybe (fromMaybe)

data Sign
  = STop
  | SZero
  | SPos
  | SNeg
  | SBot
  deriving (Show, Eq, Enum)

class Lattice x where
  (⊑) :: x -> x -> Maybe Bool
  (⊔) :: x -> x -> x
  (⊓) :: x -> x -> x

instance Lattice Sign where
  x ⊑ y = Just $ case (x, y) of
    (_, STop) -> True
    (SBot, _) -> True
    otherwise -> x == y

  x ⊔ y = case (x, y) of
    (SBot, _) -> y
    (_, SBot) -> x
    otherwise -> if x == y then x else STop

  x ⊓ y = case (x, y) of
    (STop, _) -> y
    (_, STop) -> x
    otherwise -> if x == y then x else SBot

instance (Lattice x, Lattice y) => Lattice (x, y) where
  (x1, y1) ⊑ (x2, y2) = (&&) <$> x1 ⊑ x2 <*> y1 ⊑ y2

  (x1, y1) ⊔ (x2, y2) = (x1 ⊔ x2, y1 ⊔ y2)

  (x1, y1) ⊓ (x2, y2) = (x1 ⊓ x2, y1 ⊓ y2)

-- Quickcheck this
isMonotone :: (Lattice x, Lattice y) => x -> x -> (x -> y) -> Bool
isMonotone x1 x2 f = fromMaybe True $ (&&) <$> fwd <*> bwd
 where
  fwd = do
    r <- x1 ⊑ x2
    if r
      then f x1 ⊑ f x2
      else pure True
  bwd = do
    r <- x2 ⊑ x1
    if r
      then f x2 ⊑ f x1
      else pure True

-- Exercise 6.7

data Sign2
  = S2Top
  | S2PosZ
  | S2NegZ
  | S2Pos
  | S2Zero
  | S2Neg
  | S2One
  | S2Bot
  deriving (Show, Eq, Enum)

instance Lattice Sign2 where
  -- Hmm probably easier to do a graph traversal.
  x ⊑ y = case (x, y) of
    (_, S2Top) -> Just True
    (S2Bot, _) -> Just True
    (S2One, S2Pos) -> Just True
    (S2One, S2PosZ) -> Just True
    (S2Zero, S2PosZ) -> Just True
    (S2Zero, S2NegZ) -> Just True
    (S2Neg, S2NegZ) -> Just True
    otherwise | x == y -> Just True
    otherwise -> Nothing

  {-
  x ⊔ y = case (x, y) of
    (S2Bot, _) -> y
    (_, S2Bot) -> x
    otherwise -> if x == y then x else STop

  x ⊓ y = case (x, y) of
    (STop, _) -> y
    (_, STop) -> x
    otherwise -> if x == y then x else SBot
    -}
