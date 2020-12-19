{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module SystemF where

-- Chapter 23: System F

-- Defns

newtype FBool = FBool { unFBool :: forall a. a -> a -> a }
newtype FList a = FList { unFList :: forall r. (a -> r -> r) -> r -> r }

fromFBool :: FBool -> Bool
fromFBool b = unFBool b True False

toFBool :: Bool -> FBool
toFBool b = FBool $ \t f -> if b then t else f

fromFList :: FList a -> [a]
fromFList xs = unFList xs (:) []

nilFList :: FList a
nilFList = FList $ \_ nil -> nil

consFList :: a -> FList a -> FList a
consFList x (FList xs) = FList $ \cons nil -> cons x (xs cons nil)

toFList :: [a] -> FList a
toFList = foldr consFList nilFList

test1 = fromFList . toFList $ [1, 2, 3]

-- 23.4.12 insert and sort in pure System F

fInsert :: forall a. (a -> a -> FBool) -> FList a -> a -> FList a
fInsert cmp xs x = snd $ unFList xs combine (Just x, nilFList)
 where
  combine y (mbX, xs) = case mbX of
    Nothing -> (mbX, consFList y xs)
    Just x -> unFBool (cmp x y) (Nothing, consFList x (consFList y xs))
                                (mbX, consFList y xs)

