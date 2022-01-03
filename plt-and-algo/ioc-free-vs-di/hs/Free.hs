{-# LANGUAGE DeriveFunctor #-}

module Free where

-- Free and instances

data Free f a
  = Join (f (Free f a))
  | Pure a
  deriving (Functor)

instance Functor f => Applicative (Free f) where
  pure = Pure
  Pure f <*> Pure a = Pure (f a)
  Pure f <*> Join a = Join (fmap (fmap f) a)
  Join f <*> Pure a = Join (fmap (fmap ($ a)) f)
  Join f <*> Join a = Join (fmap x a)
    where x fa = Join (fmap (<*> fa) f)

instance Functor f => Monad (Free f) where
  return = pure
  Pure a >>= f = f a
  Join fa >>= f = Join (fmap (>>= f) fa)

liftF :: Functor f => f a -> Free f a
liftF = Join . fmap Pure

-- Example operations

-- Hmm can we avoid having to return things?
-- Maybe the operational monad can help
-- http://jstimpfle.de/blah/free-monads-gadts.html factored the similar parts
-- out.
data OpF a
  = AddF Int Int (Int -> a)
  | IntF Int (Int -> a)
  | PrintF Int a
  deriving (Functor)

type Op a = Free OpF a

add x y = liftF (AddF x y id)
int n = liftF (IntF n id)
printI n = liftF (PrintF n ())

sampleProgram :: Op ()
sampleProgram = do
  n <- int 42
  n2 <- add n n
  printI n2

interp :: Op a -> IO a
interp op = case op of
  Pure a -> return a
  Join ff -> case ff of
    AddF x y k -> interp (k (x + y))
    IntF n k -> interp (k n)
    PrintF n k -> print n >> interp k

main = interp sampleProgram

