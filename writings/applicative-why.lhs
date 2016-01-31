# Why Applicative

Let's look at the minimal definition of Functor, Applicative and Monad:

> {-# LANGUAGE RebindableSyntax #-}
> module WhyApplicative where
> import Prelude (String, error)

> class Functor f where
>   fmap :: (a -> b) -> f a -> f b

> (<$) :: Functor f => a -> f b -> f a
> a <$ fb = fmap (const a) fb

> const :: a -> b -> a
> const a _ = a

> (<$>) :: Functor f => (a -> b) -> f a -> f b
> (<$>) = fmap

> flip :: (a -> b -> c) -> b -> a -> c
> flip f b a = f a b

`fmap` applies an function to a wrapped argument.
However, there's no way to compose two wrapped things.

> class Functor f => Applicative f where
>   (<*>) :: f (a -> b) -> f a -> f b
>   pure :: a -> f a

> (*>) :: Applicative f => f a -> f b -> f b
> fa *> fb = const1 <$> fa <*> fb

> const1 :: a -> b -> b
> const1 = flip const

> (<*) :: Applicative f => f a -> f b -> f a
> fa <* fb = const <$> fa <*> fb

`<*>` applies a wrapped function to a wrapped argument.
Using it, we can compose two or more wrapped things. More specifically,
we can apply n wrapped arguments to an n-ary wrapped function.

`pure` wraps a given argument.

> class Applicative f => Monad f where
>   (>>=) :: f a -> (a -> f b) -> f b

`>>=` composes two monadic actions.
`fail` is a design error...

>   fail :: String -> f a
>   fail = error

Note that Monad is strictly more powerful than Applicative, since `<*>` can
be implemented using `>>=`:

> (<*.>) :: Monad f => f (a -> b) -> f a -> f b
> (<*.>) ff fa = ff >>= \ f -> fa >>= \ a -> pure (f a)

> return :: Monad f => a -> f a
> return = pure

> (>>) :: Monad f => f a -> f b -> f b
> (>>) = (*>)

> join :: Monad f => f (f a) -> f a
> join ffa = ffa >>= id

> id :: a -> a
> id a = a

