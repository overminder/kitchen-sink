module Primitives

x : Int
x = 42

foo : String
foo = "helloWorld"

bar : Char
bar = 'b'

quux : Bool
quux = False

rev : List a -> List a
rev = go []
  where
    go : List a -> List a -> List a
    go outs ins = case ins of
      [] => outs
      x :: xs => go (x :: outs) xs


