# Question

In the follow Haskell code

    length' (_:xs) = 1 + length' xs

How do we know what `_` is?


# Answer

`:` is one of the constructor for `List` type:

    data List a = a : List a
                | []

So pattern matching something with `(_:xs) :: List a` means that `_ :: a` and
`xs :: List a`.
