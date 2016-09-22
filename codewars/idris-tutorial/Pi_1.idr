module Pi_1

isSingleton : Bool -> Type
isSingleton True = Nat
isSingleton False = List Nat

toSingleton : (x : Bool) -> isSingleton x
toSingleton True = 0
toSingleton False = Nil
