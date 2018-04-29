-- Original program

myMap f = \case
  [] -> []
  x:xs -> f x:myMap xs

xs = myMap (+1) [1, 2, 3]
ys = myMap (*2) [1, 2, 3]

-- Defunctionalized (dispatch style) closure conversion

data Closure
  = Add Int
  | Mul Int

-- Note that args is a hetrogenerous list and can't be represented
-- directly in a typed source language
apply args = \case
  Add x -> let [y] = args
            in x + y
  Mul x -> let [y] = args
            in x * y

myMap f = \case
  [] -> []
  x:xs -> apply f [x]:myMap xs

xs = myMap (Add 1) [1, 2, 3]
ys = myMap (Mul 2) [1, 2, 3]

