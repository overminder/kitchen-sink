-- TaPL: Types and Programming Languages exercises
-- Pierce's TaPL in Lean 4.
-- Good starting point: Ch. 3 (untyped arithmetic), Ch. 5 (untyped lambda calculus).

-- Untyped arithmetic expressions (TaPL Ch. 3)
inductive Term where
  | tTrue  : Term
  | tFalse : Term
  | tIf    : Term → Term → Term → Term
  | tZero  : Term
  | tSucc  : Term → Term
  | tPred  : Term → Term
  | tIsZero : Term → Term
  deriving Repr

def isNumericVal : Term → Bool
  | .tZero   => true
  | .tSucc t => isNumericVal t
  | _        => false

def isVal : Term → Bool
  | .tTrue  => true
  | .tFalse => true
  | t       => isNumericVal t
