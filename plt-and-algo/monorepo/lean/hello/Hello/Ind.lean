-- Inductive data types

inductive Expr where
| litN (n: Nat) : Expr
| add (x y : Expr) : Expr
deriving Repr

-- Name resolution by default searches in the "current" namespace first
def Expr.eval (e: Expr): Nat := match e with
| litN n => n
| add x y => eval x + eval y

def e0 := Expr.litN 0
def e1 := Expr.litN 1
def eAdd := Expr.add e0 e1

#eval eAdd.eval

-- Polymorphism
inductive MyMaybe (α : Type) where
| some (value : α) : MyMaybe α
| nothing : MyMaybe α
deriving Repr

-- Implicit {α}, and can be explicified via @ (same as Coq)
def MyMaybe.orElse {α : Type} (self: MyMaybe α) (defaultValue : α) : α := match self with
| MyMaybe.some value => value
| MyMaybe.nothing => defaultValue

def some1 := MyMaybe.some 1
#eval some1.orElse 0

-- GADTs. Notice the explicit tycon (sort) signature
inductive ExprG: (α : Type) -> Type 1 where
| litN (n: α): ExprG α
| add (x y : ExprG Nat) : ExprG Nat
| ifLt (x y : ExprG Nat) (t f : ExprG α): ExprG α
-- Need to explicitly have α's Repr instance to make ExprG Repr. Revisit after typeclass chapter

-- Implicit α can be inferred ("automatic implicit arguments")
-- "Pattern-matching definitions" allow `e` to be immediately pattern matched
def ExprG.eval : (e : ExprG α) → α
| litN n => n
| add x y => x.eval + y.eval
| ifLt x y t f => if x.eval < y.eval then t.eval else f.eval

-- No need to explicitly state the α in litN, even though (α : Type) is not explicit in ExprG.
-- Looks like datacon always have implicit type params.
def ExprG.one := litN 1
-- This still works
#check (@ExprG.litN Nat 1)
-- This also works, via named param (nice!)
#check (@ExprG.litN 1 (α := Nat))
def ExprG.two := add one one
def ExprG.three := ifLt one two (add two one) one

#eval ExprG.three.eval

-- Products with more than 2 members are via nested products (hmm)
#check (1, 2, 3).2.1
