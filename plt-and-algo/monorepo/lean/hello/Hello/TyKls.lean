inductive PosNat
| one : PosNat
| succ (n : PosNat): PosNat

def PosNat.plus (m n : PosNat) : PosNat := match m with
| one => succ n
| succ m' => succ (plus m' n)

-- Lean is strict so prefer tail recursion
def PosNat.ofNat' : (n : Nat) → PosNat → PosNat
| 0, pn => pn
| n' + 1, pn => ofNat' n' (succ pn)

-- Non-tail version
def PosNat.ofNatNT : (n : Nat) → PosNat → PosNat
| 0 => id
| n' + 1 => succ ∘ ofNat' n'

def PosNat.toNat : PosNat → Nat → Nat
| one, n => n + 1
| succ pn, n => pn.toNat (Nat.succ n)

instance : Add PosNat where
  add := PosNat.plus

-- The (n : Nat) can be omitted
instance (n : Nat): OfNat PosNat (Nat.succ n) where
  ofNat := PosNat.ofNat' n PosNat.one

instance : ToString PosNat where
  toString pn := toString (pn.toNat 0)

-- Both tail and nontail versions seem to work?
#eval (30001 : PosNat)

inductive Even
| zero
| add2 (n : Even)
deriving Repr

instance : OfNat Even 0 where
  ofNat := Even.zero

instance [OfNat Even n]: OfNat Even (n + 2) where
  ofNat := Even.add2 (OfNat.ofNat n)

#check (254 : Even)

-- Exercise: HMul
structure PPoint (α : Type) where
x : α
y : α

instance [HMul α β χ] : HMul (PPoint α) β (PPoint χ) where
  hMul p a := { x := p.x * a, y := p.y * a }

instance [ToString α]: ToString (PPoint α) where
  toString p := s!"({toString p.x}, {toString p.y})"

#eval {x := 1, y := 2 : PPoint _} * 3

-- Hmm how to use the induction tactic?

theorem PosNat.add1_comm : ∀ n : PosNat, 1 + n = n + 1 := by
  intro n; induction n
  ·  rfl
  sorry

theorem PosNat.comm : ∀ m n : PosNat, m + n = n + m := by
  sorry

-- This is how Nat.zero_add works
theorem Nat.add1_comm : ∀ n : Nat, 1 + n = n + 1
| 0 => rfl
| n + 1 => congrArg _ (add1_comm n)

-- Arrays and indexing

def northernTrees := #["sloe", "birch", "elm", "oak"]
#check northernTrees[3]

structure NonEmptyList (α : Type) where
  head : α
  tail : List α

def idahoSpiders : NonEmptyList String := {
  head := "Banded Garden Spider",
  tail := [
    "Long-legged Sac Spider",
    "Wolf Spider",
    "Hobo Spider",
    "Cat-faced Spider"
  ]
}

def NonEmptyList.get? : NonEmptyList α → Nat → Option α
  | xs, 0 => some xs.head
  | xs, n + 1 => xs.tail.get? n

-- abbrev is important to make the function reducible.
-- If this is a def, @[simp] or simp [inBounds] also works
abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i ≤ xs.tail.length

theorem atLeastThreeSpiders : idahoSpiders.inBounds 2 := by
simp [NonEmptyList.inBounds]
simp [idahoSpiders]
apply Nat.le.step
apply Nat.le.step
simp

-- See https://github.com/leanprover/fp-lean/issues/137
-- simp was changed in Lean 4.3. Use decide or simp with config instead.
theorem notSixSpiders : ¬idahoSpiders.inBounds 5 := by
simp (config := {decide := true})

theorem add11 : 1 + 1 = 2 := by simp

theorem le00 : 0 ≤ 0 := by simp
theorem le01 : 0 ≤ 1 := by simp
theorem le11 : 1 ≤ 1 := by simp
theorem le12 : 1 ≤ 2 := by
  apply Nat.le.step
  simp

theorem le12' : 1 ≤ 1 + 1 := by
  decide

def NonEmptyList.get (xs : NonEmptyList α) (i : Nat) (_ok : xs.inBounds i) : α :=
  match i with
  | 0 => xs.head
  | n + 1 => xs.tail[n] -- getElem implicitly uses _ok

instance : HAppend (List α) (NonEmptyList α) (NonEmptyList α) where
  hAppend
  | [], ys => ys
  | x :: xs, ys => { head := x, tail := xs ++ [ys.head] ++ ys.tail }

-- Dependently typed coersion is interesting...
