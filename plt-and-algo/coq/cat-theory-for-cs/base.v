(* Classical things *)

Definition Excluded_middle (P: Prop) := P \/ not P.

Axiom excluded_middle: forall P, Excluded_middle P.

(* Decidable and refied equality *)
Definition Has_eq_bool (A: Set) := exists (beq_a: A -> A -> bool), forall (a1 a2: A),
  (a1 = a2 <-> beq_a a1 a2 = true) /\ (a1 <> a2 <-> beq_a a1 a2 = false).
