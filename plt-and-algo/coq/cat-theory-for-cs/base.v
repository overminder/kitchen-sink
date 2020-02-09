(* Classical things *)

Definition Excluded_middle (P: Prop) := P \/ not P.

Axiom excluded_middle: forall P, Excluded_middle P.
