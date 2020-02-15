Require Export base_lemma.

Definition Inj {A B} (f: A -> B) :=
  forall (a1 a2: A), f a1 = f a2 -> a1 = a2.
Definition Surj {A B} (f: A -> B) :=
  forall (b: B), exists (a: A), f a = b.

Definition Bij {A B} (f: A -> B) := Inj f /\ Surj f.

(* This is stronger than bij *)
Definition Bij2 {A B} (f: A -> B) := exists (g: B -> A),
  (forall a, g (f a) = a) /\ (forall b, f (g b) = b).

Definition compose {A B C: Set} (f: B -> C) (g: A -> B): A -> C :=
  fun (a: A) => f (g a).

Definition Hom_set (A B: Set) := A -> B.

Definition Hom_set_func (S: Set) {T V: Set} (f: T -> V) :=
  fun (g: S -> T) => compose f g.

Definition not_empty_set (S: Set) := exists (s: S), True.

(* Bunch of lemmas *)

Lemma inj_r: forall {A B} (f: A -> B) (a1 a2: A),
  Inj f -> f a1 = f a2 -> a1 = a2.
Proof.
  intros.
  destruct (H a1 a2); auto.
Qed.

Lemma nat_succ_inj: Inj S.
Proof.
  unfold Inj. intros.
  - intros. injection H. auto.
Qed.

Lemma nat_succ_not_surj: not (Surj S).
Proof.
  unfold not. intros. unfold Surj in H.
  destruct (H O). discriminate H0.
Qed.

Section Examples.

Definition nat_id (n: nat): nat := n.

Example nat_id_surj: Surj nat_id.
Proof.
  unfold Surj. intros. exists b. unfold nat_id. auto.
Qed.

End Examples.

Lemma equal_const_f: forall {A B} {x1 x2: B} (Hne: not_empty_set A),
  (fun _: A => x1) = (fun _: A => x2) -> x1 = x2.
Proof.
  intros. destruct Hne as [a _].
  exact (equal_f H a).
Qed.
