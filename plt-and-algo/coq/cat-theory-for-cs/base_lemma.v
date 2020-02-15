Require Export Coq.Logic.FunctionalExtensionality.

Require Export base.

Theorem double_neg (P: Prop): not (not P) <-> P.
Proof.
  split; firstorder.
  destruct (excluded_middle P); auto.
  exfalso. apply H. apply H0.
Qed.

Theorem iff_via_falso (P Q: Prop): (P -> Q) <-> (not Q -> not P).
Proof.
  split; intros H1 H2.
  - unfold not in *. intros p. auto.
  (* The other way requires excluded middle *)
  - unfold not in *. destruct (excluded_middle Q).
    * auto.
    * exfalso. apply H1. apply H. apply H2.
Qed.

Definition iff_via_falso_bwd P Q := proj2 (iff_via_falso P Q).

Theorem not_exist_is_forall_not (A: Set) (P: A -> Prop):
  not (exists (a: A), P a) -> forall (a: A), not (P a).
Proof.
  intros. unfold not in *. intros. apply H. exists a. apply H0.
Qed.

Theorem not_forall_is_exist_not (A: Set) (P: A -> Prop):
  not (forall (a: A), P a) -> exists (a: A), not (P a).
Proof.
  intros. unfold not in *. destruct (excluded_middle (exists a, not (P a))).
  - auto.
  - assert (forall a: A, not (not (P a))).
    apply not_exist_is_forall_not. exact H0.
    exfalso. apply H. intros.
    destruct (double_neg (P a)).
    apply H2. apply (H1 a).
Qed.

Lemma not_ab_implies_a_notb (A B: Prop): not (A -> B) -> (A -> not B).
Proof.
  intros Hnab a b.
  unfold not in Hnab. apply Hnab. intros _. apply b.
Qed.

(* FunctionalExtensionality derived lemmas *)

Lemma func_ext_on_pair: forall {A B C} {f1 f2: A -> B} {g1 g2: A -> C},
  (fun a => (f1 a, g1 a)) = (fun a => (f2 a, g2 a)) -> f1 = f2 /\ g1 = g2.
Proof.
  intros. split; extensionality x; pose (Heq := equal_f H x);
            inversion Heq; reflexivity.
Qed.

Lemma func_ext_on_sum: forall {A B C} {f1 f2: A -> C} {g1 g2: B -> C},
    (fun x => match x with
           | inl a => f1 a
           | inr b => g1 b
           end) =
    (fun x => match x with
           | inl a => f2 a
           | inr b => g2 b
           end) -> f1 = f2 /\ g1 = g2.
Proof.
  intros.
  split; apply functional_extensionality; intros x.
  - apply (equal_f H (inl x)).
  - apply (equal_f H (inr x)).
Qed.
