Require Import Coq.Logic.FunctionalExtensionality.

Require Import base.

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

Theorem not_exist_is_forall_not A (P: Prop): not (exists (a: A), P) <-> forall (a: A), not P.
Proof.
  split.
  - intros. unfold not in *. intros. apply H. exists a. apply H0.
  - intros. unfold not in *. intros. destruct H0. apply (H x H0).
Qed.

Definition not_exist_is_forall_not_fwd A (P: Prop) :=
  proj1 (not_exist_is_forall_not A P).

Definition not_exist_is_forall_not_bwd A (P: Prop) :=
  proj2 (not_exist_is_forall_not A P).

Lemma not_ab_implies_a_notb (A B: Prop): not (A -> B) -> (A -> not B).
Proof.
  intros Hnab a b.
  unfold not in Hnab. apply Hnab. intros _. apply b.
Qed.

(* Eta expansions *)

Lemma eta_expansion: forall {A B} (f g: A -> B),
  (fun x1 => f x1) = (fun x2 => g x2) <-> f = g.
Proof.
  intros. split.
  - intros. apply functional_extensionality.
    intros.
    apply (f_equal (fun (f: A -> B) => f x) H).
  - intros.
    rewrite H.
    tauto.
Qed.

Lemma eta_expansion_r: forall {A B} {f g: A -> B},
  (fun x1 => f x1) = (fun x2 => g x2) -> f = g.
Proof.
  intros. destruct (eta_expansion f g).
  auto.
Qed.

Lemma eta_reduction: forall {A B} {f g: A -> B},
  f = g -> forall x, f x = g x.
Proof.
  intros. rewrite H. auto.
Qed.
