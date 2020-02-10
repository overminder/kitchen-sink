Require Import Coq.Logic.FunctionalExtensionality.
Require Coq.Arith.EqNat.
Require Coq.Structures.Equalities.

Require Import base.
Require Import base_lemma.
Require Import ch1.

Example page7: forall (S T V: Set) (f: T -> V) (Hne: not_empty_set S),
  Inj f <-> Inj (Hom_set_func S f).
Proof.
  intros. split.
  - intro Hf. unfold Inj. intros g h.
    intros. unfold Hom_set_func in H. unfold compose in H.
    apply functional_extensionality. intros.
    (* Probably need something higher level here..
       Yeah, eta_reduction makes this a lot simpler. *)
    assert (Hred := eta_reduction H).
    simpl in Hred.
    (* inj_r is easier to use than inj *)
    apply (inj_r f _ _ Hf).
    apply Hred.
  - intros Hinj a1 a2 Heq. cbv in Hinj.
    (* The below construction of const func is crucial. *)
    set (Ha := Hinj (fun _ => a1) (fun _ => a2)).
    simpl in Ha. rewrite Heq in Ha.
    assert (Haux : (fun _ : S => f a2) = (fun _ : S => f a2)).
    reflexivity.
    apply Ha in Haux.
    apply (eta_expansion_const Hne). apply Haux.
Qed.

(* Exercies *)

(* For ex_section_1_2_1, we need to construct a function to do case
   analysis. In Coq we need decidable equality *)
Section HowToConstructSuchFunction.

Import Coq.Arith.EqNat.

Lemma beq_nat_not_refl: forall (m n: nat), m <> n -> beq_nat m n = false.
Proof.
  induction m; destruct n; firstorder.
Qed.

(* To construct a function that do equality check on its args, we need
   this sort of eqb and associated reified equality (eq_refl -> bool).
   So it's not for arbitrary type. *)
Example can_construct_func: forall (B: Set) (a1 a2: nat) (b1 b2: B),
  a1 <> a2 -> exists (f: nat -> B), f a1 = b1 /\ f a2 = b2.
Proof.
  intros.
  exists (fun a => if beq_nat a a1 then b1 else b2).
  split.
  - rewrite <- beq_nat_refl. reflexivity.
  - rewrite beq_nat_not_refl; firstorder.
Qed.

Example can_extend_func: forall (B: Set) (a1 a2: nat) (b1 b2: B) (f: nat -> B),
  f a1 = b1 -> a1 <> a2 -> exists g, g a1 = b1 /\ g a2 = b2.
Proof.
  intros B a1 a2 b1 b2 f Heq Hneq.
  exists (fun a => if beq_nat a a2 then b2 else f a).
  split.
  - rewrite beq_nat_not_refl; firstorder.
  - rewrite <- beq_nat_refl. reflexivity.
Qed.

End HowToConstructSuchFunction.

Section HowToConstructSuchFunctionWithHasEqBool.

Example can_construct_func2: forall (A B: Set) (a1 a2: A) (b1 b2: B),
  Has_eq_bool A -> a1 <> a2 -> exists (f: A -> B), f a1 = b1 /\ f a2 = b2.
Proof.
  intros A B a1 a2 b1 b2 [beq_a Ha] Hne.
  exists (fun a => if beq_a a a1 then b1 else b2).
  split.
  - destruct (Ha a1 a1) as [[Heq _] [_ _]].
    replace (beq_a a1 a1) with true. reflexivity.
    symmetry. apply Heq. reflexivity.
  - destruct (Ha a2 a1) as [[_ _] [Hnea _]].
    replace (beq_a a2 a1) with false. reflexivity.
    symmetry. apply Hnea. unfold not. intros. apply Hne. auto.
Qed.

End HowToConstructSuchFunctionWithHasEqBool.

Definition Hom_func_set {W S: Set} (h: W -> S) (T: Set) :=
  fun (g: S -> T) => compose g h.

Definition Has_two_elems (S: Set) := exists s1 s2: S, s1 <> s2.

Theorem ex_section_1_2_1:
  forall (T W S: Set), Has_two_elems T -> Has_eq_bool S ->
       forall h: W -> S, Surj h <-> Inj (Hom_func_set h T).
Proof.
  intros T W S Htwo [beq_S eqdec_S] h. split.
  - intros Hsurj.
    + cbv. (* cbv is to unfold all *)
      intros a1 a2 Heq.
      apply functional_extensionality. intros s.
      destruct (Hsurj s) as [w Hws].
      assert (Heta := eta_reduction Heq w).
      simpl in Heta. rewrite Hws in Heta. exact Heta.
  - apply iff_via_falso_bwd.
    unfold not. intros Hnsurj.
    cbv in Hnsurj.
    apply not_forall_is_exist_not in Hnsurj.
    assert (Hinv : exists b: S, forall a: W, h a <> b).
      destruct Hnsurj. exists x.
      apply not_exist_is_forall_not. exact H.

    destruct Hinv as [x Hneqha].
    destruct Htwo as [t1 [t2 Hneqt]].
    intros Hinj.
    cbv in Hinj.
    (* Crucial to construct this function *)
    pose (Hinj (fun _ => t1)
               (fun s => if beq_S s x then t2 else t1)).
    simpl in e.
    assert ((fun _ : W => t1) = (fun a : W => if beq_S (h a) x then t2 else t1)).
    apply functional_extensionality.
    intros w.
    assert (beq_S (h w) x = false).
    destruct (eqdec_S (h w) x) as [[_ _] [neq_S _]].
    apply neq_S. apply Hneqha.
    rewrite H. reflexivity.
    apply e in H.
    pose (eta_reduction H x).
    simpl in e0.
    assert (beq_S x x = true).
    destruct (eqdec_S x x) as [[eq_S _] [_ _]].
    apply eq_S. reflexivity.
    rewrite H0 in e0.
    destruct (Hneqt e0).
Qed.

Definition Pair_func {X S T: Set} (f: X -> S) (g: X -> T) :=
  fun x => (f x, g x).

Theorem ex_section_1_2_2a: forall (X S T: Set) (f: X -> S) (g: X -> T),
  Bij (Pair_func f g).
Abort.
