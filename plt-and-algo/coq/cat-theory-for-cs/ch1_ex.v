Require Coq.Arith.EqNat.
Require Coq.Structures.Equalities.

Require Import ch1.

Example page7: forall (S T V: Set) (f: T -> V) (Hne: not_empty_set S),
  Inj f <-> Inj (Hom_set_func S f).
Proof.
  intros. split.
  - intros Hf g h H. cbv in H. extensionality x.
    pose (Heq := equal_f H). simpl in Heq.
    eapply inj_r. apply Hf. apply Heq.
  - intros Hinj a1 a2 Heq. cbv in Hinj.
    (* The below construction of const func is crucial. *)
    set (Ha := Hinj (fun _ => a1) (fun _ => a2)).
    simpl in Ha. rewrite Heq in Ha.
    pose (Hconst := Ha eq_refl).
    eapply equal_const_f.
    apply Hne. apply Hconst.
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
      eapply equal_f in Heq.
      rewrite <- Hws. apply Heq.
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
    pose (equal_f H x).
    simpl in e0.
    assert (beq_S x x = true).
    destruct (eqdec_S x x) as [[eq_S _] [_ _]].
    apply eq_S. reflexivity.
    rewrite H0 in e0.
    destruct (Hneqt e0).
Qed.

Definition pair_func {X S T: Set} (fg: (X -> S) * (X -> T)) :=
  let (f, g) := fg in
  fun x => (f x, g x).

Theorem ex_section_1_2_2a: forall (X S T: Set),
  Bij (@pair_func X S T).
Proof.
  intros. unfold Bij. split.
  - intros a1 a2 H. unfold pair_func in H.
    destruct a1 as [f1 g1].
    destruct a2 as [f2 g2].
    pose (Heq := func_ext_on_pair H).
    inversion Heq.
    subst.
    reflexivity.
  - intros b. exists ((fun x => fst (b x)), (fun x => (snd (b x)))). cbv.
    extensionality x. destruct (b x). reflexivity.
Qed.

(* Not sure what ex1_2_2b means *)

Definition phi {S T V: Set} (fg: (S -> V) * (T -> V)): S + T -> V :=
  fun st =>
    let (f, g) := fg in
    match st with
    | inl s => f s
    | inr t => g t
    end.

Theorem ex_section_1_2_3a: forall (S T V: Set),
  Bij (@phi S T V).
Proof.
  intros. unfold Bij. split.
  - intros x1 x2 H. destruct x1 as [f1 g1]. destruct x2 as [f2 g2].
    unfold phi in H. pose (Heq := func_ext_on_sum H).
    inversion Heq. subst. reflexivity.
  - intros fg. exists ((fun s => fg (inl s)), (fun t => fg (inr t))).
    cbv. extensionality st. destruct st; reflexivity.
Qed.

