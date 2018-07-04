(* Enumerated types *)

Inductive day :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day
  .

Definition next_weekday (d:day) :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.

(* Booleans *)

Inductive bool :=
  | true
  | false.

Definition bnot (b:bool) :=
  match b with
  | true => false
  | false => true
  end.

Definition band (b1:bool) (b2:bool) :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition bor (b1:bool) (b2:bool) :=
  match b1 with
  | true => true
  | false => b2
  end.

Notation "a && b" := (band a b).
Notation "a || b" := (bor a b).

Example test_bor1: (bor true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_bor2: (false || false) = false.
Proof. simpl. reflexivity. Qed.
Example test_bor3: (false || true) = true.
Proof. simpl. reflexivity. Qed.
Example test_bor4: (true || true) = true.
Proof. simpl. reflexivity. Qed.

(* Checks, e.g. Check true. *)

(* Compound types *)

Inductive day_range :=
  | exact_day : day -> day_range
  | between_days : day -> day -> day_range
  .

Module NatPlayground.
(* Just an example to show how nats are defined -- Coq has it in its stdlib. *)

Inductive nat :=
  | O
  | S : nat -> nat
  .

Definition pred (n:nat) :=
  match n with
  | O => O
  | S n' => n'
  end.

Example test_pred0: (pred O) = O.
Proof. simpl. reflexivity. Qed.

Example test_pred1: (pred (S O)) = O.
Proof. simpl. reflexivity. Qed.

End NatPlayground.

Fixpoint evenb (n:nat) :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Example test_evenb_0: (evenb 0) = true.
Proof. simpl. reflexivity. Qed.
Example test_evenb_1: (evenb 1) = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.
(* Just an example to show how nats operators are defined. *)

Fixpoint plus (n1:nat) (n2:nat) :=
  match n1 with
  | O => n2
  | S n1' => plus n1' (S n2)
  end.

Fixpoint mult (n1 n2 : nat) :=
  match n1 with
  | O => O
  | S n1' => plus n2 (mult n1' n2)
  end.

Fixpoint minus (n1 n2 : nat) :=
  match n1, n2 with
  | _, O => n1
  | S n1', S n2' => minus n1' n2'
  | O, S _ => O
  end.

Fixpoint exp (base pow : nat) :=
  match pow with
  | O => 1
  | S pow' => mult base (exp base pow')
  end.

Example test_mult_2_3: (mult 2 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_exp_2_3: (exp 2 3) = 8.
Proof. simpl. reflexivity. Qed.

Fixpoint nat_eq (n1 n2 : nat) :=
  match n1, n2 with
  | S n1', S n2' => nat_eq n1' n2'
  | O, O => true
  | S _, O => false
  | O, S _ => false
  end.

Fixpoint nat_lt (n1 n2 : nat) :=
  match n1, n2 with
  | S n1', S n2' => nat_lt n1' n2'
  | O, O => false
  | S _, O => true
  | O, S _ => false
  end.

End NatPlayground2.

Fixpoint fact (n:nat) :=
  match n with
  | O => 1
  | S n' => mult n (fact n')
  end.

Example test_fact_4: (fact 4) = 24.
Proof. simpl. reflexivity. Qed.

(* Proof by simpl *)

Theorem plus_O_l : forall n : nat, 0 + n = n.
  Proof. simpl. reflexivity. Qed.

Theorem plus_1_l : forall n : nat, 1 + n = S n.
  Proof. simpl. reflexivity. Qed.

Theorem mult_0_l : forall n : nat, 0 * n = 0.
  Proof. simpl. reflexivity. Qed.

Theorem plus_id_example : forall n m : nat,
  n = m ->
  n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity. Qed.

