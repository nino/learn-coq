Require Import Unicode.Utf8.

Module TuplePlayground.

  Inductive bit : Type :=
    On | Off.

  Inductive nybble : Type := bits (b0 b1 b2 b3 : bit).

  Check (bits On Off On Off) : nybble.

  Definition all_zero (nybble : nybble) : bool :=
    match nybble with
    | (bits Off Off Off Off) => true
    | _ => false
    end.

  Compute (all_zero (bits On Off Off Off)).
  Compute (all_zero (bits Off Off Off Off)).

End TuplePlayground.

Fixpoint even n :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Check even.

Definition odd n := negb (even n).

Module NatPlayground2.

  Fixpoint plus n m : nat :=
    match n with
    | O => m
    | S n' => plus n' (S m)
    end.

  Fixpoint mult n m : nat :=
    match n with
    | O => O
    | S O => m
    | S n' => plus m (mult n' m)
    end.

  Example test_3x3: (mult 3 3) = 9.
  Proof. simpl. reflexivity. Qed.

  Fixpoint minus n m : nat :=
    match n, m with
    | O, _ => O
    | S _, O => n
    | S n', S m' => minus n' m'
    end.

End NatPlayground2.

Fixpoint exp base power : nat :=
  match power with
  | O => S O
  | S power' => mult base (exp base power')
  end.


(* Exercise: Factorial *)

Fixpoint factorial (n:nat) : nat :=
  match n with
  | O => 1
  | S n' => mult n (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Fixpoint leb n m :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Definition ltb (n m : nat) :=
  match n, m with 
  | O, O => false
  | O, S _ => true
  | S _, O => false
  | S _, S m' => leb n m'
  end.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1: (2 <? 2) = false.
Proof.
  easy. Qed.

Example test_ltb2: (ltb 2 4) = true.
Proof.
  easy. Qed.


Example test_ltb3: (ltb 4 2) = false.
Proof.
  easy. Qed.


Theorem plus_O_n : ∀ n : nat, 0 + n = n.
Proof.
  intro n. simpl. reflexivity.
Qed.

(* Proof by rewriting *)

Theorem plus_id_example : ∀ n m : nat, n = m → n + n = m + m.
Proof.
  intros n m. intros H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_id_exercise : ∀ n m o : nat,
  n = m → m = o → n + m = m + o.
Proof.
  intros n m o.
  intros H.
  intros H2.
  rewrite -> H.
  rewrite <- H2.
  reflexivity.
Qed.

Check mult_n_O.
Check mult_n_Sm.
Check plus_n_O.

Theorem mult_n_1 : ∀ p : nat,
  p * 1 = p.
Proof.
  intros p.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  reflexivity.
Qed.

Theorem plus_1_neq_0_firsttry : ∀ n : nat,
  eqb (n + 1) 0 = false.
Proof.
  intros n.
  destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_true_elim2 : ∀ b c : bool,
  (b && c)%bool = true → c = true.
Proof.
  intros b c.
  destruct b.
  - simpl. intros H. assumption.
  - simpl. intros H. rewrite <- H. destruct c.
    + rewrite H. reflexivity.
    + reflexivity.
Qed.


Theorem and_true : ∀ a b : Prop,
  a ∧ b → b.
Proof.
  intros a b. intros H.
  destruct H as [Ha Hb]. assumption.
Qed.

Theorem zero_nbeq_plus_1 : ∀ n : nat,
  eqb 0 (n + 1) = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.
Qed.


(* More exercises *)

Theorem identity_fn_applied_twice :
  ∀ (f : bool → bool),
  (∀ (x : bool), f x = x) → ∀ (b : bool), f (f b) = b.
Proof.
  intros. rewrite H. rewrite H. reflexivity.
Qed.

Theorem negation_fn_applied_twice :
  ∀ (f : bool → bool),
  (∀ (x : bool), f x = negb x) → ∀ b, f (f b) = b.
Proof.
  intros. rewrite H. rewrite H.
  destruct b.
  { reflexivity. }
  { reflexivity. }
Qed.

Lemma orb_true_l : ∀ b:bool, (true || b)%bool = true.
Proof.
  reflexivity.
Qed.

Lemma andb_true_l : ∀ b:bool, (true && b)%bool = b.
Proof. reflexivity. Qed.

Lemma anbd_false_l : ∀ b, (false && b)%bool = false.
Proof.
  reflexivity. Qed.

Lemma orb_false_l : ∀ b, (false || b)%bool = b.
Proof. reflexivity. Qed.

Theorem andb_eq_orb :
  ∀ (b c : bool),
  (andb b c = orb b c) → b = c.
Proof.
  intros.
  destruct b.
  - rewrite orb_true_l in H.
    rewrite <- H.
    rewrite andb_true_l.
    reflexivity.
  - rewrite anbd_false_l in H.
    rewrite orb_false_l in H.
    assumption.
Qed.

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).


Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B1 Z
  | B0 rest => B1 rest
  | B1 rest => B0 (incr rest)
  end.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => 0
  | B1 rest => 1 + 2 * (bin_to_nat rest)
  | B0 rest => 2 * (bin_to_nat rest)
  end.

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof. easy. Qed.

Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof. easy. Qed.

Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof. easy. Qed.

Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
Proof. easy. Qed.

Example test_bin_incr5 :
        bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof. easy. Qed.

Example test_bin_incr6 :
        bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
Proof. easy. Qed.

