Require Import Unicode.Utf8.

Theorem mul_0_r : ∀ n:nat,
  n * 0 = 0.
Proof.
  intros.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. assumption.
Qed.

Theorem plus_n_Sm : ∀ n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite IHn'. reflexivity.
Qed.

Lemma n_plus_0_r : ∀ n : nat, n + 0 = n.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.



Theorem add_comm : ∀ n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl.
    rewrite n_plus_0_r.
    reflexivity.
  - simpl.
    rewrite IHn'.
    rewrite plus_n_Sm.
    reflexivity.
Qed.

Lemma n_plus_0_l : ∀ n : nat, 0 + n = n.
Proof. intros. rewrite add_comm. rewrite n_plus_0_r. reflexivity. Qed.

Theorem add_assoc : ∀ n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - rewrite n_plus_0_l.
    rewrite n_plus_0_l.
    reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Require Import Arith.

Lemma example_proof : ∀ x y : nat,  (x + y) *(x + y)= x * x + 2 * x * y + y * y.
Proof.
  intros x y.
  ring_simplify.
  reflexivity.
Qed.

Lemma not_not : ∀ a b : bool, negb a = negb b → a = b.
Proof.
  intros.
  destruct a.
  - unfold negb in H.
    destruct b.
    + reflexivity.
    + discriminate.
  - destruct b.
    + discriminate.
    + reflexivity.
Qed.


Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : ∀ n, double n = n + n.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl.
    rewrite <- plus_n_Sm.
    rewrite IHn'.
    reflexivity.
Qed.

Theorem eqb_refl : ∀ n : nat,
  (n =? n) = true.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. assumption.
Qed.

Definition even := Nat.even.

Lemma cancel_negb : ∀ a b : bool, negb a = negb b -> a = b.
Proof.
  intros a b H.
  destruct a as [].
  - destruct b as [].
    + reflexivity.
    + discriminate.
  - destruct b as [].
    + discriminate.
    + reflexivity.
Qed.

Theorem even_S : ∀ n : nat,
  even (S n) = negb (even n).
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - rewrite IHn'.
    rewrite Bool.negb_involutive.
    simpl. reflexivity.
Qed.

