Require Import Unicode.Utf8.
Require Import List.
Require Import Nat.
Import ListNotations.

Theorem silly1: ∀ (n m : nat),
  n = m → n = m.
Proof.
  intros n m eq.
  exact eq.
Qed.

Theorem silly2 : forall (n m o p : nat),
  n = m → (n = m → [n; o] = [m; p]) → [n; o] = [m; p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2.
  apply eq1.
Qed.

Theorem silly2a : forall (n m : nat),
  (n, n) = (m, m) ->
  (forall (q r : nat), (q, q) = (r, r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.
Qed.

Theorem silly_ex : forall p,
  (forall n, Nat.even n = true -> Nat.even (S n) = false) ->
  (forall n, Nat.even n = false -> Nat.odd n = true) ->
  Nat.even p = true ->
  Nat.odd (S p) = true.
Proof.
  intros.
  apply H0. apply H. assumption.
Qed.

Theorem silly3: forall (n m : nat),
  n = m -> m = n.
Proof.
  intros n m H.
  Fail apply H.
  symmetry. apply H.
Qed.

Theorem rev_exercise1 : ∀ (l l' : list nat),
  l = rev l' → l' = rev l.
Proof.
  intros.
  symmetry.
  rewrite <- rev_involutive.
  rewrite H.
  reflexivity.
Qed.

Example trans_eq_example: forall (a b c d e f : nat),
  [a; b] = [c; d] ->
  [c; d] = [e; f] ->
  [a; b] = [e; f].
Proof.
  intros.
  rewrite H.
  apply H0.
Qed.

Theorem trans_eq: forall (X:Type) (n m o: X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2.
  rewrite eq1.
  apply eq2.
Qed.

Example trans_eq_example': forall (a b c d e f : nat),
  [a; b] = [c; d] ->
  [c; d] = [e; f] ->
  [a; b] = [e; f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m := [c; d]).
  - apply eq1.
  - apply eq2.
Qed.

Fixpoint minustwo n :=
  match n with
  | O => O
  | S O => O
  | S (S n) => n
  end.

Example trans_eq_exercise : forall (n m o p : nat),
  m = (minustwo o) -> (n + p) = m -> (n + p) = (minustwo o).
Proof.
  intros.
  transitivity m; assumption.
Qed.

Theorem S_injective : forall (n m : nat),
  S n = S m -> n = m.
Proof.
  intros n m H.
  assert (H2 : n = pred (S n)). { reflexivity. }
  rewrite H2. rewrite H. simpl. reflexivity.
Qed.

Theorem S_injective' : forall (n m : nat),
  S n = S m -> n = m.
Proof.
  intros n m H.
  injection H as Hnm.
  apply Hnm.
Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n; m] = [o; o] -> n = m.
Proof.
  intros n m o H.
  injection H as H1 H2.
  transitivity o.
  - assumption.
  - symmetry. assumption.
Qed.

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
  intros X x y z l j H1 H2.
  rewrite H2 in H1.
  injection H1 as I1 I2.
  transitivity z.
  assumption.
  symmetry. assumption.
Qed.

Theorem discriminate_ex₁ : forall (n m : nat),
  false = true -> n = m.
Proof.
  intros.
  discriminate H.
Qed.

Example discriminate_ex₃ : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = [] -> x = z.
Proof.
  intros. discriminate.
Qed.

Theorem eqb_0_1 : forall n,
  0 =? n = true -> n = 0.
Proof.
  intros.
  destruct n.
  - reflexivity.
  - discriminate.
Qed.

Theorem f_equal : ∀ (A B : Type) (f : A → B) (x y : A),
  x = y → f x = f y.
Proof. intros. rewrite H. reflexivity. Qed.

Theorem eq_implies_succ_equal : forall n m, n = m -> S n = S m.
Proof.
  intros.
  f_equal. assumption.
Qed.

