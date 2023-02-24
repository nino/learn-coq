Require Import Unicode.Utf8.
Require Import List.
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

Example trans_eq_example'' : forall (a b c d e f : nat),
  [a; b] = [c; d] ->
  [c; d] = [e; f] ->
  [a; b] = [e; f].
Proof.
  intros.
  transitivity [c; d].
  apply H.
  apply H0.
Qed.

Fixpoint minustwo n :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Example trans_eq_exercise : forall (n m o p : nat),
  m = (minustwo o) ->
  (n + p) = m ->
  (n + p) = (minustwo o).
Proof.
  intros.
  transitivity m; assumption.
Qed.

Definition N := nat.

Theorem S_injective : ∀ (n m : N), S n = S m → n = m.
Proof.
  intros n m H.
  injection H as Hnm.
  easy.
Qed.

Theorem injection_ex₁ : ∀ (n m o : N),
  [n; m] = [o; o] → n = m.
Proof.
  intros n m o H.
  injection H as H₁ H₂.
  rewrite H₁. rewrite H₂. reflexivity.
Qed.

Example injection_ex₃ : ∀ (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j →
  j = z :: l →
  x = y.
Proof.
  intros.
  rewrite H0 in H.
  injection H as I1 I2.
  transitivity z.
  - assumption.
  - symmetry. assumption.
Qed.


