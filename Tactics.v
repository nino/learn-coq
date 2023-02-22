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

