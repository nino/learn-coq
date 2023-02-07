Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. assumption.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite IHn'. reflexivity.
Qed.

Lemma n_plus_0_r : forall n : nat, n + 0 = n.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.



Theorem add_comm : forall n m : nat,
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

Lemma n_plus_0_l : forall n : nat, 0 + n = n.
Proof. intros. rewrite add_comm. rewrite n_plus_0_r. reflexivity. Qed.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - rewrite n_plus_0_l.
    rewrite n_plus_0_l.
    reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

