Require Import Unicode.Utf8.
Require Import List.
Import ListNotations.
Require Import Nat.

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

Theorem discriminate_ex1 : ∀ (n m : N),
  false = true → n = m.
Proof.
  intros. discriminate.
Qed.

Example discriminate_ex3 : ∀ (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = [] → x = z.
Proof.
  intros. discriminate.
Qed.

Theorem eqb_0_l : ∀ (n : N), 0 =? n = true → n = 0.
Proof.
  intros.
  destruct n.
  - reflexivity.
  - discriminate.
Qed.

Theorem eq_implies_succ_equal : ∀ (n m : N),
  n = m → S n = S m.
Proof.
  intros.
  f_equal.
  assumption.
Qed.

Theorem silly4 : ∀ (n m p q : N),
  (n = m → p = q) → m = n → q = p.
Proof.
  intros n m p q Eq H.
  symmetry in H.
  apply Eq in H. (* Overwrites H:n=m with p=q *)
  symmetry in H.
  apply H.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Theorem double_injective_failed : ∀ (n m : N),
  double n = double m → n = m.
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl. intros eq.
    destruct m as [| m'] eqn:E.
    + reflexivity.
    + discriminate eq.
  - intros eq.
    destruct m as [| m'] eqn:E.
    + discriminate eq.
    + f_equal.
Abort.

Theorem double_injective : ∀ n m,
  double n = double m → n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. intros m eq.
    destruct m as [| m'] eqn:E.
    + reflexivity.
    + discriminate eq.
  - intros m eq.
    destruct m as [| m'] eqn:E.
    + discriminate eq.
    + f_equal.
      apply IHn'.
      injection eq as goal.
      assumption.
Qed.

Theorem eqb_true : ∀ n m, n =? m = true → n = m.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl. intros m eq.
    destruct m as [| m'] eqn:eqM.
    + reflexivity.
    + discriminate eq.
  - simpl. intros m eq.
    destruct m as [| m'] eqn:eqM.
    + discriminate eq.
    + f_equal.
      apply IHn'.
      assumption.
Qed.

Theorem plus_n_n_injective : ∀ n m,
  n + n = m + m → n = m.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl. intros m eq. destruct m as [| m' ] eqn:eqM.
    + reflexivity.
    + discriminate eq.
  - simpl. intros m eq. destruct m as [| m' ] eqn:eqM.
    + discriminate eq.
    + f_equal.
      apply IHn'.
      simpl in eq.
      rewrite PeanoNat.Nat.add_comm in eq.
      replace (m' + S m') with (S m' + m') in eq.
      2: { rewrite PeanoNat.Nat.add_comm. reflexivity. }
      simpl in eq.
      injection eq as I1.
      apply I1.
Qed.

Theorem doulbe_injective_take2_FAILED : ∀ n m,
  double n = double m → n = m.
Proof.
  intros n m.
  induction m as [| m' IHm'].
  - simpl. intros eq. destruct n as [| n'] eqn:E.
    + reflexivity.
    + discriminate eq.
  - intros eq. destruct n as [| n'] eqn:E.
    + discriminate eq.
    + f_equal.
Abort.

Theorem double_injective_take2 : ∀ n m,
  double n = double m → n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m' IHm'].
  - simpl. intros n eq. destruct n as [| n'] eqn:eqN.
    + reflexivity.
    + discriminate eq.
  - simpl. intros n eq. destruct n as [| n'] eqn:eqN.
    + discriminate eq.
    + f_equal. apply IHm'.
      injection eq as goal.
      apply goal.
Qed.

Theorem nth_error_after_last : ∀ (n:N) (X:Type) (l:list X),
  length l = n → nth_error l n = None.
Proof.
  intros.
  generalize dependent n.
  induction l as [| h t IHl].
  - intros n lEq.
    simpl in lEq.
    rewrite <- lEq.
    reflexivity.
  - intros n lEq.
    simpl in lEq.
    rewrite <- lEq.
    simpl.
    apply IHl.
    reflexivity.
Qed.

Definition square n := n * n.

Lemma square_mult : ∀ n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  unfold square.
  rewrite PeanoNat.Nat.mul_assoc.
  replace (n * n * (m * m)) with (n * n * m * m).
  2: { rewrite PeanoNat.Nat.mul_assoc. reflexivity. }
  replace (n * n * m) with (n * m * n).
  2: {
    rewrite PeanoNat.Nat.mul_comm.
    rewrite PeanoNat.Nat.mul_assoc. reflexivity.
  }
  reflexivity.
Qed.

Fixpoint combine {X Y : Type } (lx : list X) (ly : list Y) : list (X * Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.

Theorem combine_split : ∀ X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) → combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l as [| h t IHl].
  - intros.
    unfold split in H.
    injection H as I J. rewrite <- I. rewrite <- J.
    reflexivity.
  - intros l1 l2 H.
    destruct h as [x y].
Admitted.

