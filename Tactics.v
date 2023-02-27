Require Import Unicode.Utf8.
Require Import List.
Require Import Nat.
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
  - intros l1 l2 H.
    unfold split in H.
    inversion H. reflexivity.
  - intros [| h1 l1] [| h2 l2] H.
    + simpl in H. destruct (split t), h. discriminate H.
    + simpl in H. destruct (split t), h. discriminate H.
    + simpl in H. destruct (split t), h. discriminate H.
    + simpl in H. destruct (split t), h.
      inversion H.
      replace t with (combine l1 l2).
      2: { apply IHl. inversion H. reflexivity. }
      reflexivity.
Qed.

Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.

Theorem sillyfun1_odd_FAILED : forall n : N,
  sillyfun1 n = true -> odd n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3).
  (* Stuck *)
Abort.

Theorem sillyfun1_odd : forall n : N,
  sillyfun1 n = true -> odd n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:Heqe3.
  - apply PeanoNat.Nat.eqb_eq in Heqe3.
    rewrite Heqe3.
    reflexivity.
  - destruct (n =? 5) eqn:Heqe5.
    + apply PeanoNat.Nat.eqb_eq in Heqe5.
      rewrite Heqe5.
      reflexivity.
    + discriminate eq.
Qed.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct b eqn:eqB.
  - destruct (f true) eqn:eqFt.
    + rewrite eqFt. apply eqFt.
    + destruct (f false) eqn:eqFf.
      * apply eqFt.
      * apply eqFf.
  - destruct (f true) eqn:eqFt.
    + destruct (f false) eqn:eqFf.
      * rewrite eqFt. apply eqFt.
      * rewrite eqFf. apply eqFf.
    + destruct (f false) eqn:eqFf.
      * rewrite eqFt. apply eqFf.
      * rewrite eqFf. apply eqFf.
Qed.

Lemma n_eq_n : forall n : nat, (n =? n) = true.
Proof.
  intros.
  apply PeanoNat.Nat.eqb_eq.
  reflexivity.
Qed.

Theorem eqb_sym : ∀ (n m : nat),
  (n =? m) = (m =? n).
Proof.
  intros.
  destruct (n =? m) eqn:nmEq.
  - apply PeanoNat.Nat.eqb_eq in nmEq.
    symmetry.
    apply PeanoNat.Nat.eqb_eq.
    symmetry. apply nmEq.
  - destruct (m =? n) eqn:mnEq.
    + apply PeanoNat.Nat.eqb_eq in mnEq.
      symmetry in mnEq.
      apply PeanoNat.Nat.eqb_neq in nmEq.
      rewrite mnEq in nmEq.
      rewrite <- PeanoNat.Nat.eqb_neq in nmEq.
      rewrite n_eq_n in nmEq.
      discriminate.
    + reflexivity.
Qed.

Theorem eqb_trans : ∀ n m p,
  n =? m = true →
  m =? p = true →
  n =? p = true.
Proof.
  intros.
  apply PeanoNat.Nat.eqb_eq in H, H0.
  apply PeanoNat.Nat.eqb_eq.
  transitivity m; assumption.
Qed.

Definition split_combine_statement : Prop :=
  ∀ (X Y : Type) (l1 : list X) (l2 : list Y) (l : list (X * Y)),
  length l1 = length l2 → combine l1 l2 = l →
  split l = (l1, l2).

Lemma nil_length_0 : ∀ (X : Type) (l : list X),
  length l = 0 → l = [].
Proof.
  intros. induction l.
  - reflexivity.
  - discriminate H.
Qed.

Theorem split_combine : split_combine_statement.
Proof.
  unfold split_combine_statement.
  intros X Y l1 l2 l Len.
  generalize dependent l.
  induction l1 as [| h1 l1' IHl'].
  - simpl. intros l H.
    simpl in Len.
    symmetry in Len.
    apply nil_length_0 in Len.
    rewrite Len.
    rewrite <- H.
    reflexivity.
  - simpl. intros l H.
    destruct l2 as [| h2 l2'].
    + discriminate Len.
    + rewrite <- H.
      simpl.
Admitted.

(* Moving on *)
