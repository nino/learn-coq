Require Import Arith.PeanoNat.
Require Import Nat.
Require Import Lia.
Require Import List.
Import ListNotations.

Section CollatzConjecture.

  Fixpoint div2 (n : nat) :=
    match n with
    | 0 => 0
    | 1 => 0
    | S (S n) => S (div2 n)
    end.

  Definition f (n : nat) :=
    if even n then div2 n
    else (3 * n) + 1.

  Inductive reaches_1 : nat -> Prop :=
    | term_done : reaches_1 1
    | term_more (n : nat) : reaches_1 (f n) -> reaches_1 n.

  Conjecture collatz : forall n, reaches_1 n.

  Fail
  Fixpoint reaches_1_in (n : nat) :=
    if n =? 1 then 0
    else 1 + reaches_1_in (f n).
  (* So if it still fails, why did we add the conjecture? *)

End CollatzConjecture.

Module LePlayground. (* hehe *)

  Inductive le : nat -> nat -> Prop :=
    | le_n (n : nat) : le n n
    | le_S (n m : nat) : le n m -> le n (S m).

End LePlayground.

Inductive clos_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | t_step (x y : X) :
      R x y -> clos_trans R x y
  | t_trans (x y z : X) :
      clos_trans R x y ->
      clos_trans R y z ->
      clos_trans R x z.

Inductive clos_refl_trans {X : Type} (R: X->X->Prop) : X->X->Prop :=
  | tr_step (x y : X) :
      R x y -> clos_refl_trans R x y
  | tr_trans (x y z : X) :
      clos_refl_trans R x y ->
      clos_refl_trans R y z ->
      clos_refl_trans R x z
  | tr_refl (x y : X) :
      clos_refl_trans R x y ->
      clos_refl_trans R y x.

Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) :
      Perm3 [a; b; c] [b; a; c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a; b; c] [a; c; b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.

(*
   Exercise 1: perm
   Perm3 [1; 2; 3] [3; 2; 1] is True, because
   Perm3 [1; 2; 3] [1; 3; 2] is True, and
   Perm3 [1; 3; 2] [3; 1; 2] is True, and
   Perm3 [3; 1; 2] [3; 2; 1] is True, and
   transitivity.

   And Perm3 [1; 2; 3] [1; 2; 3] is True because you can swap 12 twice and then transitivity.
 *)

(* Another evenness *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

(* From Induction.v *)
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Theorem ev_double : forall n, ev (double n).
Proof.
  intros n.
  induction n.
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IHn.
Qed.

Theorem ev_inversion : forall (n : nat),
  ev n -> (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E. destruct E as [| n' E'] eqn:EE.
  - left. reflexivity.
  - right. exists n'.
    split.
    + reflexivity.
    + apply E'.
Qed.

Theorem evSS_ev : forall (n : nat), ev (S (S n)) -> ev n.
Proof.
  intros n H.
  apply ev_inversion in H.
  destruct H as [H0 | H1].
  - discriminate H0.
  - destruct H1 as [n' [HSS Hev]].
    injection HSS as Hnn.
    rewrite <- Hnn in Hev.
    apply Hev.
Qed.

Theorem evSS_ev' : forall (n : nat), ev (S (S n)) -> ev n.
Proof.
  intros n ESS.
  inversion ESS as [| n' E' Heq].
  apply E'.
Qed.

Theorem just_trying_stuff_outside_the_book : ~ forall n : nat, n < 2.
Proof.
  intros contra.
  pose (Hn := contra 2).
  inversion Hn.
  rewrite <- PeanoNat.Nat.leb_le in H0.
  discriminate H0.
Qed.

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. inversion H.
Qed.

Theorem SSSSev__even : forall n : nat, ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H.
  inversion H.
  inversion H1.
  apply H3.
Qed.

Theorem ev5_nonsense : ev 5 -> 2 + 2 = 9.
Proof.
  intros H5.
  inversion H5.
  inversion H0.
  inversion H2.
Qed.

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] -> [n] = [m].
Proof.
  intros n m o H.
  inversion H.
  reflexivity.
Qed.

Theorem inversion_ex2 : forall n : nat, S n = 0 -> 2 + 2 = 5.
Proof.
  intros. inversion H.
Qed.

(* Recall that, *)
Definition Even x := exists n : nat, x = double n.

Lemma ev_Even_firsttry : forall n : nat, ev n -> Even n.
Proof.
  unfold Even.
  intros n E.
  inversion E as [EQ' | n' E' EQ'].
  - exists 0. reflexivity.
Abort.

Lemma ev_Even : forall n : nat,
  ev n -> Even n.
Proof.
  intros n E.
  induction E as [| n' E' IH].
  - unfold Even. exists 0. reflexivity.
  - unfold Even in IH.
    destruct IH as [k Hk].
    rewrite Hk.
    unfold Even.
    exists (S k).
    simpl.
    reflexivity.
Qed.

Theorem ev_Even_iff : forall n : nat, ev n <-> Even n.
Proof.
  intros n. split.
  - apply ev_Even.
  - unfold Even.
    intros [k Hk].
    rewrite Hk.
    apply ev_double.
Qed.

Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m Hn Hm.
  induction Hn as [| n' En IHn].
  - simpl. apply Hm.
  - simpl. apply ev_SS. apply IHn.
Qed.

Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  split.
  - intros Hev'.
    induction Hev' as [ | | n' m' Hn' Hm' Hev' IH].
    + apply ev_0.
    + apply (ev_SS 0 ev_0).
    + apply (ev_sum n' m' Hm' IH).
      (* I might have fucked up some of those names in the induction *)
  - intros Hev.
    induction Hev as [ | n' Hn' IH].
    + apply ev'_0.
    + replace (S (S n')) with (2 + n') by reflexivity.
      apply (ev'_sum 2 n' ev'_2 IH).
Qed.

Theorem ev_ev__ev : forall n m, ev (n + m) -> ev n -> ev m.
Proof.
  intros n m Hsum Hn.
  induction Hn as [| n' Hn' IH].
  - simpl in Hsum. assumption.
  - apply IH.
    simpl in Hsum.
    inversion Hsum.
    assumption.
Qed.

Lemma double_is_n_plus_n : forall n : nat,
  n + n = double n.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite PeanoNat.Nat.add_comm. simpl.
    rewrite IHn. reflexivity.
Qed.

Theorem ev_plus_plus : forall n m p : nat,
  ev (n + m) -> ev (n + p) -> ev (m + p).
Proof.
  (* Do this without induction or case analysis, with some tedious
   * rewriting and clever assertions. Hint: Is (n + m) + (n + p) even? *)
  intros n m p Hnm Hnp.
  assert (Hdouble: ev (double n)) by apply ev_double.
  assert (Hnplusn: n + n = double n) by apply (double_is_n_plus_n).
  (* I guess technically we did use induction in that one?? *)
  rewrite <- Hnplusn in Hdouble.
  assert (Hsum: ev ((n + m) + (n + p))) by apply (ev_sum (n + m) (n + p) Hnm Hnp).
  replace ((n + m) + (n + p)) with ((n + n) + (m + p)) in Hsum.
  2: {
    rewrite <- (PeanoNat.Nat.add_assoc n m (n + p)).
    rewrite -> (PeanoNat.Nat.add_assoc m n p).
    rewrite (PeanoNat.Nat.add_comm m n).
    rewrite <- (PeanoNat.Nat.add_assoc n m p).
    rewrite -> (PeanoNat.Nat.add_assoc n n (m + p)).
    reflexivity.
  }
  apply (ev_ev__ev (n + n) (m + p)) in Hsum; assumption.
Qed.

Module Playground.

  Inductive le : nat -> nat -> Prop :=
    | le_n (n : nat) : le n n
    | le_S (n m : nat) (H : le n m) : le n (S m).

  Notation "n <= m" := (le n m).

  Theorem test_le1 : 3 <= 3.
  Proof. apply le_n. Qed.

  Theorem test_le2 : 3 <= 6.
  Proof.
    apply le_S.
    apply le_S.
    apply le_S.
    apply le_n.
  Qed.

  Theorem test_le3 : (2 <= 1) -> 2 + 2 = 5.
  Proof.
    intros H.
    inversion H.
    inversion H2.
  Qed.

  Definition lt (n m : nat) := le (S n) m.
  Notation "m < n" := (lt m n).

End Playground.

Inductive total_relation : nat -> nat -> Prop :=
  | any_nats (n m : nat) : total_relation n m.

Theorem total_relation_is_total : forall n m : nat, total_relation n m.
Proof. apply any_nats. Qed.

(* Not sure how to do this *)
(* Inductive empty_relation : nat -> nat -> Prop := *)
(*   | no_nats (n m : nat) (H : False) : empty_relation n m. *)

(* Theorem empty_relation_is_empty : forall n m : nat, ~ empty_relation n m. *)
(* Proof. *)
(*   intros. intro contra. *)
(*   destruct n. *)
(*   - apply (no_nats 0 m) in contra. *)

Lemma Sn_le_m_then_n_le_m : forall n m : nat, S n <= m -> n <= m.
Proof.
  intros.
  induction H.
  - apply le_S. apply le_n.
  - apply le_S.
    apply IHle.
Qed.

Lemma le_trans : forall m n o : nat, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o Hmn Hno.
  induction Hmn.
  - assumption.
  - apply Sn_le_m_then_n_le_m in Hno.
    apply IHHmn.
    assumption.
Qed.

Theorem O_le_n : forall n : nat, 0 <= n.
Proof.
  intros.
  induction n.
  - apply le_n.
  - apply le_S. assumption.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m : nat,
  n <= m -> S n <= S m.
Proof.
  intros.
  induction H.
  - apply le_n.
  - apply le_S. assumption.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m : nat,
  S n <= S m -> n <= m.
Proof.
  intros.
  inversion H.
  - apply le_n.
  - apply Sn_le_m_then_n_le_m in H1.
    assumption.
Qed.

Theorem lt_ge_cases : forall n m : nat,
  n < m \/ n >= m.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - destruct m.
    + right. apply le_n.
    + left. unfold lt.
      apply n_le_m__Sn_le_Sm.
      apply O_le_n.
Admitted.


