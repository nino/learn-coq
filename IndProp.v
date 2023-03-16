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


