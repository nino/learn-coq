Require Import Arith.PeanoNat.
Require Import Nat.
Require Import Lia.

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

