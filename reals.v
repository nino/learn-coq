Require Import Ring.

Module NewReal.

  Parameter R : Set.
  Delimit Scope R_scope with R.
  Local Open Scope R_scope.

  Parameter R0 : R.
  Parameter R1 : R.

  Parameter Rplus : R -> R -> R.
  Parameter Rmult : R -> R -> R.
  Parameter Ropp : R -> R.
  Parameter Rinv : R -> R.

  Infix "+" := Rplus : R_scope.
  Infix "*" := Rmult : R_scope.
  Notation "- x" := (Ropp x) : R_scope.
  Notation "/ x" := (Rinv x) : R_scope.

  Definition Rminus (r1 r2 : R) : R := r1 + -r2.
  Definition Rdiv (r1 r2 : R) : R := r1 * /r2.

  Infix "-" := Rminus : R_scope.
  Infix "/" := Rdiv : R_scope.

  Fixpoint INR (n : nat) : R :=
    match n with
    | O => R0
    | 1 => R1
    | S n' => R1 + INR n'
    end.

  Fail Check (4+5).

  Coercion INR : nat >-> R.

  Check 4 + 5.

  Axiom R1_neq_R0 : INR 1 <> INR 0.
  Axiom Rplus_comm : forall r1 r2 : R, r1 + r2 = r2 + r1.
  Axiom Rplus_assoc : forall r1 r2 r3 : R, (r1 + r2) + r3 = r1 + (r2 + r3).
  Axiom Rplus_opp_r : forall r : R, r + -r = 0.
  Axiom Rplus_0_l : forall r : R, 0 + r = r.

  Lemma Rplus_0_r : forall r : R, r + 0 = r.
  Proof.
    intro r.
    rewrite Rplus_comm.
    rewrite Rplus_0_l.
    reflexivity.
  Qed.

  Axiom Rmult_comm : forall r1 r2 : R, r1 * r2 = r2 * r1.
  Axiom Rmult_accoc : forall r1 r2 r3 : R, r1 * (r2 * r3) = (r1 * r2) * r3.
  Axiom Rinv_l : forall r : R, r <> 0 -> /r * r = 1.
  Axiom Rmult_1_l : forall r : R, 1 * r = r.
  Axiom Rmult_plus_distr_l : forall r1 r2 r3 : R, r1 * (r2 + r3) = r1 * r2 + r1 * r3.

  Lemma Rmult_1_r : forall r : R, r * 1 = r.
  Proof.
    intro r.
    rewrite Rmult_comm.
    rewrite Rmult_1_l.
    reflexivity.
  Qed.


  Lemma R_Ring_Theory : ring_theory R0 R1 Rplus Rmult Rminus Ropp eq.
  Proof.
    constructor.
    intros x.
    rewrite Rplus_0_l. reflexivity.
    intros x y.
    rewrite -> Rplus_comm. reflexivity.
    intros x y z. rewrite Rplus_assoc. reflexivity.
    intro. rewrite Rmult_1_l. reflexivity.
    intros. rewrite Rmult_comm. reflexivity.
    intros.
    rewrite Rmult_accoc. reflexivity.
    intros.
    rewrite -> Rmult_comm.
    rewrite Rmult_plus_distr_l.
    rewrite -> Rmult_comm.
    rewrite Rplus_comm.
    rewrite -> Rmult_comm.
    rewrite Rplus_comm.
    reflexivity.
    intros. unfold Rminus. reflexivity.
    intro. rewrite Rplus_opp_r. reflexivity.
  Qed.

End NewReal.

Require Import Vector.
Require Import Reals.
Check Vector.t.
Check Rplus.

Check map2.

Fixpoint vec_add {A : Type} {n : nat} (addition : A -> A -> A) (xs : t A n) (ys : t A n) : t A n := map2 addition xs ys.

