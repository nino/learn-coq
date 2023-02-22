Require Import Unicode.Utf8.

Module OurR.
  (* Basics *)

  Parameter R : Set.
  Declare Scope R_scope.
  Delimit Scope R_scope with R.
  Local Open Scope R_scope.

  Parameter R0 : R.
  Parameter R1 : R.

  Parameter Rplus : R → R → R.
  Parameter Rmult : R → R → R.
  Parameter Ropp : R → R.
  Parameter Rinv : R → R.

  Infix "+" := Rplus : R_scope.
  Infix "*" := Rmult : R_scope.
  Notation "- x" := (Ropp x) : R_scope.
  Notation "/ x" := (Rinv x) : R_scope.

  Definition Rminus (r1 r2 : R) : R := r1 + -r2.
  Definition Rdiv (r1 r2 : R) : R := r1 * /r2.

  Infix "-" := Rminus : R_scope.
  Infix "/" := Rdiv : R_scope.

  Fixpoint N_to_R (n : nat) : R :=
    match n with
    | O => R0
    | S O => R1
    | S n' => R1 + N_to_R n'
    end.

  Coercion N_to_R : nat >-> R.

  (* Field equations *)

  Axiom R1_neq_R0 : R1 ≠ R0.
  Axiom Rplus_comm : ∀ r s : R, r + s = s + r.
  Axiom Rplus_assoc : ∀ r s t : R, r + s + t = r + (s + t).
  Axiom Rplus_opp_r : ∀ r : R, r + -r = 0.
  Axiom Rplus_0_l : ∀ r : R, 0 + r = r.

  Lemma Rplus_0_r : ∀ r : R, r + 0 = r.
  Proof.
    intros. rewrite <- Rplus_comm. rewrite Rplus_0_l. reflexivity.
  Qed.

  Lemma Rplus_opp_l : ∀ r : R, -r + r = 0.
  Proof.
    intros. rewrite Rplus_comm. rewrite Rplus_opp_r. reflexivity.
  Qed.

  Lemma Ropp_0 : -0 = 0.
  Proof.
    rewrite <- (Rplus_0_l (-0)).
    rewrite Rplus_opp_r.
    reflexivity.
  Qed.

  Lemma Rplus_cancel_l : ∀ r s t, r + s = r + t → s = t.
  Proof.
    intros r s t H.
    rewrite <- Rplus_0_l.
    rewrite <- (Rplus_opp_l r).
    rewrite Rplus_assoc.
    rewrite <- H.
    rewrite <- Rplus_assoc.
    rewrite Rplus_opp_l.
    rewrite Rplus_0_l.
    reflexivity.
  Qed.

  Lemma R0_unique : ∀ r s, r + s = r → s = R0.
  Proof.
    intros r s H.
    rewrite <- Rplus_0_r in H.
    eapply Rplus_cancel_l.
    apply H.
  Qed.

  Axiom Rmult_comm : ∀ r s : R, r * s = s * r.
  Axiom Rmult_assoc : ∀ r s t : R, r * s * t = r * (s * t).
  Axiom Rinv_l : ∀ r : R, r ≠ 0 → /r * r = R1.


End OurR.
