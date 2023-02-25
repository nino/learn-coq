Require Import Reals.

Module Type VECTOR_SPACE.
  Parameter V : Type.
  Parameter Vadd : V -> V -> V.
  Parameter Vsmult : R -> V -> V.
  Parameter v0 : V.

  Infix "+" := Vadd.
  Infix "*" := Vsmult.

  Axiom Vadd_comm : forall (u v : V), u + v = v + u.
  Axiom Vadd_assoc : forall (u v w : V), (u + v) + w = u + (v + w).
  Axiom Vsmult_assoc : forall (v : V) (a b : R), a * (b * v) = (a * b) * v.
  Axiom Vadd_id : forall (v : V), v + v0 = v.
  Axiom Vadd_inv : forall (v : V), exists (w : V), v + w = v0.
  Axiom Vsmult_id : forall (v : V), 1 * v = v.
  Axiom Vsmult_add_distr : forall (u v : V) (a : R), a * (u + v) = a * u + a * v.
  Axiom Vadd_smult_distr : forall (a b : R) (v : V), (a + b) * v = a * v + b * v.
End VECTOR_SPACE.

Module Rvec <: VECTOR_SPACE.
  Local Open Scope R_scope.

  Definition V := R.
  Definition Vadd := Rplus.
  Definition Vsmult := Rmult.
  Definition v0 := R0.

  Definition Vadd_comm := Rplus_comm.
  Definition Vadd_assoc := Rplus_assoc.

  Lemma Vsmult_assoc : forall (v : V) (a b : R), a * (b * v) = (a * b) * v.
  Proof.
    intros.
    rewrite Rmult_assoc.
    reflexivity.
  Qed.

  Definition Vadd_id := Rplus_0_r.

  Lemma Vadd_inv : forall (v : V), exists (w : V), v + w = v0.
  Proof.
    intros.
    exists (-v).
    apply Rplus_opp_r.
  Qed.

  Lemma Vsmult_id : forall (v : V), 1 * v = v.
  Proof. intros. apply Rmult_1_l. Qed.

  Definition Vsmult_add_distr : forall (u v : V) (a : R), a * (u + v) = a * u + a * v.
  Proof. intros. apply Rmult_plus_distr_l. Qed.

  Lemma Vadd_smult_distr : forall (a b : R) (c : V), (a + b) * c = a * c + b * c.
  Proof.
    intros.
    rewrite Rmult_comm.
    replace (a * c) with (c * a).
    2: { apply Rmult_comm. }
    replace (b * c) with (c * b).
    2: { apply Rmult_comm. }
    apply Rmult_plus_distr_l.
  Qed.

End Rvec.

