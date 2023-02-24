Require Import Reals.
Set Implicit Arguments.

Variable V : Type.
Variable Vadd : V -> V -> V.
Variable Vsmult : R -> V -> V.
Infix "+" := Vadd.
Infix "*" := Vsmult.
Variable v0 : V.

Record vector_theory : Prop := mk_vt {
  Vadd_comm : forall (u v : V), u + v = v + u;
  Vadd_assoc : forall (u v w : V), (u + v) + w = u + (v + w);
  Vsmult_assoc : forall (v : V) (a b : R), a * (b * v) = (a * b) * v;
  Vadd_id : forall (v : V), v + v0 = v;
  Vadd_inv : forall (v : V), exists (w : V), v + w = v0;
  Vsmult_id : forall (v : V), 1 * v = v;
  Vsmult_add_distr : forall (u v : V) (a : R), a * (u + v) = a * u + a * v;
  Vadd_smult_distr : forall (a b : R) (v : V), (a + b) * v = a * v + b * v;
}.

Lemma unique_add_id : forall (v w : V), vector_theory -> v + w = v -> w = v0.
Proof.
  intros.
  replace 

