Lemma eqb_with_self_if_true: forall (n : nat), Nat.eqb n n = true.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl. assumption.
Qed.

