Require Import Unicode.Utf8.
Require Import Nat.
Require Import PeanoNat.

Definition plus_claim : Prop := 2 + 2 = 4.

Theorem plus_claim_is_true : plus_claim.
Proof. reflexivity. Qed.

Example and_example : 3 + 4 = 7 ∧ 2 * 2 = 4.
Proof. split; reflexivity. Qed.

Lemma and_intro : ∀ A B : Prop, A → B → A ∧ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

Example and_example' : 3 + 4 = 7 ∧ 2 * 2 = 4.
Proof. apply and_intro; reflexivity. Qed.

Example and_exercise : forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros. split.
  - destruct m as [| m'] eqn:mEq.
    + rewrite Nat.add_0_r in H.
      apply H.
    + destruct n.
      * discriminate H.
      * discriminate H.
  - destruct n.
    + simpl in H. apply H.
    + destruct m.
      * reflexivity.
      * simpl in H.
        destruct (n + S m); discriminate.
Qed.

Lemma proj2 : forall P Q : Prop, P /\ Q -> Q.
Proof. intros. destruct H as [HP HQ]. apply HQ. Qed.

Theorem and_commut : forall P Q : Prop, P /\ Q -> Q /\ P.
Proof. intros P Q [HP HQ]. split; assumption. Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - split; assumption.
  - assumption.
Qed.

Lemma factor_is_0 : forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm].
  - rewrite Hn. apply Nat.mul_0_l.
  - rewrite Hm. apply Nat.mul_0_r.
Qed.

Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof. intros. left. assumption. Qed.

Lemma zero_or_succ : forall n : nat, n = 0 ∨ n = S (pred n).
Proof.
  intros [| n' ].
  - left. reflexivity.
  - right. reflexivity.
Qed.

Lemma mult_is_O : forall n m : nat, n * m = 0 → n = 0 ∨ m = 0.
Proof.
  intros [|n] [|m] H.
  - left. reflexivity.
  - left. reflexivity.
  - right. reflexivity.
  - discriminate H.
Qed.

Theorem or_commut : forall P Q : Prop, P ∨ Q → Q ∨ P.
Proof.
  intros P Q [HP | HQ].
  - right. assumption.
  - left. assumption.
Qed.

Module NotPlayground.

  Definition not (P : Prop) : Prop := P → False.
  Notation "¬ x" := (not x) : type_scope.

  Check not : Prop → Prop.

End NotPlayground.

Theorem ex_falso_quodlibet : ∀ (P : Prop), False → P.
Proof.
  intros P contra.
  destruct contra.
Qed.

Theorem not_implies_our_not : ∀ (P : Prop),
  ¬P → (∀ (Q : Prop), P → Q).
Proof.
  intros P contra.
  intros.
  destruct contra. assumption.
Qed.

Theorem zero_not_one : 0 ≠ 1.
Proof.
  unfold not.
  intros contra. discriminate contra.
Qed.

Theorem not_False : ¬False.
Proof.
  unfold not.
  intros.
  destruct H.
Qed.

Theorem contradiction_implies_anything: forall P Q : Prop,
  (P /\ ¬P) -> Q.
Proof.
  intros P Q [HP HNP].
  unfold not in HNP.
  apply HNP in HP.
  destruct HP.
Qed.

Theorem double_neg : forall P : Prop,
  P -> ¬¬P.
Proof.
  intros P H.
  unfold not.
  intros HF.
  apply HF in H.
  destruct H.
Qed.

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (¬Q -> ¬P).
Proof.
  intros. unfold not.
  intros.
  apply H0.
  apply H.
  exact H1.
Qed.

Theorem not_both_true_and_false : forall P : Prop, ¬ (P /\ ¬P).
Proof.
  intros P. intro contra. destruct contra.
  unfold not in H0.
  apply H0 in H.
  apply H.
Qed.

Theorem de_morgan_not_or : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q.
Proof.
  intros. unfold not in H.
  split.
  - intro contra.
    apply H.
    left. assumption.
  - intro contra.
    apply H.
    right. assumption.
Qed.

Theorem not_true_is_false : ∀ b : bool,
  b ≠ true → b = false.
Proof.
  intros b H.
  destruct b eqn:bEq.
  - exfalso.
    unfold not in H.
    apply H. reflexivity.
  - reflexivity.
Qed.

Definition disc_fn (n : nat) : Prop :=
  match n with
  | O => True
  | S _ => False
  end.

Theorem disc_example : ∀ n, ¬(O = S n).
Proof.
  intros n H1.
  assert (H2 : disc_fn O).
  { simpl. apply I. }
  rewrite H1 in H2.
  simpl in H2. apply H2.
Qed.

Module IffPlayground.
  Definition iff (P Q : Prop) := (P → Q) ∧ (Q → P).
  Notation "P <-> Q" := (iff P Q) (at level 95, no associativity) : type_scope.
End IffPlayground.

Theorem iff_sym : forall P Q : Prop, (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [PQ QP].
  split.
  - apply QP.
  - apply PQ.
Qed.

Lemma not_true_iff_false : forall b : bool, b ≠ true <-> b = false.
Proof.
  intros b.
  split.
  - apply not_true_is_false.
  - intros. rewrite H. intros contra. discriminate contra.
Qed.

Lemma apply_iff_example1 : forall P Q R : Prop,
  (P <-> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R HPQ H HP.
  apply H.
  apply HPQ. apply HP.
Qed.

Lemma apply_iff_example2 : forall P Q R : Prop,
  (P ↔ Q) → (P → R) → (Q → R).
Proof.
  intros. apply H0. apply H. apply H1.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  - intros.
    destruct H.
    + split.
      * left. assumption.
      * left. assumption.
    + destruct H. split.
      * right. apply H.
      * right. apply H0.
  - intros Both_Ors.
    destruct Both_Ors as [P_or_Q P_or_R].
    destruct P_or_Q as [HP | HQ] eqn:P_or_Q_eq.
    + left. assumption.
    + destruct P_or_R as [HP | HR] eqn:P_or_R_eq.
      * left. assumption.
      * right. split; assumption.
Qed.

