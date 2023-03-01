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
