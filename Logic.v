Require Import Unicode.Utf8.

Definition plus_claim : Prop := 2 + 2 = 4.

Theorem plus_claim_is_true : plus_claim.
Proof. reflexivity. Qed.

Example and_example : 3 + 4 = 7 ∧ 2 * 2 = 4.
Proof. split; reflexivity. Qed.
