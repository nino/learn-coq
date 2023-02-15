Require Import Unicode.Utf8.

Theorem mul_0_r : ∀ n:nat,
  n * 0 = 0.
Proof.
  intros.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. assumption.
Qed.

Theorem plus_n_Sm : ∀ n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite IHn'. reflexivity.
Qed.

Lemma n_plus_0_r : ∀ n : nat, n + 0 = n.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.



Theorem add_comm : ∀ n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl.
    rewrite n_plus_0_r.
    reflexivity.
  - simpl.
    rewrite IHn'.
    rewrite plus_n_Sm.
    reflexivity.
Qed.

Lemma n_plus_0_l : ∀ n : nat, 0 + n = n.
Proof. intros. rewrite add_comm. rewrite n_plus_0_r. reflexivity. Qed.

Theorem add_assoc : ∀ n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - rewrite n_plus_0_l.
    rewrite n_plus_0_l.
    reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Require Import Arith.

Lemma example_proof : ∀ x y : nat,  (x + y) *(x + y)= x * x + 2 * x * y + y * y.
Proof.
  intros x y.
  ring_simplify.
  reflexivity.
Qed.

Lemma not_not : ∀ a b : bool, negb a = negb b → a = b.
Proof.
  intros.
  destruct a.
  - unfold negb in H.
    destruct b.
    + reflexivity.
    + discriminate.
  - destruct b.
    + discriminate.
    + reflexivity.
Qed.


Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : ∀ n, double n = n + n.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl.
    rewrite <- plus_n_Sm.
    rewrite IHn'.
    reflexivity.
Qed.

Theorem eqb_refl : ∀ n : nat,
  (n =? n) = true.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. assumption.
Qed.

Definition even := Nat.even.

Lemma cancel_negb : ∀ a b : bool, negb a = negb b -> a = b.
Proof.
  intros a b H.
  destruct a as [].
  - destruct b as [].
    + reflexivity.
    + discriminate.
  - destruct b as [].
    + discriminate.
    + reflexivity.
Qed.

Theorem even_S : ∀ n : nat,
  even (S n) = negb (even n).
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - rewrite IHn'.
    rewrite Bool.negb_involutive.
    simpl. reflexivity.
Qed.

(* Exercise "destruct induction"

  `destruct` works for inductive types where you don't need to do induction. Eg
   if there is only a finite number of possible values, you can use destruct.

 *)

(* Not doing informal proofs here, I know how they work. *)

(* More exercises *)

Theorem add_shuffle3 : ∀ n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros.
  assert (Flip_m: m + (n + p) = (n + p) + m).
  { rewrite Nat.add_comm. reflexivity. }
  rewrite Flip_m.
  assert (use_assoc: n + p + m = n + (p + m)).
  { rewrite Nat.add_assoc. reflexivity. }
  rewrite use_assoc.
  assert (flip_mp: m + p = p + m).
  { rewrite Nat.add_comm. reflexivity. }
  rewrite flip_mp. reflexivity.
Qed.

Section NatToBinAndBackToNat.

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B1 Z
  | B0 rest => B1 rest
  | B1 rest => B0 (incr rest)
  end.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => 0
  | B1 rest => 1 + 2 * (bin_to_nat rest)
  | B0 rest => 2 * (bin_to_nat rest)
  end.

Lemma S_is_plus_1_l : ∀ n, S n = 1 + n.
Proof. intros. easy. Qed.

Theorem bin_to_nat_pres_incr : ∀ b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  intros b.
  induction b as [| b1 IH1 | b2 IH2].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite IH2.
    assert (1 + bin_to_nat b2 + (1 + bin_to_nat b2 + 0) =
      1 + bin_to_nat b2 + 1 + (bin_to_nat b2 + 0)
    ).
    { simpl.
      assert (bin_to_nat b2 + 1 = S (bin_to_nat b2)).
      { rewrite Nat.add_comm. simpl. reflexivity. }
      rewrite H.
      rewrite Nat.add_0_r. simpl.
      assert (bin_to_nat b2 + S(bin_to_nat b2) = S(bin_to_nat b2 + bin_to_nat b2)).
      { rewrite Nat.add_comm. rewrite Nat.add_succ_l. reflexivity. }
      rewrite Nat.add_succ_r. reflexivity.
    }
    simpl.
    rewrite Nat.add_0_r.
    rewrite Nat.add_succ_r.
    reflexivity.
    (* I'm sure this could have been done waaaaaaaaay easier. *)
Qed.

Fixpoint nat_to_bin (n:nat) : bin :=
  match n with
  | O => Z
  | S n' => incr (nat_to_bin n')
  end.

Theorem nat_bin_nat : ∀ n, bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - replace (nat_to_bin (S n')) with (incr (nat_to_bin n')).
    2 : { unfold nat_to_bin. reflexivity. }
    rewrite bin_to_nat_pres_incr.
    rewrite IHn'. reflexivity.
Qed.

Theorem bin_nat_bin_fails : ∀ b, nat_to_bin (bin_to_nat b) = b.
Abort. (* This fails because there are two ways of expressing zero in bin *)

Lemma double_incr : ∀ n : nat, double (S n) = S (S (double n)).
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - unfold double. reflexivity.
Qed.

Definition double_bin (b:bin) : bin :=
  nat_to_bin (double (bin_to_nat b)).

Example double_bin_zero : double_bin Z = Z.
Proof.
  reflexivity.
Qed.

Lemma double_incr_bin : ∀ b,
    double_bin (incr b) = incr (incr (double_bin b)).
Proof.
  intros b.
  induction b as [| b1 IH1 | b2 IH2].
  - reflexivity.
  - simpl.
    unfold double_bin.
    replace (incr (incr (nat_to_bin (double (bin_to_nat (B0 b1))))))
    with (nat_to_bin (S (S (double (bin_to_nat (B0 b1)))))).
    (* 2 : { *)
    (*   rewrite bin_to_nat_pres_incr. *)
Admitted.


End NatToBinAndBackToNat.
