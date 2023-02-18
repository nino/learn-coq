Require Import List.
Require Import Unicode.Utf8.
Require Import Nat.
Require Import PeanoNat.
Require Import Bool.
From Learn Require Import Utils.

Section Definitions.

  (* Let's try this again *)
  Definition bag := list nat.

  Fixpoint count (n : nat) (b : bag) : nat :=
    match b with
    | nil => 0
    | h :: t => (if n =? h then 1 else 0) + count n t
    end.

  Definition member (n : nat) (b : bag) : bool := 0 <? (count n b).
  Definition sum : bag → bag → bag := @app nat.
  Definition add (n : nat) (b : bag) : bag := n :: b.

  Fixpoint remove_one (n : nat) (b : bag) : bag :=
    match b with
    | nil => nil
    | h :: t => if h =? n then t else h :: (remove_one n t)
    end.

  Fixpoint remove_all (n : nat) (b : bag) : bag :=
    match b with
    | nil => nil
    | h :: t => if h =? n then (remove_all n t) else h :: (remove_all n t)
    end.

  Fixpoint included (b1 b2 : bag) : bool :=
    match b1, b2 with
    | nil, _ => true
    | _, nil => false
    | h :: t, _ => (member h b2) && (included t (remove_one h b2))
    end.

End Definitions.

Section Facts.
  Print Nat.eq_refl.

  Theorem add_inc_count: ∀ (n : nat) (b : bag),
    count n (add n b) = S (count n b).
  Proof.
    intros.
    simpl.
    replace (n =? n) with true.
    2: { rewrite eqb_with_self_if_true. reflexivity. }
    reflexivity.
  Qed.

  Lemma rev_cons: ∀ (n : nat) (l : list nat),
    rev (n :: l) = (rev l) ++ (cons n nil).
  Proof. intros. reflexivity. Qed.

  Theorem count_member_nonzero : ∀ (n : nat) (b : bag),
    1 <=? (count n (add n b)) = true.
  Proof.
    intros. simpl.
    rewrite eqb_with_self_if_true.
    simpl. reflexivity.
  Qed.

  Lemma actual_member_count_nonzero: ∀ (s : bag) (n : nat),
    member n s = true → Nat.leb 1 (count n s) = true.
  Proof.
    intros.
    simpl.
    unfold member in H.
    destruct (count n s).
    - discriminate H.
    - reflexivity.
  Qed.

  Theorem remove_does_not_increase_count: ∀ (b : bag) (n : nat),
    (count n (remove_one n b)) <=? (count n b) = true.
  Proof.
    intros.
    induction b as [| h t IH].
    - simpl. reflexivity.
    - simpl. rewrite Nat.eqb_sym.
      destruct (n =? h) eqn:n_eq_h.
      + simpl. rewrite Nat.leb_le. auto.
      + simpl. rewrite n_eq_h. simpl.
        rewrite Nat.leb_le.
        rewrite <- Nat.leb_le.
        assumption.
  Qed.

  Theorem bag_count_sum: forall (b1 b2 : bag) (n : nat),
    count n (sum b1 b2) =? (count n b1) + (count n b2) = true.
  Proof.
    intros b1 b2 n.
    induction b1 as [| h1 t1 IH1].
    - simpl. rewrite Nat.eqb_eq. reflexivity.
    - simpl.
      destruct (n =? h1); simpl; assumption.
  Qed.

End Facts.
