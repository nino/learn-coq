Require Import Arith.PeanoNat.
Require Import Nat.
Require Import Lia.
Require Import List.
Import ListNotations.

Section CollatzConjecture.

  Fixpoint div2 (n : nat) :=
    match n with
    | 0 => 0
    | 1 => 0
    | S (S n) => S (div2 n)
    end.

  Definition f (n : nat) :=
    if even n then div2 n
    else (3 * n) + 1.

  Inductive reaches_1 : nat -> Prop :=
    | term_done : reaches_1 1
    | term_more (n : nat) : reaches_1 (f n) -> reaches_1 n.

  Conjecture collatz : forall n, reaches_1 n.

  Fail
  Fixpoint reaches_1_in (n : nat) :=
    if n =? 1 then 0
    else 1 + reaches_1_in (f n).
  (* So if it still fails, why did we add the conjecture? *)

End CollatzConjecture.

Module LePlayground. (* hehe *)

  Inductive le : nat -> nat -> Prop :=
    | le_n (n : nat) : le n n
    | le_S (n m : nat) : le n m -> le n (S m).

End LePlayground.

Inductive clos_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | t_step (x y : X) :
      R x y -> clos_trans R x y
  | t_trans (x y z : X) :
      clos_trans R x y ->
      clos_trans R y z ->
      clos_trans R x z.

Inductive clos_refl_trans {X : Type} (R: X->X->Prop) : X->X->Prop :=
  | tr_step (x y : X) :
      R x y -> clos_refl_trans R x y
  | tr_trans (x y z : X) :
      clos_refl_trans R x y ->
      clos_refl_trans R y z ->
      clos_refl_trans R x z
  | tr_refl (x y : X) :
      clos_refl_trans R x y ->
      clos_refl_trans R y x.

Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) :
      Perm3 [a; b; c] [b; a; c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a; b; c] [a; c; b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.

(*
   Exercise 1: perm
   Perm3 [1; 2; 3] [3; 2; 1] is True, because
   Perm3 [1; 2; 3] [1; 3; 2] is True, and
   Perm3 [1; 3; 2] [3; 1; 2] is True, and
   Perm3 [3; 1; 2] [3; 2; 1] is True, and
   transitivity.

   And Perm3 [1; 2; 3] [1; 2; 3] is True because you can swap 12 twice and then transitivity.
 *)

(* Another evenness *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

(* From Induction.v *)
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Theorem ev_double : forall n, ev (double n).
Proof.
  intros n.
  induction n.
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IHn.
Qed.

Theorem ev_inversion : forall (n : nat),
  ev n -> (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E. destruct E as [| n' E'] eqn:EE.
  - left. reflexivity.
  - right. exists n'.
    split.
    + reflexivity.
    + apply E'.
Qed.

Theorem evSS_ev : forall (n : nat), ev (S (S n)) -> ev n.
Proof.
  intros n H.
  apply ev_inversion in H.
  destruct H as [H0 | H1].
  - discriminate H0.
  - destruct H1 as [n' [HSS Hev]].
    injection HSS as Hnn.
    rewrite <- Hnn in Hev.
    apply Hev.
Qed.

Theorem evSS_ev' : forall (n : nat), ev (S (S n)) -> ev n.
Proof.
  intros n ESS.
  inversion ESS as [| n' E' Heq].
  apply E'.
Qed.


Theorem one_not_even : ~ ev 1.
Proof.
  intros H.
  inversion H.
Qed.

Theorem just_trying_stuff_outside_the_book : ~ forall n : nat, n < 2.
Proof.
  intros contra.
  pose (Hn := contra 2).
  inversion Hn.
  rewrite <- PeanoNat.Nat.leb_le in H0.
  discriminate H0.
Qed.

Theorem SSSSev__even : forall n : nat, ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H.
  inversion H.
  inversion H1.
  apply H3.
Qed.

Theorem ev5_nonsense : ev 5 -> 2 + 2 = 9.
Proof.
  intros H5.
  inversion H5.
  inversion H0.
  inversion H2.
Qed.

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] -> [n] = [m].
Proof.
  intros n m o H.
  inversion H.
  reflexivity.
Qed.

Theorem inversion_ex2 : forall n : nat, S n = 0 -> 2 + 2 = 5.
Proof.
  intros. inversion H.
Qed.

(* Recall that, *)
Definition Even x := exists n : nat, x = double n.

Lemma ev_Even_firsttry : forall n : nat, ev n -> Even n.
Proof.
  unfold Even.
  intros n E.
  inversion E as [EQ' | n' E' EQ'].
  - exists 0. reflexivity.
Abort.

Lemma ev_Even : forall n : nat,
  ev n -> Even n.
Proof.
  intros n E.
  induction E as [| n' E' IH].
  - unfold Even. exists 0. reflexivity.
  - unfold Even in IH.
    destruct IH as [k Hk].
    rewrite Hk.
    unfold Even.
    exists (S k).
    simpl.
    reflexivity.
Qed.

Theorem ev_Even_iff : forall n : nat, ev n <-> Even n.
Proof.
  intros n. split.
  - apply ev_Even.
  - unfold Even.
    intros [k Hk].
    rewrite Hk.
    apply ev_double.
Qed.

Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m Hn Hm.
  induction Hn as [| n' En IHn].
  - simpl. apply Hm.
  - simpl. apply ev_SS. apply IHn.
Qed.

Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  split.
  - intros Hev'.
    induction Hev' as [ | | n' m' Hn' Hm' Hev' IH].
    + apply ev_0.
    + apply (ev_SS 0 ev_0).
    + apply (ev_sum n' m' Hm' IH).
      (* I might have fucked up some of those names in the induction *)
  - intros Hev.
    induction Hev as [ | n' Hn' IH].
    + apply ev'_0.
    + replace (S (S n')) with (2 + n') by reflexivity.
      apply (ev'_sum 2 n' ev'_2 IH).
Qed.

Theorem ev_ev__ev : forall n m, ev (n + m) -> ev n -> ev m.
Proof.
  intros n m Hsum Hn.
  induction Hn as [| n' Hn' IH].
  - simpl in Hsum. assumption.
  - apply IH.
    simpl in Hsum.
    inversion Hsum.
    assumption.
Qed.

Lemma double_is_n_plus_n : forall n : nat,
  n + n = double n.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite PeanoNat.Nat.add_comm. simpl.
    rewrite IHn. reflexivity.
Qed.

Theorem ev_plus_plus : forall n m p : nat,
  ev (n + m) -> ev (n + p) -> ev (m + p).
Proof.
  (* Do this without induction or case analysis, with some tedious
   * rewriting and clever assertions. Hint: Is (n + m) + (n + p) even? *)
  intros n m p Hnm Hnp.
  assert (Hdouble: ev (double n)) by apply ev_double.
  assert (Hnplusn: n + n = double n) by apply (double_is_n_plus_n).
  (* I guess technically we did use induction in that one?? *)
  rewrite <- Hnplusn in Hdouble.
  assert (Hsum: ev ((n + m) + (n + p))) by apply (ev_sum (n + m) (n + p) Hnm Hnp).
  replace ((n + m) + (n + p)) with ((n + n) + (m + p)) in Hsum.
  2: {
    rewrite <- (PeanoNat.Nat.add_assoc n m (n + p)).
    rewrite -> (PeanoNat.Nat.add_assoc m n p).
    rewrite (PeanoNat.Nat.add_comm m n).
    rewrite <- (PeanoNat.Nat.add_assoc n m p).
    rewrite -> (PeanoNat.Nat.add_assoc n n (m + p)).
    reflexivity.
  }
  apply (ev_ev__ev (n + n) (m + p)) in Hsum; assumption.
Qed.

Module Playground.

  Inductive le : nat -> nat -> Prop :=
    | le_n (n : nat) : le n n
    | le_S (n m : nat) (H : le n m) : le n (S m).

  Notation "n <= m" := (le n m).

  Theorem test_le1 : 3 <= 3.
  Proof. apply le_n. Qed.

  Theorem test_le2 : 3 <= 6.
  Proof.
    apply le_S.
    apply le_S.
    apply le_S.
    apply le_n.
  Qed.

  Theorem test_le3 : (2 <= 1) -> 2 + 2 = 5.
  Proof.
    intros H.
    inversion H.
    inversion H2.
  Qed.

  Definition lt (n m : nat) := le (S n) m.
  Notation "m < n" := (lt m n).

End Playground.

Inductive total_relation : nat -> nat -> Prop :=
  | any_nats (n m : nat) : total_relation n m.

Theorem total_relation_is_total : forall n m : nat, total_relation n m.
Proof. apply any_nats. Qed.

Inductive empty_relation : nat -> nat -> Prop :=.

Theorem empty_relation_is_empty : forall n m : nat, ~ empty_relation n m.
Proof.
  intros. intro contra. inversion contra.
Qed.

Lemma Sn_le_m_then_n_le_m : forall n m : nat, S n <= m -> n <= m.
Proof.
  intros.
  induction H.
  - apply le_S. apply le_n.
  - apply le_S.
    apply IHle.
Qed.

Lemma le_trans : forall m n o : nat, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o Hmn Hno.
  induction Hmn.
  - assumption.
  - apply Sn_le_m_then_n_le_m in Hno.
    apply IHHmn.
    assumption.
Qed.

Theorem O_le_n : forall n : nat, 0 <= n.
Proof.
  intros.
  induction n.
  - apply le_n.
  - apply le_S. assumption.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m : nat,
  n <= m -> S n <= S m.
Proof.
  intros.
  induction H.
  - apply le_n.
  - apply le_S. assumption.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m : nat,
  S n <= S m -> n <= m.
Proof.
  intros.
  inversion H.
  - apply le_n.
  - apply Sn_le_m_then_n_le_m in H1.
    assumption.
Qed.

Theorem lt_ge_cases : forall n m : nat,
  n < m \/ n >= m.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - destruct m as [| m'].
    + right. apply le_n.
    + left. apply n_le_m__Sn_le_Sm. apply O_le_n.
  - destruct IHn'.
    + destruct H as [| m' Hm].
      * right. apply le_n.
      * left. apply n_le_m__Sn_le_Sm. assumption.
    + right. apply le_S.
      assumption.
Qed.

Theorem le_gt_cases : forall n m : nat,
  n <= m \/ n > m.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - left. apply O_le_n.
  - destruct IHn' as [H | H].
    + inversion H.
      * right. apply le_n.
      * left. apply n_le_m__Sn_le_Sm. apply H0.
    + right. unfold gt in *. unfold lt in *.
      apply le_S. apply H.
Qed.


Theorem le_plus_l : forall a b : nat,
  a <= a + b.
Proof.
  induction b as [| b' IHb'].
  - rewrite PeanoNat.Nat.add_0_r. apply le_n.
  - destruct a as [ | a'].
    + simpl. apply O_le_n.
    + simpl. apply le_S.
      replace (a' + S b') with (S a' + b').
      2: {
        simpl. rewrite (PeanoNat.Nat.add_comm a' (S b')).
        simpl. rewrite (PeanoNat.Nat.add_comm a' b').
        reflexivity.
      }
      apply IHb'.
Qed.

Lemma lt_le : forall n m : nat,
  n < m -> n <= m.
Proof.
  intros n m Hlt.
  unfold lt in Hlt.
  apply Sn_le_m_then_n_le_m in Hlt. apply Hlt.
Qed.

Theorem plus_le : forall n1 n2 m : nat,
  n1 + n2 <= m ->
  n1 <= m /\ n2 <= m.
Proof.
  intros n1 n2 m H.
  split.
  - induction n2.
    + rewrite PeanoNat.Nat.add_0_r in H. apply H.
    + rewrite PeanoNat.Nat.add_comm in H. simpl in H.
      rewrite PeanoNat.Nat.add_comm in H.
      apply Sn_le_m_then_n_le_m in H.
      apply IHn2 in H. apply H.
  - induction n1.
    + rewrite PeanoNat.Nat.add_0_l in H. apply H.
    + simpl in H.
      apply Sn_le_m_then_n_le_m in H.
      apply IHn1 in H. apply H.
Qed.

Lemma le_plus_on_both_sides : forall n m k : nat,
  n <= m -> n + k <= m + k.
Proof.
  intros n m k H.
  induction k as [| k' IHk].
  - rewrite PeanoNat.Nat.add_0_r.
    rewrite (PeanoNat.Nat.add_0_r m).
    apply H.
  - rewrite (PeanoNat.Nat.add_comm n).
    rewrite (PeanoNat.Nat.add_comm m).
    simpl.
    rewrite (PeanoNat.Nat.add_comm k').
    rewrite (PeanoNat.Nat.add_comm k').
    apply n_le_m__Sn_le_Sm. apply IHk.
Qed.

Lemma replace_left_with_smaller_addend : forall n n' m p : nat,
  n' <= n -> n + m <= p -> n' + m <= p.
Proof.
  intros n n' m p Hnn H.
  induction n'.
  - simpl. apply plus_le in H. destruct H as [Hn Hm]. apply Hm.
  - apply (le_plus_on_both_sides (S n') n m) in Hnn.
    Check le_trans.
    apply (le_trans (S n' + m) (n + m) p Hnn H).
Qed.

Lemma le_cancel_plus : forall k p q : nat,
  k + p <= k + q -> p <= q.
Proof.
  intros k p q H.
  induction k.
  - simpl in H. apply H.
  - simpl in H. apply Sn_le_Sm__n_le_m in H.
    apply IHk in H. apply H.
Qed.

Theorem add_le_cases : forall n m p q : nat,
  n + m <= p + q -> n <= p \/ m <= q.
Proof.
  intros n m p q H.
  induction n as [| n' IHn].
  - left. apply O_le_n.
  - destruct (le_gt_cases (S n') p) as [H1 | H1].
    + left. apply H1.
    + right. unfold gt in H1. apply lt_le in H1.
      apply (replace_left_with_smaller_addend (S n') p m (p + q) H1) in H.
      apply le_cancel_plus in H. apply H.
Qed.

Theorem plus_le_compat_l : forall n m p : nat,
  n <= m -> p + n <= p + m.
Proof.
  intros.
  rewrite (PeanoNat.Nat.add_comm p).
  rewrite (PeanoNat.Nat.add_comm p).
  now apply le_plus_on_both_sides.
Qed.

Theorem plus_le_compat_r : forall n m p,
  n <= m -> n + p <= m + p.
Proof.
  apply le_plus_on_both_sides.
Qed.

Theorem le_plus_trans : forall n m p : nat,
  n <= m ->
  n <= m + p.
Proof.
  intros n m p H.
  induction p.
  - rewrite (PeanoNat.Nat.add_comm m).
    simpl. apply H.
  - rewrite PeanoNat.Nat.add_comm.
    simpl.
    rewrite PeanoNat.Nat.add_comm.
    apply le_S in IHp. apply IHp.
Qed.

Theorem n_lt_m__n_le_m : forall n m : nat,
  n < m ->
  n <= m.
Proof. now apply lt_le. Qed.

Theorem plus_lt : forall n1 n2 m : nat,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  intros n1 n2 m H.
  unfold lt in *.
  split.
  - replace (S (n1 + n2)) with (S n1 + n2) in H by reflexivity.
    apply plus_le in H.
    destruct H. assumption.
  - replace (S (n1 + n2)) with (n1 + S n2) in H.
    2: {
      rewrite PeanoNat.Nat.add_comm. simpl.
      rewrite PeanoNat.Nat.add_comm. reflexivity.
    }
    apply plus_le in H.
    destruct H. assumption.
Qed.

Theorem leb_complete : forall n m : nat,
  n <=? m = true -> n <= m.
Proof.
  intros n.
  induction n as [| n IHn].
  - intro m. destruct m.
    + simpl. intros H. apply le_n.
    + simpl. intros H. apply O_le_n.
  - intro m. destruct m.
    + simpl. intros contra. discriminate.
    + simpl. intro Hnm.
      apply (IHn m) in Hnm.
      now apply n_le_m__Sn_le_Sm.
Qed.

Lemma n_leb_n : forall n : nat, (n <=? n) = true.
Proof.
  induction n.
  - reflexivity.
  - now simpl.
Qed.

Theorem leb_correct : forall n m : nat,
  n <= m ->
  n <=? m = true.
Proof.
  intros n m H.
  induction m as [| m' IHm'].
  (* Why can I not figure this out?? *)
Admitted.

Theorem leb_iff : forall n m : nat,
  n <=? m = true <-> n <= m.
Proof.
  split.
  - apply leb_complete.
  - apply leb_correct.
Qed.

Theorem leb_true_trans : forall n m o : nat,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  intros.
  apply leb_complete in H.
  apply leb_complete in H0.
  apply leb_correct.
  apply (le_trans n m o H H0).
Qed.

Module R.

  (* I guess this is a 3-way relation *)
  Inductive R : nat -> nat -> nat -> Prop :=
    | c1 : R 0 0 0
    | c2 m n o (H : R m n o) : R (S m) n (S o)
    | c3 m n o (H : R m n o) : R m (S n) (S o)
    | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
    | c5 m n o (H : R m n o) : R n m o.

  Example R112 : R 1 1 2.
  Proof.
    repeat constructor.
  Qed.

  (* If we dropped constructor c5 from the definition of R, would the set
   * of provable propositions change? Briefly (1 sentence) explain your
   * answer. *)
  (* I don't think so. *)

  (* If we dropped constructor c4 from the definition of R, would the
   * set of provable propositions change? Briefly (1 sentence)
   * explain your answer. *)
  (* I don't think so. You can derive this one from 2 and 3 *)

  (* The relation R above actually encodes a familiar function. Figure out which function; then state and prove this equivalence in Coq. *)
  (* Is R a b c true if a + b = c? *)

  Definition fR : nat -> nat -> nat := add.

  Theorem R_equiv_fR : forall a b c, R a b c <-> fR a b = c.
  Proof.
    unfold fR.
    intros a b c.
    split; intros H.
    - induction H.
      + reflexivity.
      + simpl. f_equal. apply IHR.
      + rewrite Nat.add_comm. simpl. rewrite Nat.add_comm. f_equal. apply IHR.
      + simpl in IHR.
        rewrite Nat.add_comm in IHR.
        simpl in IHR. rewrite Nat.add_comm in IHR.
        (* This is dumb but it works: *)
        inversion IHR. rewrite Nat.add_comm. reflexivity.
      + now rewrite Nat.add_comm.
    - destruct H. (* Not sure how this step worked, but it did?? *)
      induction a; destruct b.
      + constructor.
      + constructor. induction b; try constructor.
        apply IHb.
      + rewrite Nat.add_0_r in *.
        constructor. apply IHa.
      + simpl. constructor. apply IHa.
  Qed.
  (* Not sure why I had to / did do `destruct b` and then `induction b` *)

End R.

Inductive subseq : list nat -> list nat -> Prop :=
  | nil_subseq (l : list nat) : subseq [] l
  | hd_match (l1 l2 : list nat) (hd : nat) (H: subseq l1 l2) :
      subseq (hd :: l1) (hd :: l2)
  | hd_mismatch (l1 l2 : list nat) (hd : nat) (H: subseq l1 l2) :
      subseq l1 (hd :: l2).

Infix "<@" := subseq (at level 80).

Theorem subseq_refl : forall l : list nat,
  subseq l l.
Proof.
  intros l.
  induction l as [| hd tl IH].
  - apply nil_subseq.
  - apply hd_match. apply IH.
Qed.

Set Printing Parentheses.

Theorem subseq_app : forall l1 l2 l3 : list nat,
  l1 <@ l2 -> l1 <@ (l2 ++ l3).
Proof.
  intros l1 l2 l3 H.
  induction H as [ l2 | l1 l2 hd H IH | l1 l2 hd H IH].
  - apply nil_subseq.
  - simpl. apply hd_match. apply IH.
  - simpl. apply hd_mismatch. apply IH.
Qed.

Theorem subseq_trans : forall A B C : list nat,
  A <@ B -> B <@ C ->
  A <@ C.
Proof.
  intros A B C.
  generalize dependent B.
  generalize dependent A.
  induction C as [| hd tl IHC ].
  - (* C = [] *) intros A B H_AB H_BC.
    (* since H_BC : B <@ [], we can do *)
    inversion H_BC.
    (* and now H: B = [] *)
    rewrite <- H in H_AB (* so now H_AB: A <@ [] *).
    inversion H_AB.
    apply nil_subseq.
  - (* C = hd :: tl *) intros A B H_AB H_BC.
    inversion H_BC as [ | B' C' hd' H_BC' HB' HC' | B' C' hd' H_BC' HB' HC' ].
    + (* nil_subseq *) rewrite <- H in H_AB. inversion H_AB. apply nil_subseq.
    + (* hd_match *)
      (* Tidy: *)
      rewrite -> HC' in * (* since hd' = hd, use hd everywhere *).
      clear HC' (* hd' now unused *).
      inversion H_AB as [ | A'' B'' hd'' H_AB'' HA'' HB'' | A'' B'' hd'' H_AB'' HA'' HB'' ].
      * apply nil_subseq.
      * (* hd_match *)
        assert (Hhdsame: hd = hd'').
        { rewrite <- HB'' in HB'.
          injection HB'.
          intros. assumption. }
        rewrite <- Hhdsame in *.
        clear Hhdsame.
        (* Now all heads are hd *)
        assert (HBsame: B' = B'').
        { rewrite <- HB'' in HB'.
          injection HB'. intros. assumption. }
        rewrite <- HBsame in *. clear HBsame.
        apply hd_match.
        apply (IHC A'' B' H_AB'' H_BC').
      * (* hd_mismatch *)
        (* Tidy: *)
        clear HA''. clear A''.
        assert (Hhdsame: hd = hd'').
        { rewrite <- HB'' in HB'. injection HB'. intros. assumption. }
        rewrite <- Hhdsame in *. clear Hhdsame. clear hd''.
        assert (HBsame: B' = B'').
        { rewrite <- HB'' in HB'.
          injection HB'. intros. assumption. }
        rewrite <- HBsame in *. clear HBsame. clear B''.
        apply hd_mismatch.
        apply (IHC A B' H_AB'' H_BC').
    + (* hd_mismatch *)
      (* Tidy: *) clear HC'. clear hd'.
      apply hd_mismatch.
      apply (IHC A B H_AB H_BC').
Qed.

Module bin1.
  Inductive bin : Type :=
    | Z
    | B0 (n : bin)
    | B1 (n : bin).
End bin1.

Module bin2.
  Inductive bin : Type :=
    | Z : bin
    | B0 (n : bin) : bin
    | B1 (n : bin) : bin.
End bin2.

Module bin3.
  Inductive bin : Type :=
    | Z : bin
    | B0 : bin -> bin
    | B1 : bin -> bin.
End bin3.

Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

Reserved Notation "S =~ re" (at level 80).

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2 (H1: s1 =~ re1) (H2: s2 =~ re2)
      : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s re1 re2 (H1: s =~ re1) : s =~ (Union re1 re2)
  | MUnionR s re1 re2 (H1: s =~ re2) : s =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re (H1: s1 =~ re) (H2: s2 =~ (Star re))
      : (s1 ++ s2) =~ (Star re)

      where "s =~ re" := (exp_match s re).

Example reg_exp_ex1 : [1] =~ Char 1.
Proof. apply MChar. Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1]); apply MChar.
Qed.

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intro H.
  inversion H.
Qed.

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl.
  apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

Lemma MStar1 :
  forall T s (re : reg_exp T),
  s =~ re ->
  s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (List.app_nil_r s).
  apply (MStarApp s [] re H (MStar0 re)).
Qed.

Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  intros T s H.
  inversion H.
Qed.

Lemma MUnion' : forall (T : Type) (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros T s re1 re2 [H1 | H2].
  - now apply MUnionL.
  - now apply MUnionR.
Qed.
