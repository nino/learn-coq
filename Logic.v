Require Import Nat.
Require Import PeanoNat.

Require Import List.
Import ListNotations.

Definition plus_claim : Prop := 2 + 2 = 4.

Theorem plus_claim_is_true : plus_claim.
Proof. reflexivity. Qed.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof. split; reflexivity. Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
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

Lemma zero_or_succ : forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [| n' ].
  - left. reflexivity.
  - right. reflexivity.
Qed.

Lemma mult_is_O : forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros [|n] [|m] H.
  - left. reflexivity.
  - left. reflexivity.
  - right. reflexivity.
  - discriminate H.
Qed.

Theorem or_commut : forall P Q : Prop, P \/ Q -> Q \/ P.
Proof.
  intros P Q [HP | HQ].
  - right. assumption.
  - left. assumption.
Qed.

Module NotPlayground.

  Definition not (P : Prop) : Prop := P -> False.
  Notation "~ x" := (not x) : type_scope.

  Check not : Prop -> Prop.

End NotPlayground.

Theorem ex_falso_quodlibet : forall (P : Prop), False -> P.
Proof.
  intros P contra.
  destruct contra.
Qed.

Theorem not_implies_our_not : forall (P : Prop),
  ~P -> (forall (Q : Prop), P -> Q).
Proof.
  intros P contra.
  intros.
  destruct contra. assumption.
Qed.

Theorem zero_not_one : 0 <> 1.
Proof.
  unfold not.
  intros contra. discriminate contra.
Qed.

Theorem not_False : ~False.
Proof.
  unfold not.
  intros.
  destruct H.
Qed.

Theorem contradiction_implies_anything: forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q [HP HNP].
  unfold not in HNP.
  apply HNP in HP.
  destruct HP.
Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P H.
  unfold not.
  intros HF.
  apply HF in H.
  destruct H.
Qed.

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros. unfold not.
  intros.
  apply H0.
  apply H.
  exact H1.
Qed.

Theorem not_both_true_and_false : forall P : Prop, ~ (P /\ ~P).
Proof.
  intros P. intro contra. destruct contra.
  unfold not in H0.
  apply H0 in H.
  apply H.
Qed.

Theorem de_morgan_not_or : forall (P Q : Prop), ~ (P \/ Q) -> ~P /\ ~Q.
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

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
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

Theorem disc_example : forall n, ~(O = S n).
Proof.
  intros n H1.
  assert (H2 : disc_fn O).
  { simpl. apply I. }
  rewrite H1 in H2.
  simpl in H2. apply H2.
Qed.

Module IffPlayground.
  Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).
  Notation "P <-> Q" := (iff P Q) (at level 95, no associativity) : type_scope.
End IffPlayground.

Theorem iff_sym : forall P Q : Prop, (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [PQ QP].
  split.
  - apply QP.
  - apply PQ.
Qed.

Lemma not_true_iff_false : forall b : bool, b <> true <-> b = false.
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
  (P <-> Q) -> (P -> R) -> (Q -> R).
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

From Coq Require Import Setoids.Setoid.

Lemma mul_eq_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  intros.
  split.
  - apply mult_is_O.
  - apply factor_is_0.
Qed.

Theorem or_assoc : forall P Q R : Prop,
  P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  split.
  - intros. destruct H as [HP | [HQ | HR]].
    * left. left. assumption.
    * left. right. assumption.
    * right. assumption.
  - intros. destruct H as [[H | H] | H].
    * left. assumption.
    * right. left. assumption.
    * right. right. assumption.
Qed.

Lemma mul_eq_0_ternary : forall n m p,
  n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mul_eq_0.
  rewrite mul_eq_0.
  rewrite or_assoc.
  reflexivity.
Qed.

(* Existential quantification *)

Definition Even x := exists n : nat, x = double n.

Lemma four_is_even : Even 4.
Proof.
  unfold Even. exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) -> (exists o, n = 2 + o).
Proof.
  intros n [m Hm].
  exists (2 + m).
  apply Hm.
Qed.

Theorem dist_not_exists : forall (X : Type) (P : X -> Prop),
  (forall x : X, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P Hx.
  unfold not. intro contra.
  destruct contra as [x' Hx'].
  apply Hx' in Hx.
  apply Hx.
Qed.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q. split.
  - intros [x1 H_or].
    destruct H_or.
    * left. exists x1. apply H.
    * right. exists x1. apply H.
  - intros [[xp HP] | [xq HQ]].
    * exists xp. left. assumption.
    * exists xq. right. assumption.
Qed.

Theorem leb_plus_exists : forall n m : nat,
  n <=? m = true -> exists x, m = n + x.
Proof.
  intros n m n_le_m.
  exists (m - n).
  induction m as [| m' IHm].
  - simpl. destruct n.
    * reflexivity.
    * unfold leb in n_le_m. discriminate n_le_m.
  - simpl.
    destruct n as [| n'].
    * reflexivity.
    * simpl in n_le_m.
Admitted.

(* Programming with propositions *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_1_auto : In 4 [1; 2; 3; 4; 5].
Proof.
  simpl. auto.
Qed.

Example In_example_2 : forall n, In n [2; 4] -> exists n', n = 2 * n'.
Proof.
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.

Theorem In_map : forall (A B : Type) (f : A -> B) (l : list A) (x : A),
  In x l -> In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [| x' l' IHl].
  - simpl. intro contra. apply contra.
  - simpl. intros [Hxx | Hin].
    * left. rewrite Hxx. reflexivity.
    * right. apply IHl. apply Hin.
Qed.

Theorem In_map_iff : forall (A B : Type) (f : A -> B) (l : list A) (y : B),
  In y (map f l) <-> exists x, f x = y /\ In x l.
Proof.
  intros A B f l y.
  induction l as [| x' l' IHl].
  - simpl. split.
    + intros contra. exfalso. apply contra.
    + intros [x Hx]. destruct Hx. apply H0.
  - split.
    + simpl.
      intros [ Hh | Ht ].
      * exists x'. split.
        -- assumption.
        -- left. reflexivity.
      * rewrite IHl in Ht.
        destruct Ht as [x Hx].
        exists x.
        destruct Hx.
        split.
        --  apply H.
        --  right. apply H0.
    + simpl. rewrite IHl.
      intros [x Hx]. destruct Hx as [Hfxy [Hxx | Hin]].
      * rewrite <- Hxx in Hfxy.
        left. apply Hfxy.
      * right. exists x. split.
        -- apply Hfxy.
        -- apply Hin.
Qed.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | h :: t => P h /\ All P t
  end.

Theorem All_In : forall T (P : T -> Prop) (l : list T),
  (forall x, In x l -> P x) <-> All P l.
Proof.
  intros T P l.
  induction l as [| hd tl IHl].
  - (* Induction start *)
    simpl. split.
    + intros. apply I.
    + intros HTrue.
      intros x.
      intros contra. exfalso. apply contra.
  - (* Induction step *)
    split.
    + (* (In x l -> Px) -> All P l *)
      intros.
      simpl.
      split.
      * apply H.
        simpl. left. reflexivity.
      * apply IHl.
        simpl in H.
        intros x Hin.
        apply H.
        right.
        apply Hin.
    + (*  All P l -> (In x l -> Px) *)
      simpl. intros [HPh Hall] x.
      intros [Heq | Hin].
      * rewrite <- Heq. apply HPh.
      * apply IHl; assumption.
Qed.

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun n => if even n then Peven n else Podd n.

Lemma even_not_odd : forall n : nat,
  even n = negb (odd n).
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - replace (S n') with (1 + n').
    2: { simpl. reflexivity. }
    destruct (even n') eqn:eqEven.
    + rewrite Nat.even_spec in eqEven.
      unfold Nat.Even in eqEven.
      destruct eqEven as [half Hhalf].
Abort.

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
  (odd n = true -> Podd n) ->
  (odd n = false -> Peven n) ->
  combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n Hodd Heven.
  destruct (odd n) eqn:nOddEq.
  - unfold combine_odd_even.
Admitted.
(* Let's get back to this some other time *)

(* Applying theorems to arguments *)
Set Printing Parentheses.

Lemma add_comm3 : forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite Nat.add_comm.
  rewrite (Nat.add_comm y z).
  rewrite (Nat.add_comm (z + y) x).
  reflexivity.
Qed.

Theorem in_not_nil : forall A (x : A) (l : list A),
  In x l -> l <> [].
Proof.
  intros A x l H Hempty.
  destruct l as [| hd tl ].
  - simpl in H. apply H.
  - discriminate Hempty.
Qed.

Theorem in_not_nil_42 : forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

Theorem in_not_nil_42_take2 : forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  assumption.
Qed.

