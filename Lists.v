Require Import Unicode.Utf8.
Require Import List.

Notation "x =? y" := (Nat.eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (Nat.leb x y) (at level 70) : nat_scope.

Inductive natprod :=
  | pair (n1 n2 : nat).

Notation "( x , y )" := (pair x y).

Definition fst pair := match pair with
  | (x, y) => x
  end.

Definition snd pair := match pair with (x, y) => y end.

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof. reflexivity. Qed.

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros.
  destruct p.
  simpl.
  reflexivity.
Qed.

Definition swap_pair p := match p with
| (x, y) => (y, x)
end.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p /\ snd (swap_pair p) = fst p.
Proof.
  intros.
  destruct p.
  simpl.
  split; reflexivity.
Qed.

Definition natlist := list nat.

Require Import List.

Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t =>
    if negb (Nat.eqb h 0)
      then h :: (nonzeros t)
      else (nonzeros t)
 end.

Compute (nonzeros (1 :: 2 :: 0 :: 10 :: 0 :: nil)).

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. trivial. Qed.

Fixpoint filter (f : nat -> bool) (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => if f h
    then h :: (filter f t)
    else filter f t
  end.

Definition oddmembers (l:natlist) : natlist :=
  filter Nat.odd l.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof.
  reflexivity.
Qed.

Lemma oddmembers_works : forall (l : natlist),
  existsb Nat.even (oddmembers l) = false.
Proof.
  intros.
  induction l as [| hd tl IH].
  - reflexivity.
  - unfold existsb.
  (* I'll need to know more to be able to finish this. *)
  Admitted.

Fixpoint length {A: Type} (l : list A) := match l with
  | nil => 0
  | cons hd tl => S (length tl)
  end.

Definition countoddmembers (l:natlist) : nat :=
  length (oddmembers l).

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | nil, _ => l2
  | _, nil => l1
  | h1 :: t1, h2 :: t2 =>
      h1 :: h2 :: (alternate t1 t2)
  end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.

(* Bags *)

Definition bag := natlist.

Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
  | nil => 0
  | h :: t => (if Nat.eqb v h then 1 else 0) + count v t
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.

Definition sum : bag -> bag -> bag := alternate.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

Definition add (v : nat) (s : bag) : bag :=
  v :: s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.

Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

Fixpoint member (v : nat) (s : bag) : bool :=
  match s with
  | nil => false
  | h :: t => orb (Nat.eqb h v) (member v t)
  end.

Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.

Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with
  | nil => nil
  | h :: t => if Nat.eqb h v then t else h :: (remove_one v t)
  end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t =>
      if Nat.eqb h v
      then (remove_all v t)
      else h :: (remove_all v t)
  end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.

Fixpoint included (s1 : bag) (s2 : bag) : bool :=
  match s1, s2 with
  | nil, _ => true
  | _, nil => false
  | h :: t, _ =>
      if member h s2
      then included t (remove_one h s2)
      else false
  end.

Example test_included1: included [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.

Example test_included2: included [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.

Lemma eqb_is_eq : forall (n : nat), Nat.eqb n n = true.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl. assumption.
Qed.

Theorem add_inc_count : forall (n : nat) (b : bag),
  count n (add n b) = 1 + count n b.
Proof.
  intros n b.
  simpl.
  rewrite eqb_is_eq.
  simpl.
  reflexivity.
Qed.

Theorem app_nil_r : ∀ l : natlist,
  l ++ [] = l.
Proof.
  intros l.
  induction l as [| n l IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma rev_cons: forall (n:nat) (l:natlist),
  rev (n :: l) = rev l ++ [n].
Proof.
  intros.
  induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma app_assoc: forall (A : Type) (xs ys zs : list A),
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs.
Proof.
  intros.
  induction xs as [| x xt IHx ].
  - simpl. reflexivity.
  - simpl. rewrite IHx. reflexivity.
Qed.

Theorem rev_app_distr: ∀ l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2.
  induction l1 as [| n l1' IHl1'].
  - simpl.
    rewrite app_nil_r.
    reflexivity.
  - simpl. rewrite IHl1'.
    simpl. rewrite app_assoc. reflexivity.
Qed.

Theorem rev_involutive : ∀ l : natlist,
  rev (rev l) = l.
Proof.
  intros.
  induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite rev_app_distr. simpl.
    rewrite IH.
    reflexivity.
Qed.

Theorem app_assoc4 : ∀ l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros.
  rewrite app_assoc. rewrite app_assoc. reflexivity.
Qed.

Lemma nonzeros_app : ∀ l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros.
  induction l1 as [| h t IH].
  - simpl. reflexivity.
  - simpl.
    rewrite IH.
    destruct (negb (Nat.eqb h 0)).
    + simpl. reflexivity.
    + reflexivity.
Qed.

Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1, l2 with
  | nil, nil => true
  | nil, _ => false
  | _, nil => false
  | h1 :: t1, h2 :: t2 => andb (Nat.eqb h1 h2) (eqblist t1 t2)
  end.

Example test_eqblist1 :
  (eqblist nil nil = true).
Proof.
  reflexivity.
Qed.

Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.

Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Theorem eqblist_refl : ∀ l:natlist,
  true = eqblist l l.
Proof.
  intro l.
  induction l as [| h t IH].
  - reflexivity.
  - simpl. rewrite <- IH.
    rewrite eqb_is_eq.
    simpl. reflexivity.
Qed.

Theorem leb_n_Sn : ∀ n,
  Nat.leb n (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity.
Qed.

Theorem count_member_nonzero : ∀ (s : bag) (n : nat),
  Nat.leb 1 (count n (n :: s)) = true.
Proof.
  intros s n.
  simpl.
  rewrite eqb_is_eq.
  simpl. reflexivity.
Qed.

Lemma different_length_implies_not_equal: forall (A : Type) (xs ys : list A),
  Nat.eqb (length xs) (length ys) = false ->  xs <> ys.
Proof.
  intros.
  intros contra.
  apply (f_equal (@length A)) in contra.
  apply PeanoNat.Nat.eqb_eq in contra.
  rewrite H in contra. discriminate contra.
Qed.

Lemma succ_not_same: forall n, S n <> n.
Proof.
  intros.
  intros contra.
  induction n.
  - discriminate.
  - apply (f_equal pred) in contra.
    rewrite PeanoNat.Nat.pred_succ in contra.
    rewrite PeanoNat.Nat.pred_succ in contra.
    contradict IHn. assumption.
Qed.

Lemma cons_l_neq_l: forall (A : Type) (l : list A) (el : A),
  el :: l ≠ l.
Proof.
  intros.
  destruct l.
  - intros contra.
    apply (f_equal length) in contra.
    discriminate contra.
  - intros contra.
    replace (a :: l) with ([a] ++ l) in contra.
    2: { unfold app. reflexivity. }
    apply (f_equal (@List.length A)) in contra.
    simpl in contra.
    apply succ_not_same in contra.
    contradiction.
Qed.

Lemma actual_member_count_nonzero: ∀ (s : bag) (n : nat),
  member n s = true -> Nat.leb 1 (count n s) = true.
Proof.
  intros.
  simpl.
  induction s as [| v s' IHs'].
  - simpl. discriminate.
  - simpl.
    simpl in H.
    rewrite PeanoNat.Nat.eqb_sym.
    destruct (PeanoNat.Nat.eqb v n) eqn:Equality.
    + simpl. reflexivity.
    + simpl in H.
      simpl.
      rewrite IHs'.
      * reflexivity.
      * assumption.
Qed.

Lemma less_than_succ: forall (n : nat),
  n <=? S n = true.
Proof.
  intros n.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Theorem remove_does_not_increase_count: ∀ (s : bag) (n : nat),
  (count n (remove_one n s)) <=? (count n s) = true.
Proof.
  intros s n.
  induction s as [| h t IH].
  - simpl. reflexivity.
  - simpl.
    destruct (h =? n) eqn:Eq.
    {
      (* If h = n *)
      rewrite PeanoNat.Nat.eqb_sym.
      rewrite Eq.
      simpl.
      rewrite less_than_succ.
      reflexivity.
    }
    {
      (* If h ≠ n *)
      rewrite PeanoNat.Nat.eqb_sym.
      rewrite Eq.
      simpl.
      rewrite PeanoNat.Nat.eqb_sym.
      rewrite Eq.
      simpl.
      rewrite IH.
      reflexivity.
    }
Qed.

Lemma sum_with_nil: forall l,
  sum l [] = l.
Proof.
  intros.
  induction l; reflexivity.
Qed.

Lemma count_with_cons: forall (l : bag) (n : nat),
  count n (n :: l) = S (count n l).
Proof.
  intros.
  simpl.
  assert (refl: n = n).
  { reflexivity. }
  rewrite <- PeanoNat.Nat.eqb_eq in refl.
  rewrite refl.
  simpl. reflexivity.
Qed.

Theorem involution_injective : ∀ (f : nat → nat),
    (∀ n : nat, n = f (f n)) → (∀ n1 n2 : nat, f n1 = f n2 → n1 = n2).
Proof.
  intros.
  apply (f_equal f) in H0.
  rewrite <- H in H0.
  rewrite <- H in H0.
  assumption.
Qed.

Theorem rev_injective : ∀ (l1 l2 : natlist),
  rev l1 = rev l2 → l1 = l2.
Proof.
  intros.
  apply (f_equal (@rev nat)) in H.
  rewrite rev_involutive in H.
  rewrite rev_involutive in H.
  assumption.
Qed.

Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.

Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.

Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

Definition hd_error (l : natlist) : natoption :=
  match l with
  | nil => None
  | h :: _ => Some h
  end.

Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.

Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.

Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd : ∀ (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  intros.
  destruct l as [| h t]; simpl; reflexivity.
Qed.

(* Partial maps *)

Inductive id : Type :=
  | Id (n : nat).

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

Theorem eqb_id_refl : ∀ x:id, eqb_id x x = true.
Proof.
  intros x.
  destruct x.
  simpl.
  rewrite PeanoNat.Nat.eqb_eq.
  reflexivity.
Qed.

Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

Definition update (d : partial_map) (x : id) (value : nat) : partial_map :=
  record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record y v d' =>
      if eqb_id x y
      then Some v
      else find x d'
  end.

Theorem update_eq :
  ∀ (d : partial_map) (x : id) (v : nat),
  find x (update d x v) = Some v.
Proof.
  intros d x v.
  simpl.
  rewrite eqb_id_refl.
  reflexivity.
Qed.

Theorem update_neq :
  ∀ (d : partial_map) (x y : id) (o : nat),
  eqb_id x y = false → find x (update d y o) = find x d.
Proof.
  intros d x y o H.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Inductive baz : Type :=
  | Baz1 (x : baz)
  | Baz2 (y : baz) (b : bool).

(* How many elements does the type `baz` have?

   I'm not sure I understand the question. *)
