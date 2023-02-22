Require Import Unicode.Utf8.
Require Import Reals.
Require Import Lia.
Require Import Lra.

Inductive list (X : Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X : Type} (l : list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ t => S (length t)
  end.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Theorem app_nil_r : ∀ (X : Type), ∀ l : list X,
  l ++ [] = l.
Proof.
  intros X l.
  induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Theorem app_assoc : ∀ (A : Type) (l m n : list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite IHl.
    reflexivity.
Qed.

Theorem app_length : ∀ (X : Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros.
  induction l1.
  - simpl. reflexivity.
  - simpl. rewrite IHl1.
    reflexivity.
Qed.

Theorem rev_app_distr : ∀ X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros.
  induction l1.
  - simpl.
    rewrite app_nil_r.
    reflexivity.
  - simpl. rewrite IHl1.
    rewrite app_assoc.
    reflexivity.
Qed.

Theorem rev_involutive : ∀ X : Type, ∀ l : list X,
  rev (rev l) = l.
Proof.
  intros.
  induction l.
  - simpl.
    reflexivity.
  - simpl.
    rewrite rev_app_distr.
    rewrite IHl.
    simpl.
    reflexivity.
Qed.

Inductive prod (X Y : Type) :=
  | pair (x : X) (y : Y).

Arguments pair {X} {Y}.
Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, _) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (_, y) => y
  end.

Fixpoint combine {X Y : Type } (lx : list X) (ly : list Y) : list (X * Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Fixpoint map {X Y : Type} (f : X → Y) (l : list X) : list Y :=
  match l with
  | nil => nil
  | cons h t => (f h) :: (map f t)
  end.

Definition split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
  ((map fst l), (map snd l)).

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.

Module OptionPlayground.

  Inductive option (X:Type) : Type :=
    | Some (x : X)
    | None.

  Arguments Some {X}.
  Arguments None {X}.

  Definition hd_error {X : Type} (l : list X) : option X :=
    match l with
    | nil => None
    | cons h _ => Some h
    end.

End OptionPlayground.

Section OtherCrap.

Check Rmult_le_compat_l.

Lemma lessthanthing : ∀ (n : nat),
  (1 <= 1.5^n)%R.
Proof.
  intros.
  induction n.
  - intuition.
  - simpl.
    apply (Rmult_le_compat_l 1.5) in IHn.
    2: { lra. }
    rewrite Rmult_1_r in IHn.
    lra.
Qed.

End OtherCrap.

Fixpoint filter {X:Type} (test: X → bool) (l:list X) : list X :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: (filter test t)
    else filter test t
  end.

Definition partition
  {X : Type}
  (test : X → bool)
  (l : list X)
  : list X * list X :=
  (filter test l, filter (fun e => negb (test e)) l).

Example test_partition1: partition Nat.odd [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.

Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

Lemma map_app : ∀ (X Y : Type) (f : X → Y) (l1 l2 : list X),
  (map f l1) ++ (map f l2) = map f (l1 ++ l2).
Proof.
  intros.
  induction l1.
  - simpl. reflexivity.
  - simpl. rewrite IHl1. reflexivity.
Qed.

Theorem map_rev : ∀ (X Y : Type) (f : X → Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl.
    rewrite <- map_app.
    rewrite IHl.
    reflexivity.
Qed.

Fixpoint flatten {X : Type} (l: list (list X)) : list X :=
  match l with
  | nil => nil
  | h :: t => h ++ (flatten t)
  end.

Definition flat_map {X Y: Type} (f: X → list Y) (l: list X) : list Y :=
  flatten (map f l).

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

Definition option_map {X Y : Type} (f : X → Y) (xo : option X)
                      : option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.

Fixpoint fold {X Y: Type} (f : X → Y → Y) (l : list X) (b : Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Module Exercises.

  (* map in terms of fold *)
  Definition fold_map {X Y: Type} (f: X → Y) (l: list X) : list Y :=
    fold (fun el acc => [f el] ++ acc) l [].

  Example test_map1: fold_map (fun x => plus 3 x) [2;0;2] = [5;3;5].
  Proof. reflexivity. Qed.


  Example test_map2:
    fold_map Nat.odd [2;1;2;5] = [false;true;false;true].
  Proof. reflexivity. Qed.

  Example test_map3:
    fold_map (fun n => [Nat.even n; Nat.odd n]) [2;1;2;5]
    = [[true;false];[false;true];[true;false];[false;true]].
  Proof. reflexivity. Qed.

  Theorem fold_map_correct : ∀ {X Y : Type} (f : X → Y) (l : list X),
    fold_map f l = map f l.
  Proof.
    intros.
    induction l.
    - simpl. reflexivity.
    - simpl.
      rewrite <- IHl.
      reflexivity.
  Qed.

  Definition prod_curry
    {X Y Z : Type} (f : X * Y → Z) (x : X) (y : Y) : Z :=
    f (x, y).

  Definition prod_uncurry
    {X Y Z : Type} (f : X → Y → Z) (p : X * Y) : Z :=
    match p with
    | (x, y) => f x y
    end.

  Theorem uncurry_curry : ∀ (X Y Z : Type) (f : X → Y → Z) x y,
    prod_curry (prod_uncurry f) x y = f x y.
  Proof.
    intros.
    unfold prod_curry.
    unfold prod_uncurry.
    reflexivity.
  Qed.

  Theorem curry_uncurry : ∀ (X Y Z : Type) (f : (X * Y) → Z) (p : X * Y),
    prod_uncurry (prod_curry f) p = f p.
  Proof.
    intros.
    unfold prod_uncurry.
    unfold prod_curry.
    destruct p; reflexivity.
  Qed.

  Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
    match l with
    | [] => None
    | a :: l' => if Nat.eqb n O then Some a else nth_error l' (pred n)
    end.

  Lemma length_of_cons_neq_0 : ∀ (X : Type) (l : list X) (el : X),
    (@length X (el :: l)) ≠ 0.
  Admitted.

  (* Lemma if_length_h_t_is_n_then_length_t_is_pred_n: ∀ (X : Type) (h : X) (t : list X), *)
  (*   @length X ( *)

  Theorem nth_error_informal_but_not_really : ∀ (X : Type) (l : list X) (n : nat),
    @length X l = n → @nth_error X l n = None.
  Proof.
    intros.
    induction l.
    - simpl. reflexivity.
    - simpl.
      assert (length (x :: l) ≠ 0).
      { apply length_of_cons_neq_0. }
      rewrite H in H0.
      rewrite <- PeanoNat.Nat.eqb_neq in H0.
      rewrite H0.
  Admitted.
  (* They said to do it informally. I tried to do it formally, but couldn't do
   * it. *)

End Exercises.

