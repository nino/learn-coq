Require Import Unicode.Utf8.
From Learn Require Export Lists.

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

Require Import Reals.
Require Import Lia.
Require Import Lra.

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



