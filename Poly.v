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


