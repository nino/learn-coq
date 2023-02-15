Inductive natprod :=
  | pair (n1 n2 : nat).

Notation "( x , y )" := (pair x y).

Definition fst pair := match pair with
  | (x, y) => x
  end.
  
Definition snd pair := match pair with (x, y) => y end.

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity. Qed.

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
  
