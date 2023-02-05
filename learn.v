Inductive day :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_day d :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday
  end.

Compute (next_day thursday).

Example two_days_after_friday_is_sunday :
  (next_day (next_day friday)) = sunday.
Proof.
  simpl.
  reflexivity.
Qed.

Inductive bool := true | false.

Definition bool_neg b :=
  match b with
  | true => false
  | false => true
  end.

Definition bool_and a b :=
  match a with
  | true => b
  | false => false
  end.

Definition bool_or a b :=
  match a with
  | true => true
  | false => b
  end.

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => bool_neg b2
  | false => true
  end.

Example test_nandb1: (nandb true false) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_nandb2: (nandb false false) = true.
Proof.
  reflexivity.
Qed.

Example test_nandb3: (nandb false true) = true.
Proof.
  reflexivity.
Qed.

Example test_nandb4: (nandb true true) = false.
Proof.
  reflexivity.
Qed.


Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match (b1, b2, b3) with
  | (true, true, true) => true
  | (_, _, _) => false
  end.

Example test_andb31: (andb3 true true true) = true.
Proof.
  reflexivity.
Qed.

Example test_andb32: (andb3 false true true) = false.
Proof.
  reflexivity.
Qed.

Example test_andb33: (andb3 true false true) = false.
Proof.
  reflexivity.
Qed.

Example test_andb34: (andb3 true true false) = false.
Proof.
  reflexivity.
Qed.


Inductive rgb :=
  | red
  | green
  | blue.

Inductive color :=
  | black
  | white
  | primary (p : rgb).

Definition monochrome color :=
  match color with
  | primary _ => false
  | _ => true
  end.

Definition isred color :=
  match color with
  | primary red => true
  | _ => false
  end.

