Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Inductive bit : Type :=
  | B0
  | B1.

Definition bin : Type := list bit.

Fixpoint bin_to_nat (b : bin) : nat :=
  match b with
  | [] => 0
  | B0 :: b' => 2 * bin_to_nat b'
  | B1 :: b' => 1 + 2 * bin_to_nat b'
  end.

Fixpoint bin_to_positive (b : bin) : option positive :=
  let fix digits_to_positive (b : bin) : positive :=
    match b with
    | [] => xH
    | B0 :: b' => xO (digits_to_positive b')
    | B1 :: b' => xI (digits_to_positive b')
    end in
  match b with
  | [] => None
  | B0 :: b' => bin_to_positive b'
  | B1 :: b' => Some (digits_to_positive b')
  end.

Definition bin_to_Z (b : bin) : Z :=
  match hd B0 b, bin_to_positive (tl b) with
  | _, None => Z0
  | B0, Some p => Zpos p
  | B1, Some p => Zneg p
  end.

Definition bin_to_N (b : bin) : N :=
  match bin_to_positive b with
  | None => N0
  | Some p => Npos p
  end.

Definition bit_to_bool (b : bit) : bool :=
  match b with
  | B0 => false
  | B1 => true
  end.

Definition bin_to_string (b : bin) : option string :=
  let fix bin_to_string (b : bin) (s : string) : option string :=
    match b with
    | [] => Some s
    | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b' =>
        bin_to_string b' (String (Ascii (bit_to_bool b0)
                                        (bit_to_bool b1)
                                        (bit_to_bool b2)
                                        (bit_to_bool b3)
                                        (bit_to_bool b4)
                                        (bit_to_bool b5)
                                        (bit_to_bool b6)
                                        (bit_to_bool b7)) s)
    | _ => None
    end in
  bin_to_string b EmptyString.
