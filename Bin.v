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

Fixpoint incr (b : bin) : bin :=
  match b with
  | [] => [B1]
  | B0 :: b' => B1 :: b'
  | B1 :: b' => B0 :: (incr b')
  end.

Fixpoint incr_signed (b : bin) : bin :=
  match b with
  | [] | [B0] => [B1; B0]
  | [B1] => [B1; B1]
  | B0 :: b' => B1 :: b'
  | B1 :: b' => B0 :: (incr_signed b')
  end.

Fixpoint to_nat (b : bin) : nat :=
  match b with
  | [] => 0
  | B0 :: b' => 2 * to_nat b'
  | B1 :: b' => 1 + 2 * to_nat b'
  end.

Fixpoint of_nat (n : nat) : bin :=
  match n with
  | O => [B0]
  | S n' => incr (of_nat n')
  end.

Fixpoint of_nat_signed (n : nat) : bin :=
  match n with
  | O => [B0; B0]
  | S n' => incr_signed (of_nat_signed n')
  end.

Fixpoint to_positive (b : bin) : option positive :=
  let fix digits_to_positive (b : bin) : positive :=
    match b with
    | [] => xH
    | B0 :: b' => xO (digits_to_positive b')
    | B1 :: b' => xI (digits_to_positive b')
    end in
  match b with
  | [] => None
  | B0 :: b' => to_positive b'
  | B1 :: b' => Some (digits_to_positive b')
  end.

Fixpoint of_positive (p : positive) : bin :=
  match p with
  | xH => [B1]
  | xO p' => B0 :: of_positive p'
  | xI p' => B0 :: of_positive p'
  end.

Definition to_Z (b : bin) : Z :=
  match hd B0 b, to_positive (tl b) with
  | _, None => Z0
  | B0, Some p => Zpos p
  | B1, Some p => Zneg p
  end.

Definition of_Z (z : Z) : bin :=
  match z with
  | Z0 => [B0]
  | Zpos p => B0 :: of_positive p
  | Zneg p => B1 :: of_positive p
  end.

Definition to_N (b : bin) : N :=
  match to_positive b with
  | None => N0
  | Some p => Npos p
  end.

Definition of_N (n : N) : bin :=
  match n with
  | N0 => [B0]
  | Npos p => of_positive p
  end.

Definition bit_to_bool (b : bit) : bool :=
  match b with
  | B0 => false
  | B1 => true
  end.

Definition bool_to_bit (b : bool) : bit :=
  match b with
  | false => B0
  | true => B1
  end.

Theorem bit_bool_bit : forall b,
  bool_to_bit (bit_to_bool b) = b.
Proof. intros []; reflexivity. Qed.

Theorem bool_bit_bool : forall b,
  bit_to_bool (bool_to_bit b) = b.
Proof. intros []; reflexivity. Qed.

Definition bits_to_ascii (b0 b1 b2 b3 b4 b5 b6 b7 : bit) : ascii :=
  Ascii (bit_to_bool b0)
        (bit_to_bool b1)
        (bit_to_bool b2)
        (bit_to_bool b3)
        (bit_to_bool b4)
        (bit_to_bool b5)
        (bit_to_bool b6)
        (bit_to_bool b7).

Fixpoint to_string (b : bin) : option string :=
  match b with
  | [] => Some EmptyString
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b' =>
      match to_string b' with
      | None => None
      | Some s =>
          Some (String (bits_to_ascii b0 b1 b2 b3 b4 b5 b6 b7) s)
      end
  | _ => None
  end.

Fixpoint of_string (s : string) : bin :=
  match s with
  | EmptyString => []
  | String (Ascii b0 b1 b2 b3 b4 b5 b6 b7) s' =>
      bool_to_bit b0 ::
          bool_to_bit b1 ::
          bool_to_bit b2 ::
          bool_to_bit b3 ::
          bool_to_bit b4 ::
          bool_to_bit b5 ::
          bool_to_bit b6 ::
          bool_to_bit b7 ::
          of_string s'
  end.

Theorem bin_string_bin : forall b s,
  to_string b = Some s -> of_string s = b.
Proof.
  induction b as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 b']]]]]]]];
  intros; inversion H; subst; clear H.
  - reflexivity.
  - generalize dependent s.
    induction b'. cbn in *. Admitted.

Theorem string_bin_string : forall s,
  to_string (of_string s) = Some s.
Proof.
  induction s.
  - reflexivity.
  - destruct a. cbn. rewrite IHs.
    unfold bits_to_ascii. repeat rewrite bool_bit_bool. reflexivity.
Qed.

Fixpoint positive_to_nat (p : positive) : nat :=
  match p with
  | xH => 1
  | xO p' => 2 * positive_to_nat p'
  | xI p' => 1 + 2 * positive_to_nat p'
  end.

Definition Z_to_nat (z : Z) : option nat :=
  match z with
  | Z0 => Some O
  | Zpos p => Some (positive_to_nat p)
  | Zneg _ => None
  end.

Definition N_to_nat (n : N) : nat :=
  match n with
  | N0 => 0
  | Npos p => positive_to_nat p
  end.
