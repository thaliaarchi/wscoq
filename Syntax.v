Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Export WSpace.Bin.

Inductive char : Type :=
  | Space
  | Tab
  | LF.

Inductive token : Type :=
  | TPush (n : bin)
  | TDup
  | TCopy (n : bin)
  | TSwap
  | TDrop
  | TSlide (n : bin)
  | TAdd
  | TSub
  | TMul
  | TDiv
  | TMod
  | TStore
  | TRetrieve
  | TLabel (l : bin)
  | TCall (l : bin)
  | TJmp (l : bin)
  | TJz (l : bin)
  | TJn (l : bin)
  | TRet
  | TEnd
  | TPrintc
  | TPrinti
  | TReadc
  | TReadi
  | TError.

Definition map_standard (a : ascii) : option char :=
  match a with
  | Ascii false false false false false true false false => Some Space (* ' ' *)
  | Ascii true false false true false false false false => Some Tab (* '\t' *)
  | Ascii false true false true false false false false => Some LF (* '\n' *)
  | _ => None
  end.
Definition map_STL (a : ascii) : option char :=
  match a with
  | Ascii true true false false true false true false => Some Space (* 'S' *)
  | Ascii false false true false true false true false => Some Tab (* 'T' *)
  | Ascii false false true true false false true false => Some LF (* 'L' *)
  | _ => None
  end.

Fixpoint scan (s : string) (map : ascii -> option char)
    : list char :=
  match s with
  | EmptyString => []
  | String a s' => match map a with
                   | Some c => c :: scan s' map
                   | None => scan s' map
                   end
  end.

Fixpoint parse (cs : list char) : list token :=
  let fix parse_arg' (cs : list char) (ctor : bin -> token) (b : bin)
      : list token :=
    match cs with
    | Space :: cs' => parse_arg' cs' ctor (B0 :: b)
    | Tab :: cs' => parse_arg' cs' ctor (B1 :: b)
    | LF :: cs' => ctor b :: parse cs'
    | [] => [TError]
    end in
  let parse_arg := fun cs ctor => parse_arg' cs ctor [] in
  match cs with
  | Space :: Space :: cs' => parse_arg cs' TPush
  | Space :: LF :: Space :: cs' => TDup :: parse cs'
  | Space :: Tab :: Space :: cs' => parse_arg cs' TCopy
  | Space :: LF :: Tab :: cs' => TSwap :: parse cs'
  | Space :: LF :: LF :: cs' => TDrop :: parse cs'
  | Space :: Tab :: LF :: cs' => parse_arg cs' TSlide
  | Tab :: Space :: Space :: Space :: cs' => TAdd :: parse cs'
  | Tab :: Space :: Space :: Tab :: cs' => TSub :: parse cs'
  | Tab :: Space :: Space :: LF :: cs' => TMul :: parse cs'
  | Tab :: Space :: Tab :: Space :: cs' => TDiv :: parse cs'
  | Tab :: Space :: Tab :: Tab :: cs' => TMod :: parse cs'
  | Tab :: Tab :: Space :: cs' => TStore :: parse cs'
  | Tab :: Tab :: Tab :: cs' => TRetrieve :: parse cs'
  | LF :: Space :: Space :: cs' => parse_arg cs' TLabel
  | LF :: Space :: Tab :: cs' => parse_arg cs' TCall
  | LF :: Space :: LF :: cs' => parse_arg cs' TJmp
  | LF :: Tab :: Space :: cs' => parse_arg cs' TJz
  | LF :: Tab :: Tab :: cs' => parse_arg cs' TJn
  | LF :: Tab :: LF :: cs' => TRet :: parse cs'
  | LF :: LF :: LF :: cs' => TEnd :: parse cs'
  | Tab :: LF :: Space :: Space :: cs' => TPrintc :: parse cs'
  | Tab :: LF :: Space :: Tab :: cs' => TPrinti :: parse cs'
  | Tab :: LF :: Tab :: Space :: cs' => TReadc :: parse cs'
  | Tab :: LF :: Tab :: Tab :: cs' => TReadi :: parse cs'
  | [] => []
  | _ => [TError]
  end.
