Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import WSpace.Bin.

Inductive inst : Type :=
  | IPush (n : Z)
  | IDup
  | ICopy (n : nat)
  | ISwap
  | IDrop
  | ISlide (n : nat)
  | IAdd
  | ISub
  | IMul
  | IDiv
  | IMod
  | IStore
  | IRetrieve
  | ILabel (l : bin)
  | ICall (l : bin)
  | IJmp (l : bin)
  | IJz (l : bin)
  | IJn (l : bin)
  | IRet
  | IEnd
  | IPrintc
  | IPrinti
  | IReadc
  | IReadi.

Inductive io : Type :=
  | IOChar (c : Z)
  | IOInt (n : Z).

Inductive vm : Type :=
  | VM (program : list inst)
       (stack : list Z)
       (heap : list Z)
       (stdin : list io)
       (stdout : list io).
       (* callstack *)
       (* labels *)

Definition program (v : vm) : list inst :=
  match v with VM program _ _ _ _ => program end.
Definition stack (v : vm) : list Z :=
  match v with VM _ stack _ _ _ => stack end.
Definition heap (v : vm) : list Z :=
  match v with VM _ _ heap _ _ => heap end.
Definition stdin (v : vm) : list io :=
  match v with VM _ _ _ stdin _ => stdin end.
Definition stdout (v : vm) : list io :=
  match v with VM _ _ _ _ stdout => stdout end.

Definition set_stack (v : vm) (new_stack : list Z) : vm :=
  match v with
  | VM program stack heap stdin stdout =>
      VM program new_stack heap stdin stdout
  end.
Definition execute_arith (v : vm) (f : Z -> Z -> Z) : option vm :=
  match stack v with
  | y :: x :: stk => Some (set_stack v (f x y :: stk))
  | _ => None
  end.
Definition execute_print (v : vm) (f : Z -> io) : option vm :=
  match v with
  | VM program (x :: stk) heap stdin stdout =>
      Some (VM program stk heap stdin (f x :: stdout))
  | _ => None
  end.

Definition execute_inst (v : vm) (i : inst) : option vm :=
  match i, stack v with
  | IPush n, stk         => Some (set_stack v (n :: stk))
  | IDup, x :: stk       => Some (set_stack v (x :: x :: stk))
  | ICopy n, stk         => match nth_error stk n with
                            | Some x => Some (set_stack v (x :: stk))
                            | None => None
                            end
  | ISwap, y :: x :: stk => Some (set_stack v (x :: y :: stk))
  | IDrop, x :: stk      => Some (set_stack v (stk))
  | ISlide n, x :: stk   => Some (set_stack v (x :: skipn n stk))
  | IAdd, _              => execute_arith v Z.add
  | ISub, _              => execute_arith v Z.sub
  | IMul, _              => execute_arith v Z.mul
  | IDiv, _              => execute_arith v Z.div
  | IMod, _              => execute_arith v Z.modulo
  | IPrintc, _           => execute_print v IOChar
  | IPrinti, _           => execute_print v IOInt
  | _, _                 => None
  end.
