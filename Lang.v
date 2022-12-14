Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

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
  | ILabel (l : nat)
  | ICall (l : nat)
  | IJmp (l : nat)
  | IJz (l : nat)
  | IJn (l : nat)
  | IRet
  | IEnd
  | IPrintc
  | IPrinti
  | IReadc
  | IReadi.

Definition execute_inst (i : inst) (s : list Z) : option (list Z) :=
  match i, s with
  | IPush n, s         => Some (n :: s)
  | IDup, x :: s       => Some (x :: x :: s)
  | ICopy n, s         => match nth_error s n with
                          | Some x => Some (x :: s)
                          | None => None
                          end
  | ISwap, y :: x :: s => Some (x :: y :: s)
  | IDrop, x :: s      => Some (s)
  | ISlide n, x :: s   => Some (x :: skipn n s)
  | IAdd, y :: x :: s  => Some (x + y :: s)
  | ISub, y :: x :: s  => Some (x - y :: s)
  | IMul, y :: x :: s  => Some (x * y :: s)
  | IDiv, y :: x :: s  => Some (x / y :: s)
  | IMod, y :: x :: s  => Some (x mod y :: s)
  | _, _               => None
  end.
