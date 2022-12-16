Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Export WSpace.Bin.

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

Inductive io : Type :=
  | IOChar (c : Z)
  | IOInt (n : Z).

Inductive vm : Type :=
  | VM (program : list inst)
       (stack : list Z)
       (heap : list Z)
       (stdin : list io)
       (stdout : list io)
       (pc : nat)
       (calls : list nat).

Fixpoint store (hp : list Z) (n : nat) (x : Z) : list Z :=
  match n, hp with
  | O, _ :: hp' => x :: hp'
  | O, [] => [x]
  | S n', y :: hp' => y :: store hp' n' x
  | S n', [] => 0 :: store [] n' x
  end.
Definition retrieve (hp : list Z) (n : nat) : Z :=
  nth_default 0 hp n.

Inductive step : vm -> vm -> Prop :=
  | SPush : forall prog stk hp sin sout pc calls n,
      nth_error prog pc = Some (IPush n) ->
      step (VM prog stk hp sin sout pc calls)
           (VM prog (n :: stk) hp sin sout (S pc) calls)
  | SDup : forall prog x stk' hp sin sout pc calls,
      nth_error prog pc = Some IDup ->
      step (VM prog (x :: stk') hp sin sout pc calls)
           (VM prog (x :: x :: stk') hp sin sout (S pc) calls)
  | SCopy : forall prog stk hp sin sout pc calls n x,
      nth_error prog pc = Some (ICopy n) ->
      nth_error stk n = Some x ->
      step (VM prog stk hp sin sout pc calls)
           (VM prog (x :: stk) hp sin sout (S pc) calls)
  | SSwap : forall prog x y stk' hp sin sout pc calls,
      nth_error prog pc = Some (ISwap) ->
      step (VM prog (x :: y :: stk') hp sin sout pc calls)
           (VM prog (y :: x :: stk') hp sin sout (S pc) calls)
  | SDrop : forall prog x stk' hp sin sout pc calls,
      nth_error prog pc = Some (IDrop) ->
      step (VM prog (x :: stk') hp sin sout pc calls)
           (VM prog stk' hp sin sout (S pc) calls)
  | SSlide : forall prog x stk' hp sin sout pc calls n,
      nth_error prog pc = Some (ISlide n) ->
      step (VM prog (x :: stk') hp sin sout pc calls)
           (VM prog (x :: skipn n stk') hp sin sout (S pc) calls)
  | SAdd : forall prog y x stk' hp sin sout pc calls,
      nth_error prog pc = Some IAdd ->
      step (VM prog (y :: x :: stk') hp sin sout pc calls)
           (VM prog (x + y :: stk') hp sin sout (S pc) calls)
  | SSub : forall prog y x stk' hp sin sout pc calls,
      nth_error prog pc = Some ISub ->
      step (VM prog (y :: x :: stk') hp sin sout pc calls)
           (VM prog (x - y :: stk') hp sin sout (S pc) calls)
  | SMul : forall prog y x stk' hp sin sout pc calls,
      nth_error prog pc = Some IMul ->
      step (VM prog (y :: x :: stk') hp sin sout pc calls)
           (VM prog (x * y :: stk') hp sin sout (S pc) calls)
  | SDiv : forall prog y x stk' hp sin sout pc calls,
      nth_error prog pc = Some IDiv ->
      step (VM prog (y :: x :: stk') hp sin sout pc calls)
           (VM prog (x / y :: stk') hp sin sout (S pc) calls)
  | SMod : forall prog y x stk' hp sin sout pc calls,
      nth_error prog pc = Some IMod ->
      step (VM prog (y :: x :: stk') hp sin sout pc calls)
           (VM prog (x mod y :: stk') hp sin sout (S pc) calls)
  | SStore : forall prog y x n stk' hp sin sout pc calls,
      nth_error prog pc = Some IStore ->
      Z_to_nat x = Some n ->
      step (VM prog (y :: x :: stk') hp sin sout pc calls)
           (VM prog stk' (store hp n y) sin sout (S pc) calls)
  | SRetrieve : forall prog x n stk' hp sin sout pc calls,
      nth_error prog pc = Some IRetrieve ->
      Z_to_nat x = Some n ->
      step (VM prog (x :: stk') hp sin sout pc calls)
           (VM prog (retrieve hp n :: stk') hp sin sout (S pc) calls)
  | SLabel : forall prog stk hp sin sout pc calls l,
      nth_error prog pc = Some (ILabel l) ->
      step (VM prog stk hp sin sout pc calls)
           (VM prog stk hp sin sout (S pc) calls)
  | SCall : forall prog stk hp sin sout pc calls l,
      nth_error prog pc = Some (ICall l) ->
      step (VM prog stk hp sin sout pc calls)
           (VM prog stk hp sin sout l (S pc :: calls))
  | SJmp : forall prog stk hp sin sout pc calls l,
      nth_error prog pc = Some (IJmp l) ->
      step (VM prog stk hp sin sout pc calls)
           (VM prog stk hp sin sout l calls)
  | SJz : forall prog x stk' hp sin sout pc calls l,
      nth_error prog pc = Some (IJz l) ->
      step (VM prog (x :: stk') hp sin sout pc calls)
           (VM prog stk' hp sin sout (if x =? 0 then l else S pc) calls)
  | SJn : forall prog x stk' hp sin sout pc calls l,
      nth_error prog pc = Some (IJn l) ->
      step (VM prog (x :: stk') hp sin sout pc calls)
           (VM prog stk' hp sin sout (if x <? 0 then l else S pc) calls)
  | SRet : forall prog stk hp sin sout pc l calls,
      nth_error prog pc = Some IRet ->
      step (VM prog stk hp sin sout pc (l :: calls))
           (VM prog stk hp sin sout l calls)
  | SEnd : forall prog stk hp sin sout pc calls,
      nth_error prog pc = Some IEnd ->
      step (VM prog stk hp sin sout pc calls)
           (VM prog stk hp sin sout (length prog) calls)
  | SPrintc : forall prog x stk' hp sin sout pc calls,
      nth_error prog pc = Some IPrintc ->
      step (VM prog (x :: stk') hp sin sout pc calls)
           (VM prog stk' hp sin (IOChar x :: sout) (S pc) calls)
  | SPrinti : forall prog v stk' hp sin sout pc calls,
      nth_error prog pc = Some IPrinti ->
      step (VM prog (v :: stk') hp sin sout pc calls)
           (VM prog stk' hp sin (IOInt v :: sout) (S pc) calls)
  | SReadc : forall prog x n stk' hp v sin sout pc calls,
      nth_error prog pc = Some IReadc ->
      Z_to_nat x = Some n ->
      step (VM prog (x :: stk') hp (IOChar v :: sin) sout pc calls)
           (VM prog stk' (store hp n v) sin sout (S pc) calls)
  | SReadi : forall prog x n stk' hp v sin sout pc calls,
      nth_error prog pc = Some IReadi ->
      Z_to_nat x = Some n ->
      step (VM prog (x :: stk') hp (IOInt v :: sin) sout pc calls)
           (VM prog stk' (store hp n v) sin sout (S pc) calls).

(* Equivalent to clos_refl_trans_1n in Coq.Relations.Relation_Operators. *)
Inductive execute : vm -> vm -> Prop :=
  | execute_refl : forall (x : vm),
      execute x x
  | execute_step : forall (x y z : vm),
      step x y ->
      execute y z ->
      execute x z.

Ltac execute :=
  repeat (eapply execute_step; [econstructor; reflexivity | cbn]);
  apply execute_refl.
