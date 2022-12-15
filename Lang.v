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
       (stdout : list io)
       (pc : nat).
       (* callstack *)
       (* labels *)

Definition get_program (v : vm) : list inst :=
  match v with VM program _ _ _ _ _ => program end.
Definition get_stack (v : vm) : list Z :=
  match v with VM _ stack _ _ _ _ => stack end.
Definition get_heap (v : vm) : list Z :=
  match v with VM _ _ heap _ _ _ => heap end.
Definition get_stdin (v : vm) : list io :=
  match v with VM _ _ _ stdin _ _ => stdin end.
Definition get_stdout (v : vm) : list io :=
  match v with VM _ _ _ _ stdout _ => stdout end.
Definition get_pc (v : vm) : nat :=
  match v with VM _ _ _ _ _ pc => pc end.

Definition get_inst (v : vm) : option inst :=
  nth_error (get_program v) (get_pc v).

Definition set_stack (v : vm) (stack : list Z) : vm :=
  match v with VM program _ heap stdin stdout pc =>
    VM program stack heap stdin stdout pc end.
Definition set_heap (v : vm) (heap : list Z) : vm :=
  match v with VM program stack _ stdin stdout pc =>
    VM program stack heap stdin stdout pc end.
Definition incr_pc (v : vm) : vm :=
  match v with VM program stack heap stdin stdout pc =>
    VM program stack heap stdin stdout (S pc) end.

Inductive step : vm -> vm -> Prop :=
  | SPush : forall prog stk hp sin sout pc n,
      nth_error prog pc = Some (IPush n) ->
      step (VM prog stk hp sin sout pc)
           (VM prog (n :: stk) hp sin sout (S pc))
  | SDup : forall prog x stk' hp sin sout pc,
      nth_error prog pc = Some IDup ->
      step (VM prog (x :: stk') hp sin sout pc)
           (VM prog (x :: x :: stk') hp sin sout (S pc))
  | SCopy : forall prog stk hp sin sout pc n x,
      nth_error prog pc = Some (ICopy n) ->
      nth_error stk n = Some x ->
      step (VM prog stk hp sin sout pc)
           (VM prog (x :: stk) hp sin sout (S pc))
  | SSwap : forall prog x y stk' hp sin sout pc,
      nth_error prog pc = Some (ISwap) ->
      step (VM prog (x :: y :: stk') hp sin sout pc)
           (VM prog (y :: x :: stk') hp sin sout (S pc))
  | SDrop : forall prog x stk' hp sin sout pc,
      nth_error prog pc = Some (IDrop) ->
      step (VM prog (x :: stk') hp sin sout pc)
           (VM prog stk' hp sin sout (S pc))
  | SSlide : forall prog x stk' hp sin sout pc n,
      nth_error prog pc = Some (ISlide n) ->
      step (VM prog (x :: stk') hp sin sout pc)
           (VM prog (x :: skipn n stk') hp sin sout (S pc))
  | SAdd : forall prog x y stk' hp sin sout pc,
      nth_error prog pc = Some IAdd ->
      step (VM prog (x :: y :: stk') hp sin sout pc)
           (VM prog (y + x :: stk') hp sin sout (S pc))
  | SSub : forall prog x y stk' hp sin sout pc,
      nth_error prog pc = Some ISub ->
      step (VM prog (x :: y :: stk') hp sin sout pc)
           (VM prog (y - x :: stk') hp sin sout (S pc))
  | SMul : forall prog x y stk' hp sin sout pc,
      nth_error prog pc = Some IMul ->
      step (VM prog (x :: y :: stk') hp sin sout pc)
           (VM prog (y * x :: stk') hp sin sout (S pc))
  | SDiv : forall prog x y stk' hp sin sout pc,
      nth_error prog pc = Some IDiv ->
      step (VM prog (x :: y :: stk') hp sin sout pc)
           (VM prog (y / x :: stk') hp sin sout (S pc))
  | SMod : forall prog x y stk' hp sin sout pc,
      nth_error prog pc = Some IMod ->
      step (VM prog (x :: y :: stk') hp sin sout pc)
           (VM prog (y mod x :: stk') hp sin sout (S pc))
  | SEnd : forall prog stk hp sin sout pc,
      nth_error prog pc = Some IEnd ->
      step (VM prog stk hp sin sout pc)
           (VM prog stk hp sin sout (length prog))
  | SPrintc : forall prog x stk' hp sin sout pc,
      nth_error prog pc = Some IPrintc ->
      step (VM prog (x :: stk') hp sin sout pc)
           (VM prog stk' hp sin (IOChar x :: sout) (S pc))
  | SPrinti : forall prog x stk' hp sin sout pc,
      nth_error prog pc = Some IPrinti ->
      step (VM prog (x :: stk') hp sin sout pc)
           (VM prog stk' hp sin (IOInt x :: sout) (S pc)).

(* Equivalent to clos_refl_trans_1n in Coq.Relations.Relation_Operators. *)
Inductive execute : vm -> vm -> Prop :=
  | execute_refl : forall (x : vm),
      execute x x
  | execute_step : forall (x y z : vm),
      step x y ->
      execute y z ->
      execute x z.

Ltac step inst :=
  eapply execute_step; [apply inst; reflexivity | ].

Example add_1_2 :
  execute (VM [IPush 1; IPush 2; IAdd; IPrinti; IEnd] [] [] [] [] 0)
          (VM [IPush 1; IPush 2; IAdd; IPrinti; IEnd] [] [] [] [IOInt 3] 5).
Proof.
  step SPush. step SPush. step SAdd. step SPrinti. step SEnd.
  apply execute_refl.
Qed.
