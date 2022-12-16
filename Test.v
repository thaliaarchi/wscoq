Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
From WSpace Require Export Bin Syntax Lang.

Example execute_add_1_2 :
  let prog := [IPush 1; IPush 2; IAdd; IPrinti; IEnd] in
  execute (VM prog [] [] [] [] 0 [])
          (VM prog [] [] [] [IOInt 3] 5 []).
Proof. execute. Qed.

Definition count_src := "CountSfromS1StoT10LLSSSTSSSSTTLSLSTLSTSSSTSTSLTLSSSSSTLTSSSSLSSSSTSTTLTSSTLTSSTSSSTSTLLSLSTSSSSTTLLSSSTSSSTSTLSLLLLL"%string.
Definition count_chars := [
    Space; Space; Space; Tab; LF; LF; Space; Space; Space; Tab; Space; Space;
    Space; Space; Tab; Tab; LF; Space; LF; Space; Tab; LF; Space; Tab; Space;
    Space; Space; Tab; Space; Tab; Space; LF; Tab; LF; Space; Space; Space;
    Space; Space; Tab; LF; Tab; Space; Space; Space; Space; LF; Space; Space;
    Space; Space; Tab; Space; Tab; Tab; LF; Tab; Space; Space; Tab; LF; Tab;
    Space; Space; Tab; Space; Space; Space; Tab; Space; Tab; LF; LF; Space; LF;
    Space; Tab; Space; Space; Space; Space; Tab; Tab; LF; LF; Space; Space;
    Space; Tab; Space; Space; Space; Tab; Space; Tab; LF; Space; LF; LF; LF; LF;
    LF].
Definition count_tokens := [
    TPush (Bin.of_nat_signed 1);
    TLabel (Bin.of_string "C");
    TDup; TPrinti;
    TPush (Bin.of_nat_signed 10); TPrintc;
    TPush (Bin.of_nat_signed 1); TAdd;
    TDup; TPush (Bin.of_nat_signed 11); TSub; TJz (Bin.of_string "E");
    TJmp (Bin.of_string "C");
    TLabel (Bin.of_string "E");
    TDrop;
    TEnd].
Definition count_prog := [
    IPush 1;
    ILabel (Bin.of_string "C");
    IDup; IPrinti;
    IPush 10; IPrintc;
    IPush 1; IAdd;
    IDup; IPush 11; ISub; IJz 13;
    IJmp 1;
    ILabel (Bin.of_string "E");
    IDrop;
    IEnd].

Example scan_count : scan count_src map_STL = count_chars.
Proof. reflexivity. Qed.

Example parse_count : parse count_chars = count_tokens.
Proof. reflexivity. Qed.

Example execute_count :
  execute (VM count_prog [] [] [] [] 0 [])
          (VM count_prog [] [] []
              [IOChar 10; IOInt 10; IOChar 10; IOInt 9; IOChar 10; IOInt 8;
               IOChar 10; IOInt 7; IOChar 10; IOInt 6; IOChar 10; IOInt 5;
               IOChar 10; IOInt 4; IOChar 10; IOInt 3; IOChar 10; IOInt 2;
               IOChar 10; IOInt 1] 16 []).
Proof. execute. Qed.

Example execute_fibonacci :
  let prog := [
    IPush 72; IPrintc;
    IPush 111; IPrintc;
    IPush 119; IPrintc;
    IPush 32; IPrintc;
    IPush 109; IPrintc;
    IPush 97; IPrintc;
    IPush 110; IPrintc;
    IPush 121; IPrintc;
    IPush 63; IPrintc;
    IPush 32; IPrintc;
    IPush 2; IReadi;
    IPush 0;
    IPush 1;
    IDup; IPrinti;
    IPush 10; IPrintc;
    ILabel (Bin.of_nat 1);
    IDup; IPush 1; ISwap; IStore;
    IAdd;
    IPush 1; IRetrieve;
    ISwap;
    IDup; IPrinti;
    IPush 10; IPrintc;
    IPush 2; IRetrieve;
    IPush 1; ISub;
    IDup; IPush 2; ISwap; IStore;
    IJn 51; (* 2 *)
    IJmp 28; (* 1 *)
    ILabel (Bin.of_nat 2);
    IEnd] in
  execute (VM prog [] [] [IOInt 5] [] 0 [])
          (VM prog [13; 8] [0; 8; -1] []
              [IOChar 10; IOInt 13; IOChar 10; IOInt 8; IOChar 10; IOInt 5;
               IOChar 10; IOInt 3; IOChar 10; IOInt 2; IOChar 10; IOInt 1;
               IOChar 10; IOInt 1; IOChar 32; IOChar 63; IOChar 121; IOChar 110;
               IOChar 97; IOChar 109; IOChar 32; IOChar 119; IOChar 111;
               IOChar 72] 53 []).
Proof. execute. Qed.
