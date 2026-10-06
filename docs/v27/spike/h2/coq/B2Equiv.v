(* B2 (spike H.5 stage 2): the restructured interpreter IS the pre-B2 interpreter.

   Each member of Interp.v's mutual block is equal to the same member of RefInterp.v (the
   pre-B2 block, verbatim) by reflexivity: the kernel unfolds NAME_body and beta-reduces, and
   the two fixpoints then have the same bodies. So is the whole program's run (Main.run, whose
   text is unchanged, states it over Interp.callp). Proof obligations: these eleven equalities,
   nothing else. Print Assumptions lists only the kernel's primitive types and operations
   (PrimInt63, PrimFloat, PArray), which the statements' own terms use: no axiom.
   The negative control shows reflexivity is not vacuous here: a member is NOT convertible to
   its pre-B2 counterpart run with one more unit of fuel. *)

From Coq Require Import ZArith List.
From PS Require Import Syntax Values Interp RefInterp ProgGlobals Prog Boundary CMain Main.
Import ListNotations.

Lemma evale_b2 : Interp.evale = RefInterp.evale. Proof. reflexivity. Qed.
Lemma evall_b2 : Interp.evall = RefInterp.evall. Proof. reflexivity. Qed.
Lemma evalargs_b2 : Interp.evalargs = RefInterp.evalargs. Proof. reflexivity. Qed.
Lemma evalx_b2 : Interp.evalx = RefInterp.evalx. Proof. reflexivity. Qed.
Lemma callp_b2 : Interp.callp = RefInterp.callp. Proof. reflexivity. Qed.
Lemma exec_b2 : Interp.exec = RefInterp.exec. Proof. reflexivity. Qed.
Lemma for_loop_b2 : Interp.for_loop = RefInterp.for_loop. Proof. reflexivity. Qed.
Lemma exec_list_b2 : Interp.exec_list = RefInterp.exec_list. Proof. reflexivity. Qed.
Lemma goto_in_b2 : Interp.goto_in = RefInterp.goto_in. Proof. reflexivity. Qed.
Lemma write_items_b2 : Interp.write_items = RefInterp.write_items. Proof. reflexivity. Qed.

(* the program's semantics: Main.run with the pre-B2 interpreter in place of the new one *)
Lemma run_b2 :
  Main.run = fun fuel x => RefInterp.callp procs_array nglobals ext fuel P_mainbody [] (initial_state x).
Proof. reflexivity. Qed.

(* negative control *)
Goal Interp.exec = fun procs sb ext fuel s st => RefInterp.exec procs sb ext (S fuel) s st.
Proof. Fail reflexivity. Abort.

Print Assumptions run_b2.
