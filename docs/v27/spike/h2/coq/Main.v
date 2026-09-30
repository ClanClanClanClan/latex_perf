(* The whole program: initial state, a run of mainbody, and extraction (spike H.2).

   The initial state is C's: every global in static storage, zero-initialised (C11
   6.7.9 p10: arithmetic 0, pointers NULL, unions' first member 0), string literals in
   their own static arrays, then what TeX Live's C main program (lib/texmfmp.c main,
   maininit, parse_options) wrote before it called mainbody: CMain.v, generated from a
   measurement of the reference binary at the entry of mainbody (h2/cmain/). *)

From Coq Require Import ZArith List Bool String PArray Uint63 Sint63 Floats.
From PS Require Import Syntax Values Interp ProgGlobals Prog Boundary CMain.
Import ListNotations.
Local Open Scope Z_scope.

Definition zero_of (c : ct) : cell :=
  match c with
  | CF64 => KDbl 0%float
  | CPTR | CFILE => KNull
  | CW8 => KWord 0 255
  | CW4 => KWord 0 15
  | _ => KInt 0
  end.

Fixpoint shape_size (s : gshape) : Z :=
  match s with [] => 0 | (n, _) :: r => zi n + shape_size r end.

Fixpoint fill_run (n : nat) (o : Z) (k : cell) (b : block) : block :=
  match n with
  | O => b
  | S n' => match bset b o k with Some b' => fill_run n' (o + 1) k b' | None => b end
  end.

(* a global's block: the first run's zero as the default, the other runs written *)
Definition global_block (s : gshape) : block :=
  match s with
  | [] => new_block 1 (KInt 0)
  | (_, c0) :: _ =>
    let b0 := new_block (shape_size s) (zero_of c0) in
    fst (fold_left (fun (acc : block * Z) (r : int * ct) =>
                      let (b, o) := acc in let (n, c) := r in
                      (if negb (match c, c0 with
                                | CW8, CW8 | CW4, CW4 | CF64, CF64 | CPTR, CPTR | CFILE, CFILE
                                | CPTR, CFILE | CFILE, CPTR => true
                                | CU8, CU8 | CS8, CS8 | CS16, CS16 | CU16, CU16 | CI32, CI32 | CI64, CI64
                                | CC8, CC8 => true
                                | _, _ => false end)
                       then fill_run (Z.to_nat (zi n)) o (zero_of c) b else b, o + zi n)) s (b0, 0))
  end.

Definition string_block (bytes : list int) : block :=
  let n := Z.of_nat (List.length bytes) + 1 in
  fst (fold_left (fun (acc : block * Z) (c : int) => let (b, o) := acc in
                    (match bset b o (KInt (zi c)) with Some b' => b' | None => b end, o + 1))
                 bytes (new_block n (KInt 0), 0)).

Definition nglobals : Z := Z.of_nat (List.length globals).

Definition procs_array : array proc :=
  fst (fold_left (fun (acc : array proc * Z) (p : proc) => let (a, i) := acc in
                    (PArray.set a (Uint63.of_Z i) p, i + 1))
                 procs (PArray.make (Uint63.of_Z (Z.of_nat (List.length procs))) (mkproc [] 1%uint63 None SSkip), 0)).

Definition initial_heap : array block * Z :=
  let h0 := PArray.make (Uint63.of_Z heap_cap) empty_block in
  let (h1, g) := fold_left (fun (acc : array block * Z) (s : gshape) => let (h, i) := acc in
                              (PArray.set h (Uint63.of_Z i) (global_block s), i + 1)) globals (h0, 0) in
  fold_left (fun (acc : array block * Z) (s : list int) => let (h, i) := acc in
               (PArray.set h (Uint63.of_Z i) (string_block s), i + 1)) strings (h1, g).

Definition initial_state (x : io) : state :=
  let (h, next) := initial_heap in
  (* C main's writes, measured (CMain.v) *)
  cmain (mkst h next frame_base frame_base x).

Definition run (fuel : nat) (x : io) : eres :=
  callp procs_array nglobals ext fuel P_mainbody [] (initial_state x).
