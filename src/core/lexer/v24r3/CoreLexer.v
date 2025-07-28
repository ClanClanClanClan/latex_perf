(* CoreLexer.v - Base types for v24-R3 incremental lexer *)
(* This provides the foundation types needed by the v24-R3 proof files *)

Require Import List.
Require Import Ascii.
Require Import String.
Require Import ZArith.
Require Import NArith.

(* Basic byte type *)
Definition byte := N.

(* Conversion helpers *)
Definition byte_of_nat (n : nat) : byte := N.of_nat n.
Definition Byte := N.

Module Byte.
  Definition x00 : byte := 0%N.
  Definition x01 : byte := 1%N.
  Definition of_N (n : N) : byte := n.
  Definition to_N (b : byte) : N := b.
End Byte.

(* Token types *)
Inductive token : Type :=
  | TChar : ascii -> token
  | TCommand : string -> token
  | TNewline : token
  | TSpace : token
  | TMath : token
  | TComment : string -> token
  | TBeginEnv : string -> token
  | TEndEnv : string -> token
  | TError : string -> token.

(* Lexer modes *)
Inductive mode : Type :=
  | MNormal : mode
  | MMath : mode
  | MComment : mode
  | MVerbatim : mode.

(* Lexer state *)
Record lexer_state : Type := mkLexerState {
  line_no : nat;
  col_no : nat;
  in_math : bool;
  in_comment : bool;
  in_verbatim : bool;
  mode_stack : list mode
}.

(* Initial state *)
Definition init_state : lexer_state :=
  mkLexerState 0 0 false false false nil.

(* Chunk type for incremental processing *)
Record chunk : Type := mkChunk {
  c_state : lexer_state;
  c_bytes : list byte
}.

(* Stub lexing functions - these would be implemented in the real lexer *)
Parameter lex_bytes : lexer_state -> list byte -> (list token * lexer_state).
Parameter lex_chunk : chunk -> (list token * lexer_state).

(* Properties we assume about lexing *)
Axiom lex_bytes_nil : lex_bytes init_state nil = (nil, init_state).
Axiom lex_bytes_app : forall st bs1 bs2,
  let '(toks1, st1) := lex_bytes st bs1 in
  let '(toks2, st2) := lex_bytes st1 bs2 in
  lex_bytes st (bs1 ++ bs2) = (toks1 ++ toks2, st2).

(* Helper to convert string to byte list *)
Definition list_of_string (s : string) : list byte :=
  map (fun a => N.of_nat (nat_of_ascii a)) (list_ascii_of_string s).

(* Helper for repeat *)
Fixpoint repeat {A : Type} (x : A) (n : nat) : list A :=
  match n with
  | 0 => nil
  | S n' => x :: repeat x n'
  end.