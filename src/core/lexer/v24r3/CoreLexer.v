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

(* Implementation of lexing functions based on functional approach *)

(* Convert byte to ascii for compatibility with LatexLexer *)
Definition byte_to_ascii (b : byte) : ascii :=
  ascii_of_nat (N.to_nat b).

(* Simple token conversion - maps only compatible tokens *)
Definition simple_token_of_ascii (a : ascii) : token :=
  match a with
  | "010"%char => TNewline       (* newline *)
  | " "%char => TSpace           (* space *)
  | "\"%char => TCommand "\"     (* backslash - basic command marker *)
  | _ => TChar a                 (* regular character *)
  end.

(* Convert byte list to token list using simple character-level lexing *)
Fixpoint lex_bytes_simple (bs : list byte) : list token :=
  match bs with
  | nil => nil
  | b :: rest => 
      let a := byte_to_ascii b in
      let tok := simple_token_of_ascii a in
      tok :: lex_bytes_simple rest
  end.

(* Implement lex_bytes with proper signature *)
Definition lex_bytes (st : lexer_state) (bs : list byte) : (list token * lexer_state) :=
  (lex_bytes_simple bs, st).

(* Implement lex_chunk *)
Definition lex_chunk (c : chunk) : (list token * lexer_state) :=
  lex_bytes c.(c_state) c.(c_bytes).

(* Properties we can now prove about lexing *)
Theorem lex_bytes_nil : lex_bytes init_state nil = (nil, init_state).
Proof.
  unfold lex_bytes, lex_bytes_simple.
  reflexivity.
Qed.

Theorem lex_bytes_app : forall st bs1 bs2,
  let '(toks1, st1) := lex_bytes st bs1 in
  let '(toks2, st2) := lex_bytes st1 bs2 in
  lex_bytes st (bs1 ++ bs2) = (toks1 ++ toks2, st2).
Proof.
  intros st bs1 bs2.
  unfold lex_bytes.
  simpl.
  (* Since lex_bytes doesn't modify state, st1 = st2 = st *)
  f_equal.
  (* Now prove lex_bytes_simple (bs1 ++ bs2) = lex_bytes_simple bs1 ++ lex_bytes_simple bs2 *)
  induction bs1 as [| b1 bs1' IH].
  - simpl. reflexivity.
  - simpl. f_equal. exact IH.
Qed.

(* Helper to convert string to byte list *)
Definition list_of_string (s : string) : list byte :=
  map (fun a => N.of_nat (nat_of_ascii a)) (list_ascii_of_string s).

(* Helper for repeat *)
Fixpoint repeat {A : Type} (x : A) (n : nat) : list A :=
  match n with
  | 0 => nil
  | S n' => x :: repeat x n'
  end.