(** Verified Lexer - Bridge between extracted Coq code and v25 system
    
    This module wraps the extracted verified lexer and adapts it to the
    v25 architecture, replacing lexer_stub.ml with formally verified code.
*)

open Types

(* Note: This file should be compiled with extracted_lexer.ml in scope *)
(* For now, we'll create type definitions that match the extracted types *)

(** Convert between our Types.token and extracted latex_token *)
let token_of_latex_token : Extracted.latex_token -> Types.token = function
  | Extracted.TText s -> TText (String.of_seq (List.to_seq s))
  | Extracted.TCommand s -> TCommand (String.of_seq (List.to_seq s))
  | Extracted.TMathShift -> TMathShift
  | Extracted.TBeginGroup -> TBeginGroup
  | Extracted.TEndGroup -> TEndGroup
  | Extracted.TSpace -> TSpace
  | Extracted.TNewline -> TNewline
  | Extracted.TComment s -> TComment (String.of_seq (List.to_seq s))
  | Extracted.TEOF -> TEOF

let latex_token_of_token : Types.token -> Extracted.latex_token = function
  | TText s -> Extracted.TText (List.of_seq (String.to_seq s))
  | TCommand s -> Extracted.TCommand (List.of_seq (String.to_seq s))
  | TMathShift -> Extracted.TMathShift
  | TBeginGroup -> Extracted.TBeginGroup
  | TEndGroup -> Extracted.TEndGroup
  | TSpace -> Extracted.TSpace
  | TNewline -> Extracted.TNewline
  | TComment s -> Extracted.TComment (List.of_seq (String.to_seq s))
  | TEOF -> Extracted.TEOF

(** Convert between string and char list *)
let char_list_of_string s = List.of_seq (String.to_seq s)
let string_of_char_list chars = String.of_seq (List.to_seq chars)

(** Verified lexer state compatible with v25 architecture *)
type lexer_state = {
  buffer : string;
  position : position;
  verified_state : Extracted.lexer_state option; (* Internal extracted state *)
}

(** Initial state using verified implementation *)
let initial_state = {
  buffer = "";
  position = { byte_offset = 0; line = 1; column = 0 };
  verified_state = None;
}

(** Initialize with input *)
let init_with_input input = {
  buffer = input;
  position = { byte_offset = 0; line = 1; column = 0 };
  verified_state = Some (Extracted.initial_state (char_list_of_string input));
}

(** Main lexing function using verified implementation *)
let lex_string (input : string) : Types.token list =
  let char_list = char_list_of_string input in
  let latex_tokens = Extracted.lex_from_string char_list in
  List.map token_of_latex_token latex_tokens

(** Lex from bytes (v25 interface) *)
let lex_bytes (bytes : bytes) : Types.token array * lexer_state =
  let input = Bytes.to_string bytes in
  let tokens = lex_string input in
  let final_state = {
    buffer = input;
    position = { 
      byte_offset = String.length input; 
      line = 1; (* TODO: calculate from tokens *)
      column = 0; 
    };
    verified_state = None;
  } in
  (Array.of_list tokens, final_state)

(** Chunk-based lexing for v25 *)
let lex_chunk ?(prev : lexer_state option = None) (bytes : bytes) : Types.token array * lexer_state =
  lex_bytes bytes

(** Performance: this is now formally verified code! *)
let benchmark_verified_performance () =
  let test_input = "\\documentclass{article}\\begin{document}Hello \\LaTeX{} world!\\end{document}" in
  let start_time = Unix.gettimeofday () in
  let tokens = lex_string test_input in
  let end_time = Unix.gettimeofday () in
  let elapsed_us = (end_time -. start_time) *. 1_000_000. in
  Printf.printf "Verified lexer: %d chars -> %d tokens in %.0fμs (%.1f chars/μs)\n"
    (String.length test_input) (List.length tokens) elapsed_us 
    (float (String.length test_input) /. elapsed_us);
  (tokens, elapsed_us)