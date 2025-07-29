(** Verified Bridge - Integration between extracted Coq code and v25 system
    
    This module provides the bridge between the extracted verified lexer
    and the v25 architecture.
*)

open Types

(* Extracted types - copied from extracted_lexer.ml *)
type latex_token =
| TCommand of char list
| TBeginGroup
| TEndGroup
| TMathShift
| TAlignment
| TParameter
| TSuperscript
| TSubscript
| TText of char list
| TSpace
| TComment of char list
| TNewline
| TEOF

(** Convert between our Types.token and extracted latex_token *)
let token_of_latex_token : latex_token -> Types.token = function
  | TText chars -> TText (String.of_seq (List.to_seq chars))
  | TCommand chars -> TCommand (String.of_seq (List.to_seq chars))
  | TMathShift -> TMathShift
  | TBeginGroup -> TBeginGroup
  | TEndGroup -> TEndGroup
  | TSpace -> TSpace
  | TNewline -> TNewline
  | TComment chars -> TComment (String.of_seq (List.to_seq chars))
  | TEOF -> TEOF
  | TAlignment -> TSpace (* Map to closest equivalent *)
  | TParameter -> TText "#" (* Map to text representation *)
  | TSuperscript -> TText "^"
  | TSubscript -> TText "_"

(** Convert string to char list for extracted functions *)
let char_list_of_string s = List.of_seq (String.to_seq s)

(** Integration with extracted verified lexer - will be linked at compile time *)
external verified_lex_from_string : char list -> latex_token list = "verified_lex_from_string"

(** Main verified lexing function *)
let lex_verified (input : string) : Types.token list =
  let char_list = char_list_of_string input in
  let latex_tokens = verified_lex_from_string char_list in
  List.map token_of_latex_token latex_tokens

(** Performance test with verified implementation *)
let test_verified_performance () =
  let test_input = "\\documentclass{article}\\begin{document}Hello \\LaTeX{} world!\\end{document}" in
  let start_time = Unix.gettimeofday () in
  let tokens = lex_verified test_input in
  let end_time = Unix.gettimeofday () in
  let elapsed_us = (end_time -. start_time) *. 1_000_000. in
  Printf.printf "🔥 VERIFIED LEXER: %d chars -> %d tokens in %.0fμs (%.1f chars/μs)\n"
    (String.length test_input) (List.length tokens) elapsed_us 
    (float (String.length test_input) /. elapsed_us);
  (tokens, elapsed_us)