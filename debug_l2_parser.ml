(* Debug L2 Parser *)

open Lexer_v25
open L1_expander
open L2_parser

let () =
  (* Test simple text *)
  let text = "Hello world!" in
  Printf.printf "Input: %s\n" text;
  
  (* Tokenize *)
  let tokens = L0_lexer_track_a_arena.tokenize text in
  Printf.printf "L0 tokens (%d):\n" (List.length tokens);
  List.iteri (fun i tok ->
    Printf.printf "  [%d] %s\n" i (token_to_string tok)
  ) tokens;
  
  (* Expand (no macros, so should be identity) *)
  let l1_state = L1_expander.initial_state () in
  let expanded = L1_expander.expand_tokens l1_state tokens in
  Printf.printf "\nL1 tokens (%d):\n" (List.length expanded.tokens);
  List.iteri (fun i tok ->
    Printf.printf "  [%d] %s\n" i (token_to_string tok)
  ) expanded.tokens;
  
  (* Parse *)
  let token_array = Array.of_list expanded.tokens in
  let doc = L2_parser.parse token_array in
  
  Printf.printf "\nParsed document:\n";
  Format.printf "%a@." L2_parser.pp_document doc