(** Debug Character Coalescing - LaTeX Perfectionist v25 *)

open Lexer_v25
open L1_expander
open L2_parser

let debug_coalescing () =
  Printf.printf "=== DEBUGGING CHARACTER COALESCING ===\n\n";
  
  let test_input = "Hello world!" in
  Printf.printf "Input text: \"%s\"\n\n" test_input;
  
  (* Step 1: Tokenization *)
  let tokens = L0_lexer_track_a_arena.tokenize test_input in
  Printf.printf "L0 TOKENS (%d total):\n" (List.length tokens);
  List.iteri (fun i token ->
    Printf.printf "  [%02d] %s\n" i (Lexer_v25.token_to_string token)
  ) tokens;
  
  (* Step 2: L1 Expansion *)
  let l1_state = L1_expander.initial_state () in
  let expanded = L1_expander.expand_tokens l1_state tokens in
  Printf.printf "\nL1 EXPANDED TOKENS (%d total):\n" (List.length expanded.tokens);
  List.iteri (fun i token ->
    Printf.printf "  [%02d] %s\n" i (Lexer_v25.token_to_string token)
  ) expanded.tokens;
  
  (* Step 3: L2 Parsing *)
  let token_array = Array.of_list expanded.tokens in
  Printf.printf "\nL2 PARSING:\n";
  Printf.printf "Token array length: %d\n" (Array.length token_array);
  
  let doc = L2_parser.parse token_array in
  Printf.printf "Parsed document with %d body items\n\n" (List.length doc.body);
  
  (* Analyze the result *)
  Printf.printf "DOCUMENT STRUCTURE:\n";
  List.iteri (fun i block ->
    match block with
    | Paragraph inlines ->
        Printf.printf "  body[%d]: Paragraph with %d inline elements\n" i (List.length inlines);
        List.iteri (fun j inline ->
          match inline with
          | Text s -> 
              Printf.printf "    [%02d] Text(\"%s\") - length %d\n" j s (String.length s)
          | Space -> 
              Printf.printf "    [%02d] Space\n" j
          | _ -> 
              Printf.printf "    [%02d] Other inline type\n" j
        ) inlines
    | _ ->
        Printf.printf "  body[%d]: Non-paragraph block\n" i
  ) doc.body;
  
  (* Test expectation analysis *)
  Printf.printf "\nTEST EXPECTATION ANALYSIS:\n";
  let expected_individual_chars = [
    "H"; "e"; "l"; "l"; "o"; 
    "w"; "o"; "r"; "l"; "d"; "!"
  ] in
  
  match doc.body with
  | [Paragraph inlines] ->
      Printf.printf "✓ Got single paragraph with %d inline elements\n" (List.length inlines);
      
      (* Check if matches individual character expectation *)
      let rec check_individual_chars inlines expected_chars has_space =
        match inlines, expected_chars with
        | [], [] -> 
            Printf.printf "✅ PERFECT MATCH: Individual character pattern\n"
        | Space :: rest_inlines, expected when not has_space ->
            check_individual_chars rest_inlines expected true
        | Text s :: rest_inlines, expected_char :: rest_expected when s = expected_char ->
            check_individual_chars rest_inlines rest_expected has_space
        | Text s :: _, expected_char :: _ when s <> expected_char ->
            Printf.printf "❌ MISMATCH: Expected Text(\"%s\"), got Text(\"%s\")\n" expected_char s
        | Text s :: _, [] ->
            Printf.printf "❌ EXTRA: Unexpected Text(\"%s\")\n" s
        | [], expected_char :: _ ->
            Printf.printf "❌ MISSING: Expected Text(\"%s\")\n" expected_char
        | _ ->
            Printf.printf "❌ STRUCTURE MISMATCH: Unexpected inline type\n"
      in
      
      Printf.printf "Checking individual character pattern...\n";
      check_individual_chars inlines expected_individual_chars false;
      
      (* Check if matches coalesced text expectation *)
      Printf.printf "\nChecking coalesced text pattern...\n";
      (match inlines with
      | [Text "Hello"; Space; Text "world!"] ->
          Printf.printf "✅ PERFECT MATCH: Coalesced text pattern\n"
      | [Text full_text] when full_text = "Hello world!" ->
          Printf.printf "✅ PERFECT MATCH: Fully coalesced text pattern\n"
      | _ ->
          Printf.printf "❌ NO MATCH: Neither coalesced pattern works\n")
  | _ ->
      Printf.printf "❌ WRONG STRUCTURE: Expected single paragraph\n"
  
let () = debug_coalescing ()