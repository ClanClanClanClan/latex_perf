(** Debug Math Parsing - LaTeX Perfectionist v25 *)

open Lexer_v25
open L1_expander
open L2_parser

let debug_inline_math () =
  Printf.printf "=== DEBUGGING INLINE MATH PARSING ===\n\n";
  
  let test_input = "The equation $x + y = z$ is simple." in
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
              Printf.printf "    [%02d] Text(\"%s\")\n" j s
          | Space -> 
              Printf.printf "    [%02d] Space\n" j
          | MathInline content ->
              Printf.printf "    [%02d] MathInline with %d elements\n" j (List.length content)
          | Command { name; _ } ->
              Printf.printf "    [%02d] Command(\"%s\")\n" j name
          | _ -> 
              Printf.printf "    [%02d] Other inline type\n" j
        ) inlines
    | _ ->
        Printf.printf "  body[%d]: Non-paragraph block\n" i
  ) doc.body;
  
  (* Test expectation analysis *)
  Printf.printf "\nTEST EXPECTATION ANALYSIS:\n";
  match doc.body with
  | [Paragraph inlines] ->
      Printf.printf "✓ Got single paragraph with %d inline elements\n" (List.length inlines);
      
      let has_math = List.exists (function MathInline _ -> true | _ -> false) inlines in
      if has_math then
        Printf.printf "✅ FOUND inline math elements\n"
      else
        Printf.printf "❌ NO inline math elements found\n";
      
      Printf.printf "\nDetailed inline analysis:\n";
      List.iteri (fun i inline ->
        match inline with
        | MathInline content ->
            Printf.printf "  inline[%d]: MathInline found with %d content elements\n" i (List.length content)
        | Text s when String.contains s '$' ->
            Printf.printf "  inline[%d]: Text contains $ character: \"%s\"\n" i s
        | Text s ->
            Printf.printf "  inline[%d]: Regular text: \"%s\"\n" i s
        | _ ->
            Printf.printf "  inline[%d]: Other type\n" i
      ) inlines
  | _ ->
      Printf.printf "❌ WRONG STRUCTURE: Expected single paragraph\n"

let debug_display_math () =
  Printf.printf "\n\n=== DEBUGGING DISPLAY MATH PARSING ===\n\n";
  
  let test_input = "\\[\n  E = mc^2\n\\]" in
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
    | MathDisplay content ->
        Printf.printf "  body[%d]: MathDisplay with %d content elements\n" i (List.length content)
    | Paragraph inlines ->
        Printf.printf "  body[%d]: Paragraph with %d inline elements\n" i (List.length inlines)
    | _ ->
        Printf.printf "  body[%d]: Other block type\n" i
  ) doc.body;
  
  (* Test expectation analysis *)
  Printf.printf "\nTEST EXPECTATION ANALYSIS:\n";
  match doc.body with
  | [MathDisplay _] ->
      Printf.printf "✅ PERFECT MATCH: Found MathDisplay block\n"
  | blocks ->
      Printf.printf "❌ MISMATCH: Got %d blocks, expected 1 MathDisplay\n" (List.length blocks)

let () = 
  debug_inline_math ();
  debug_display_math ()