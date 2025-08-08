(** Debug simple paragraph parsing issue *)

open Lexer_v25
open L1_expander  
open L2_parser

let debug_tokenize_and_expand text =
  Printf.printf "=== DEBUGGING: %s ===\n" text;
  
  (* Step 1: L0 tokenization *)
  let tokens = L0_lexer_track_a_arena.tokenize text in
  Printf.printf "L0 tokens: %d tokens\n" (List.length tokens);
  List.iteri (fun i token ->
    Printf.printf "  [%d] %s\n" i (L0_lexer_track_a_arena.debug_token_to_string token)
  ) tokens;
  
  (* Step 2: L1 expansion *)
  let l1_state = L1_expander.initial_state () in
  let expanded = L1_expander.expand_tokens l1_state tokens in
  Printf.printf "L1 expanded: %d tokens\n" (List.length expanded.tokens);
  List.iteri (fun i token ->
    Printf.printf "  [%d] %s\n" i (L0_lexer_track_a_arena.debug_token_to_string token)
  ) expanded.tokens;
  
  (* Step 3: L2 parsing *)
  let token_array = Array.of_list expanded.tokens in
  let doc = L2_parser.parse token_array in
  
  Printf.printf "L2 parsed document:\n";
  Printf.printf "  preamble: %d items\n" (List.length doc.preamble);
  Printf.printf "  body: %d items\n" (List.length doc.body);
  
  (* Analyze body structure *)
  List.iteri (fun i block ->
    match block with
    | Paragraph inlines ->
        Printf.printf "  body[%d]: Paragraph with %d inlines\n" i (List.length inlines);
        List.iteri (fun j inline ->
          match inline with
          | Text s -> Printf.printf "    inline[%d]: Text \"%s\"\n" j s
          | Space -> Printf.printf "    inline[%d]: Space\n" j
          | Command { name; _ } -> Printf.printf "    inline[%d]: Command \"%s\"\n" j name
          | _ -> Printf.printf "    inline[%d]: Other inline\n" j
        ) inlines
    | Section { title; _ } ->
        Printf.printf "  body[%d]: Section\n" i
    | _ ->
        Printf.printf "  body[%d]: Other block\n" i
  ) doc.body;
  
  (* Test expectation *)
  Printf.printf "\nTest expectation check:\n";
  match doc.body with
  | [Paragraph [Text "H"; Text "e"; Text "l"; Text "l"; Text "o"; 
                Space; Text "w"; Text "o"; Text "r"; Text "l"; Text "d"; Text "!"]] ->
      Printf.printf "  ✅ MATCHES expected individual character pattern\n"
  | [Paragraph inlines] ->
      Printf.printf "  ❌ Got paragraph but wrong inline structure (%d inlines)\n" (List.length inlines);
      Printf.printf "      Expected: 12 items (11 chars + 1 space)\n"
  | _ ->
      Printf.printf "  ❌ Wrong document structure entirely\n"

let () =
  debug_tokenize_and_expand "Hello world!"