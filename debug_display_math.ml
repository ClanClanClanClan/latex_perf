open Printf

(* Quick standalone debug for display math parsing *)

let debug_display_math () =
  printf "=== DISPLAY MATH DEBUG ===\n";
  let test_input = "\\[x^2 + y^2 = z^2\\]" in
  printf "Input: %s\n" test_input;
  
  try
    (* Simple tokenization test using L0 lexer *)
    let bytes = Bytes.of_string test_input in
    let arena = L0_lexer_track_a_arena.create_arena 1024 in
    let tokens = L0_lexer_track_a_arena.tokenize_arena bytes 0 (String.length test_input) arena in
    
    printf "Tokens found: %d\n" (List.length tokens);
    tokens |> List.iteri (fun i token ->
      match token with
      | L0_lexer_track_a_arena.TChar (c, cat) -> 
          printf "  [%d] TChar('%c', %s)\n" i c (Catcode.catcode_to_string cat)
      | L0_lexer_track_a_arena.TMacro name -> 
          printf "  [%d] TMacro(\"%s\") <- PROBLEM HERE?\n" i name
      | L0_lexer_track_a_arena.TParam n ->
          printf "  [%d] TParam(%d)\n" i n
      | L0_lexer_track_a_arena.TGroupOpen ->
          printf "  [%d] TGroupOpen\n" i
      | L0_lexer_track_a_arena.TGroupClose ->
          printf "  [%d] TGroupClose\n" i
      | L0_lexer_track_a_arena.TEOF ->
          printf "  [%d] TEOF\n" i
    );
    printf "=== END TOKENIZATION ===\n\n";
    
    (* Test if L2 parser can handle these tokens *)
    printf "=== TESTING L2 PARSER ===\n";
    let ast = L2_parser.parse_tokens tokens in
    match ast with
    | [L2_parser.MathDisplay content] ->
        printf "✅ SUCCESS: Parsed as MathDisplay with %d elements\n" (List.length content)
    | _ ->
        printf "❌ FAILED: Unexpected AST structure\n";
        printf "AST: %s\n" (L2_parser.ast_to_string ast)
    
  with 
  | e -> printf "ERROR: %s\n" (Printexc.to_string e)

let () = debug_display_math ()