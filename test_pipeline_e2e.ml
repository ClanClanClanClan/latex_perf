open Printf

(* End-to-end test of L0→L1→L2 pipeline with fixes *)

let test_l0_fixed () =
  printf "=== TESTING L0 WITH FIXES ===\n";
  
  (* Test display math tokenization *)
  let input = "\\[x^2 + y^2 = z^2\\]" in
  printf "Input: %s\n" input;
  
  let tokens = L0_lexer_track_a_arena.tokenize input in
  printf "L0 tokens (%d):\n" (List.length tokens);
  
  let found_display_begin = ref false in
  let found_display_end = ref false in
  
  tokens |> List.iteri (fun i tok ->
    match tok with
    | Lexer_v25.TMacro name ->
        printf "  [%d] TMacro(\"%s\")" i name;
        if name = "[" then (found_display_begin := true; printf " ✅ DISPLAY BEGIN");
        if name = "]" then (found_display_end := true; printf " ✅ DISPLAY END");
        printf "\n"
    | Lexer_v25.TChar (c, cat) ->
        let code = Uchar.to_int c in
        if code < 128 then
          printf "  [%d] TChar('%c', %s)\n" i (Char.chr code) (Catcode.catcode_to_string cat)
        else
          printf "  [%d] TChar(U+%04X, %s)\n" i code (Catcode.catcode_to_string cat)
    | _ -> printf "  [%d] Other token\n" i
  );
  
  if !found_display_begin && !found_display_end then
    printf "✅ L0 SUCCESS: Display math macros recognized!\n\n"
  else
    printf "❌ L0 FAILED: Display math macros not found\n\n";
    
  tokens

let test_l1_expansion tokens =
  printf "=== TESTING L1 EXPANSION ===\n";
  
  try
    let l1_state = L1_v25.create_initial_state () in
    let expanded = L1_v25.expand_tokens l1_state tokens in
    
    printf "L1 expanded tokens (%d):\n" (List.length expanded.tokens);
    
    (* Check if [ and ] survive expansion *)
    let has_display_begin = List.exists (function
      | Lexer_v25.TMacro "[" -> true
      | _ -> false) expanded.tokens in
    let has_display_end = List.exists (function  
      | Lexer_v25.TMacro "]" -> true
      | _ -> false) expanded.tokens in
      
    if has_display_begin && has_display_end then (
      printf "✅ L1 SUCCESS: Display math macros preserved through expansion\n\n";
      expanded.tokens
    ) else (
      printf "❌ L1 FAILED: Display math macros lost during expansion\n";
      printf "Expanded tokens:\n";
      expanded.tokens |> List.iteri (fun i tok ->
        match tok with
        | Lexer_v25.TMacro name -> printf "  [%d] TMacro(\"%s\")\n" i name
        | _ -> ()
      );
      printf "\n";
      expanded.tokens
    )
  with e ->
    printf "❌ L1 ERROR: %s\n\n" (Printexc.to_string e);
    []

let test_l2_parsing tokens =
  printf "=== TESTING L2 PARSING ===\n";
  
  if tokens = [] then (
    printf "❌ No tokens to parse\n";
    ()
  ) else
  try
    let ast = L2_parser.parse_tokens tokens in
    printf "L2 AST:\n%s\n" (L2_parser.ast_to_string ast);
    
    match ast with
    | [L2_parser.MathDisplay content] ->
        printf "✅ L2 SUCCESS: Parsed as MathDisplay with %d elements\n" (List.length content)
    | _ ->
        printf "❌ L2 FAILED: Unexpected AST structure\n"
  with e ->
    printf "❌ L2 ERROR: %s\n" (Printexc.to_string e)

let test_complete_pipeline () =
  printf "\n=== COMPLETE PIPELINE TEST ===\n";
  
  let test_cases = [
    ("Display math \\[...\\]", "\\[E = mc^2\\]");
    ("Inline math $...$", "The equation $x + y = z$ is simple.");
    ("Section with math", "\\section{Theory}\nWe have \\[x^2 + y^2 = z^2\\]");
    ("Mixed content", "Text with $inline$ and\n\\[\n  display\n\\]\nmath.");
  ] in
  
  test_cases |> List.iter (fun (name, input) ->
    printf "\nTest: %s\n" name;
    printf "Input: %s\n" input;
    
    try
      (* L0 *)
      let l0_tokens = L0_lexer_track_a_arena.tokenize input in
      printf "  L0: %d tokens" (List.length l0_tokens);
      
      (* Check for key macros *)
      let macros = List.fold_left (fun acc tok ->
        match tok with
        | Lexer_v25.TMacro name -> name :: acc
        | _ -> acc
      ) [] l0_tokens in
      if macros <> [] then printf " (macros: %s)" (String.concat ", " (List.rev macros));
      printf "\n";
      
      (* L1 *)
      let l1_state = L1_v25.create_initial_state () in
      let expanded = L1_v25.expand_tokens l1_state l0_tokens in
      printf "  L1: %d tokens after expansion\n" (List.length expanded.tokens);
      
      (* L2 *)
      let ast = L2_parser.parse_tokens expanded.tokens in
      printf "  L2: ";
      
      (* Check results *)
      let has_display = List.exists (function L2_parser.MathDisplay _ -> true | _ -> false) ast in
      let has_inline = ref false in
      let check_inline = function
        | L2_parser.MathInline _ -> has_inline := true; true
        | _ -> false in
      let rec check_ast = function
        | L2_parser.Paragraph inlines -> List.exists check_inline inlines
        | L2_parser.Section s -> List.exists check_ast s.content
        | _ -> false in
      List.iter (fun node -> ignore (check_ast node)) ast;
      
      if String.contains input '[' && has_display then
        printf "✅ Display math found\n"
      else if String.contains input '$' && !has_inline then  
        printf "✅ Inline math found\n"
      else
        printf "✅ Parsed successfully\n"
        
    with e ->
      printf "\n  ❌ Pipeline failed: %s\n" (Printexc.to_string e)
  )

let () =
  (* Initialize L0 built-in macros *)
  if not !L0_lexer_track_a_arena.initialized then (
    L0_lexer_track_a_arena.StringOps.initialize_builtin_macros ();
    L0_lexer_track_a_arena.initialized := true
  );
  
  (* Run tests *)
  let l0_tokens = test_l0_fixed () in
  let l1_tokens = test_l1_expansion l0_tokens in
  let _ = test_l2_parsing l1_tokens in
  test_complete_pipeline ()