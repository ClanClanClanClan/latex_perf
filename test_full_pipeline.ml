open Printf

(* Test the complete L0→L1→L2 pipeline with our fixes *)

let test_pipeline () =
  printf "=== L0→L1→L2 PIPELINE TEST ===\n\n";
  
  (* Initialize L0 if needed *)
  if not !L0_lexer_track_a_arena.initialized then begin
    printf "Initializing L0 built-in macros...\n";
    L0_lexer_track_a_arena.StringOps.initialize_builtin_macros ();
    L0_lexer_track_a_arena.initialized := true
  end;
  
  let test_cases = [
    ("Simple text", "Hello world!");
    ("Inline math", "The equation $x + y = z$ is simple.");
    ("Display math", "\\[E = mc^2\\]");
    ("Section", "\\section{Introduction}\nSome text here.");
    ("Mixed", "Text with $inline$ and\\[display\\]math.");
  ] in
  
  test_cases |> List.iter (fun (name, input) ->
    printf "Test: %s\n" name;
    printf "Input: %s\n" input;
    
    try
      (* L0: Tokenize *)
      printf "  L0 Tokenization...\n";
      let l0_tokens = L0_lexer_track_a_arena.tokenize input in
      printf "    → %d tokens\n" (List.length l0_tokens);
      
      (* Show macros found *)
      let macros = List.fold_left (fun acc tok ->
        match tok with
        | Lexer_v25.TMacro name -> name :: acc
        | _ -> acc
      ) [] l0_tokens |> List.rev in
      if macros <> [] then
        printf "    → Macros: %s\n" (String.concat ", " macros);
      
      (* L1: Expand *)
      printf "  L1 Expansion...\n";
      let l1_state = L1_v25.create_initial_state () in
      let expanded = L1_v25.expand_tokens l1_state l0_tokens in
      printf "    → %d tokens after expansion\n" (List.length expanded.tokens);
      
      (* Check if display math macros survived *)
      let expanded_macros = List.fold_left (fun acc tok ->
        match tok with
        | Lexer_v25.TMacro name -> name :: acc
        | _ -> acc
      ) [] expanded.tokens |> List.rev in
      if expanded_macros <> macros then
        printf "    → Macros changed: %s\n" (String.concat ", " expanded_macros);
      
      (* L2: Parse *)
      printf "  L2 Parsing...\n";
      let ast = L2_parser.parse_tokens expanded.tokens in
      printf "    → AST: %s\n" (L2_parser.ast_to_string ast);
      
      (* Check result *)
      let success = match name, ast with
        | "Display math", [L2_parser.MathDisplay _] -> true
        | "Inline math", [L2_parser.Paragraph inlines] ->
            List.exists (function L2_parser.MathInline _ -> true | _ -> false) inlines
        | "Section", [L2_parser.Section _] -> true
        | _ -> List.length ast > 0
      in
      
      if success then
        printf "  ✅ SUCCESS\n"
      else
        printf "  ❌ UNEXPECTED RESULT\n";
        
    with e ->
      printf "  ❌ ERROR: %s\n" (Printexc.to_string e);
      
    printf "\n"
  )

let test_display_math_detailed () =
  printf "=== DETAILED DISPLAY MATH TEST ===\n\n";
  
  let input = "\\[x^2 + y^2 = z^2\\]" in
  printf "Input: %s\n\n" input;
  
  (* Step by step *)
  try
    (* L0 *)
    printf "Step 1: L0 Tokenization\n";
    let l0_tokens = L0_lexer_track_a_arena.tokenize input in
    l0_tokens |> List.iteri (fun i tok ->
      match tok with
      | Lexer_v25.TMacro name -> 
          printf "  [%d] TMacro(\"%s\")\n" i name
      | Lexer_v25.TChar (c, cat) ->
          let ch = try Char.chr (Uchar.to_int c) with _ -> '?' in
          printf "  [%d] TChar('%c', %s)\n" i ch (Catcode.catcode_to_string cat)
      | _ -> printf "  [%d] Other\n" i
    );
    
    (* Check critical macros *)
    let has_lbrack = List.exists (function 
      | Lexer_v25.TMacro "[" -> true | _ -> false) l0_tokens in
    let has_rbrack = List.exists (function
      | Lexer_v25.TMacro "]" -> true | _ -> false) l0_tokens in
    
    if has_lbrack && has_rbrack then
      printf "✅ Display math macros found in L0 output\n\n"
    else begin
      printf "❌ Display math macros MISSING from L0 output\n";
      printf "Cannot continue with pipeline test\n";
      exit 1
    end;
    
    (* L1 *)
    printf "Step 2: L1 Expansion\n";
    let l1_state = L1_v25.create_initial_state () in
    let expanded = L1_v25.expand_tokens l1_state l0_tokens in
    printf "  Expanded to %d tokens\n" (List.length expanded.tokens);
    
    (* L2 *)
    printf "\nStep 3: L2 Parsing\n";
    let ast = L2_parser.parse_tokens expanded.tokens in
    printf "  AST: %s\n" (L2_parser.ast_to_string ast);
    
    match ast with
    | [L2_parser.MathDisplay content] ->
        printf "✅ SUCCESSFULLY parsed as display math!\n";
        printf "  Content has %d elements\n" (List.length content)
    | _ ->
        printf "❌ FAILED to parse as display math\n";
        printf "  Got: %s\n" (L2_parser.ast_to_string ast)
        
  with e ->
    printf "❌ Pipeline error: %s\n" (Printexc.to_string e);
    printf "  %s\n" (Printexc.get_backtrace ())

let () =
  printf "\n";
  printf "=====================================\n";
  printf "FULL L0→L1→L2 PIPELINE TEST\n";
  printf "=====================================\n\n";
  
  test_pipeline ();
  printf "\n";
  test_display_math_detailed ();
  
  printf "\n=====================================\n"