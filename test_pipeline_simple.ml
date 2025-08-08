(* Test L0→L1→L2 Pipeline *)

let test_display_math () =
  print_endline "=== TESTING L0→L1→L2 PIPELINE ===\n";
  
  let test_input = "\\[E = mc^2\\]" in
  Printf.printf "Input: %s\n\n" test_input;
  
  try
    (* Step 1: L0 Tokenization *)
    print_endline "Step 1: L0 Tokenization";
    let l0_tokens = L0_lexer_track_a_arena.tokenize test_input in
    Printf.printf "  Tokens: %d\n" (List.length l0_tokens);
    
    (* Check for display math macros *)
    let macros = List.fold_left (fun acc tok ->
      match tok with
      | Lexer_v25.TMacro name -> name :: acc  
      | _ -> acc
    ) [] l0_tokens |> List.rev in
    
    Printf.printf "  Macros found: [%s]\n" (String.concat ", " macros);
    
    if not (List.mem "[" macros && List.mem "]" macros) then begin
      print_endline "  ❌ Display math macros missing!";
      exit 1
    end else
      print_endline "  ✅ Display math macros found";
      
    (* Step 2: L1 Expansion *)
    print_endline "\nStep 2: L1 Expansion";
    let l1_state = L1_v25.create_initial_state () in
    let expanded = L1_v25.expand_tokens l1_state l0_tokens in
    Printf.printf "  Expanded tokens: %d\n" (List.length expanded.L1_v25.tokens);
    
    (* Step 3: L2 Parsing *)
    print_endline "\nStep 3: L2 Parsing";
    let ast = L2_parser.parse_tokens expanded.L1_v25.tokens in
    Printf.printf "  AST nodes: %d\n" (List.length ast);
    
    (* Check result *)
    match ast with
    | [L2_parser.MathDisplay content] ->
        print_endline "  ✅ Successfully parsed as display math!";
        Printf.printf "  Content elements: %d\n" (List.length content)
    | _ ->
        print_endline "  ❌ Failed to parse as display math";
        Printf.printf "  Got: %s\n" (L2_parser.ast_to_string ast)
        
  with e ->
    Printf.printf "❌ Pipeline error: %s\n" (Printexc.to_string e);
    Printf.printf "%s\n" (Printexc.get_backtrace ())

let test_multiple_cases () =
  print_endline "\n=== TESTING MULTIPLE CASES ===\n";
  
  let test_cases = [
    ("Simple text", "Hello world!");
    ("Inline math", "The equation $x + y = z$ is simple.");
    ("Section", "\\section{Introduction}");
    ("Mixed", "Text with $inline$ and \\[display\\] math.");
  ] in
  
  test_cases |> List.iter (fun (name, input) ->
    Printf.printf "Test: %s\n" name;
    Printf.printf "Input: %s\n" input;
    
    try
      let tokens = L0_lexer_track_a_arena.tokenize input in
      let l1_state = L1_v25.create_initial_state () in
      let expanded = L1_v25.expand_tokens l1_state tokens in
      let ast = L2_parser.parse_tokens expanded.L1_v25.tokens in
      
      Printf.printf "  → L0: %d tokens, L1: %d tokens, L2: %d nodes\n"
        (List.length tokens)
        (List.length expanded.L1_v25.tokens)
        (List.length ast);
        
      print_endline "  ✅ Pipeline completed\n"
      
    with e ->
      Printf.printf "  ❌ Error: %s\n\n" (Printexc.to_string e)
  )

let () =
  Printexc.record_backtrace true;
  test_display_math ();
  test_multiple_cases ();
  print_endline "=== END PIPELINE TEST ==="