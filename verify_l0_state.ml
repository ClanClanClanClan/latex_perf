(* Minimal verification of L0 state - let's see what actually works *)

(* First, check if the arena lexer exists and has our fixes *)
let check_arena_lexer () =
  Printf.printf "=== CHECKING L0 ARENA LEXER STATE ===\n";
  
  (* Check if the module exists *)
  try
    let module L = L0_lexer_track_a_arena in
    Printf.printf "✅ L0_lexer_track_a_arena module exists\n";
    
    (* Check if StringOps has our additions *)
    let _ = L.StringOps.macro_table in
    Printf.printf "✅ StringOps.macro_table exists\n";
    
    let _ = L.StringOps.reverse_macro_table in  
    Printf.printf "✅ StringOps.reverse_macro_table exists\n";
    
    (* Check if initialize_builtin_macros exists *)
    let _ = L.StringOps.initialize_builtin_macros in
    Printf.printf "✅ StringOps.initialize_builtin_macros exists\n";
    
    (* Check if initialized flag exists *)
    let _ = !L.initialized in
    Printf.printf "✅ initialized flag exists\n";
    
    true
  with e ->
    Printf.printf "❌ ERROR: %s\n" (Printexc.to_string e);
    false

(* Test basic tokenization *)
let test_simple_tokenization () =
  Printf.printf "\n=== TESTING SIMPLE TOKENIZATION ===\n";
  
  (* Very simple test *)
  let input = "abc" in
  Printf.printf "Input: '%s'\n" input;
  
  try
    let packed = L0_lexer_track_a_arena.tokenize_arena input in
    Printf.printf "✅ tokenize_arena works, produced %d packed tokens\n" (Array.length packed);
    
    (* Try to convert to regular tokens *)
    let tokens = L0_lexer_track_a_arena.convert_packed_tokens packed in
    Printf.printf "✅ convert_packed_tokens works, produced %d tokens\n" (List.length tokens);
    
    (* Check token types *)
    List.iter (function
      | Lexer_v25.TChar (c, _) -> 
          Printf.printf "  Token: TChar('%c')\n" (Uchar.to_char c)
      | Lexer_v25.TMacro name ->
          Printf.printf "  Token: TMacro(\"%s\")\n" name
      | _ -> Printf.printf "  Token: Other\n"
    ) tokens;
    
    true
  with e ->
    Printf.printf "❌ Tokenization failed: %s\n" (Printexc.to_string e);
    false

(* Test macro recognition *)
let test_macro_recognition () =
  Printf.printf "\n=== TESTING MACRO RECOGNITION ===\n";
  
  (* Initialize macros if not done *)
  if not !L0_lexer_track_a_arena.initialized then begin
    Printf.printf "Initializing built-in macros...\n";
    L0_lexer_track_a_arena.StringOps.macro_counter := 0;
    Hashtbl.clear L0_lexer_track_a_arena.StringOps.macro_table;
    Hashtbl.clear L0_lexer_track_a_arena.StringOps.reverse_macro_table;
    L0_lexer_track_a_arena.StringOps.initialize_builtin_macros ();
    L0_lexer_track_a_arena.initialized := true;
    Printf.printf "✅ Initialization complete\n"
  end;
  
  (* Check what's in the macro table *)
  Printf.printf "Macro table size: %d\n" (Hashtbl.length L0_lexer_track_a_arena.StringOps.macro_table);
  
  (* Check specific macros *)
  let check_macro name =
    if Hashtbl.mem L0_lexer_track_a_arena.StringOps.macro_table name then
      Printf.printf "  ✅ Macro '%s' is registered\n" name
    else
      Printf.printf "  ❌ Macro '%s' is MISSING\n" name
  in
  
  check_macro "[";
  check_macro "]";
  check_macro "LaTeX";
  check_macro "section";
  check_macro "alpha";
  
  (* Test tokenizing with macros *)
  Printf.printf "\nTesting display math tokenization:\n";
  let input = "\\[x\\]" in
  Printf.printf "Input: '%s'\n" input;
  
  try
    let tokens = L0_lexer_track_a_arena.tokenize input in
    Printf.printf "Tokens produced: %d\n" (List.length tokens);
    
    List.iteri (fun i tok ->
      match tok with
      | Lexer_v25.TMacro name ->
          Printf.printf "  [%d] TMacro(\"%s\") %s\n" i name 
            (if name = "[" || name = "]" then "← DISPLAY MATH!" else "")
      | Lexer_v25.TChar (c, _) ->
          Printf.printf "  [%d] TChar('%c')\n" i (Uchar.to_char c)
      | _ -> Printf.printf "  [%d] Other\n" i
    ) tokens;
    
    (* Check if we found the macros *)
    let found_macros = List.fold_left (fun acc tok ->
      match tok with
      | Lexer_v25.TMacro name -> name :: acc
      | _ -> acc
    ) [] tokens in
    
    if List.mem "[" found_macros && List.mem "]" found_macros then
      Printf.printf "✅ Display math macros recognized!\n"
    else
      Printf.printf "❌ Display math macros NOT recognized\n"
      
  with e ->
    Printf.printf "❌ Error: %s\n" (Printexc.to_string e)

(* Quick performance check *)
let test_performance () =
  Printf.printf "\n=== QUICK PERFORMANCE CHECK ===\n";
  
  (* Create a test document *)
  let size = 100_000 in (* 100KB for quick test *)
  let doc = String.make size 'a' in
  Printf.printf "Test document: %d bytes\n" size;
  
  try
    let start = Unix.gettimeofday () in
    let _ = L0_lexer_track_a_arena.tokenize doc in
    let stop = Unix.gettimeofday () in
    let elapsed_ms = (stop -. start) *. 1000.0 in
    
    Printf.printf "Time for %dKB: %.2f ms\n" (size/1000) elapsed_ms;
    Printf.printf "Extrapolated to 1.1MB: ~%.2f ms\n" (elapsed_ms *. 11.0);
    
    if elapsed_ms *. 11.0 <= 220.0 then
      Printf.printf "✅ Performance looks reasonable\n"
    else
      Printf.printf "⚠️ Performance may be slower than expected\n"
      
  with e ->
    Printf.printf "❌ Performance test failed: %s\n" (Printexc.to_string e)

(* Main *)
let () =
  Printf.printf "\n";
  Printf.printf "=====================================\n";
  Printf.printf "L0 ARENA LEXER STATE VERIFICATION\n";
  Printf.printf "=====================================\n\n";
  
  if check_arena_lexer () then begin
    test_simple_tokenization () |> ignore;
    test_macro_recognition ();
    test_performance ()
  end;
  
  Printf.printf "\n=====================================\n";
  Printf.printf "END VERIFICATION\n";
  Printf.printf "=====================================\n"