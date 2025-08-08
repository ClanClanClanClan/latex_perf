(* ACTUAL L0 TEST - Let's verify our claims *)

open Printf

(* First, let's check if the fixes are actually in the code *)
let test_macro_initialization () =
  printf "=== TESTING L0 MACRO INITIALIZATION ===\n";
  
  (* Check if initialize_builtin_macros exists and works *)
  try
    (* Reset state *)
    L0_lexer_track_a_arena.initialized := false;
    L0_lexer_track_a_arena.StringOps.macro_counter := 0;
    Hashtbl.clear L0_lexer_track_a_arena.StringOps.macro_table;
    Hashtbl.clear L0_lexer_track_a_arena.StringOps.reverse_macro_table;
    
    (* Initialize *)
    L0_lexer_track_a_arena.StringOps.initialize_builtin_macros ();
    L0_lexer_track_a_arena.initialized := true;
    
    (* Check critical macros *)
    let check_macro name expected =
      let exists = Hashtbl.mem L0_lexer_track_a_arena.StringOps.macro_table name in
      printf "  Macro '%s': %s\n" name (if exists then "✅ EXISTS" else "❌ MISSING");
      exists
    in
    
    let critical_macros = [
      check_macro "[" true;
      check_macro "]" true;
      check_macro "LaTeX" true;
      check_macro "section" true;
      check_macro "alpha" true;
    ] in
    
    let total_macros = Hashtbl.length L0_lexer_track_a_arena.StringOps.macro_table in
    printf "  Total macros initialized: %d (expected 78)\n" total_macros;
    
    if List.for_all (fun x -> x) critical_macros && total_macros >= 78 then
      printf "✅ Macro initialization WORKS\n\n"
    else
      printf "❌ Macro initialization BROKEN\n\n"
      
  with e ->
    printf "❌ ERROR: %s\n\n" (Printexc.to_string e)

let test_tokenization () =
  printf "=== TESTING L0 TOKENIZATION ===\n";
  
  (* Test display math tokenization *)
  let test_input = "\\[x^2 + y^2 = z^2\\]" in
  printf "Input: %s\n" test_input;
  
  try
    let tokens = L0_lexer_track_a_arena.tokenize test_input in
    printf "Tokens produced: %d\n" (List.length tokens);
    
    (* Check for display math macros *)
    let found_macros = ref [] in
    tokens |> List.iter (function
      | Lexer_v25.TMacro name -> found_macros := name :: !found_macros
      | _ -> ()
    );
    
    printf "Macros found: %s\n" (String.concat ", " (List.rev !found_macros));
    
    let has_display_begin = List.mem "[" !found_macros in
    let has_display_end = List.mem "]" !found_macros in
    
    if has_display_begin && has_display_end then
      printf "✅ Display math macros RECOGNIZED\n\n"
    else
      printf "❌ Display math macros NOT FOUND\n\n"
      
  with e ->
    printf "❌ ERROR during tokenization: %s\n\n" (Printexc.to_string e)

let test_performance () =
  printf "=== TESTING L0 PERFORMANCE ===\n";
  
  (* Create a 1.1MB test document *)
  let size = 1_100_000 in
  let buffer = Buffer.create size in
  
  (* Generate realistic LaTeX content *)
  Buffer.add_string buffer "\\documentclass{article}\n\\begin{document}\n";
  
  (* Add mixed content to reach ~1.1MB *)
  let words_needed = size / 6 in (* average 6 chars per word *)
  for i = 1 to words_needed do
    if i mod 100 = 0 then Buffer.add_string buffer "\n\n";
    if i mod 1000 = 0 then Buffer.add_string buffer (sprintf "\\section{Section %d}\n" (i/1000));
    if i mod 50 = 0 then Buffer.add_string buffer (sprintf "$x_%d$ " i)
    else Buffer.add_string buffer (sprintf "word%d " i)
  done;
  
  Buffer.add_string buffer "\n\\end{document}\n";
  let doc = Buffer.contents buffer in
  let actual_size = String.length doc in
  printf "Document size: %d bytes\n" actual_size;
  
  try
    (* Warm-up run *)
    let _ = L0_lexer_track_a_arena.tokenize doc in
    
    (* Timed runs *)
    let times = ref [] in
    for run = 1 to 5 do
      let start = Unix.gettimeofday () in
      let tokens = L0_lexer_track_a_arena.tokenize doc in
      let stop = Unix.gettimeofday () in
      let elapsed_ms = (stop -. start) *. 1000.0 in
      times := elapsed_ms :: !times;
      printf "  Run %d: %.2f ms (%d tokens)\n" run elapsed_ms (List.length tokens)
    done;
    
    let sorted_times = List.sort compare !times in
    let p95 = List.nth sorted_times 4 in (* 5th element for P95 *)
    let avg = (List.fold_left (+.) 0.0 !times) /. 5.0 in
    
    printf "\nResults:\n";
    printf "  Average: %.2f ms\n" avg;
    printf "  P95: %.2f ms\n" p95;
    printf "  Target: ≤20ms\n";
    
    if p95 <= 20.0 then
      printf "✅ PERFORMANCE TARGET MET (%.1f%% better)\n\n" ((20.0 -. p95) /. 20.0 *. 100.0)
    else
      printf "❌ PERFORMANCE TARGET FAILED\n\n"
      
  with e ->
    printf "❌ ERROR during performance test: %s\n\n" (Printexc.to_string e)

let () =
  printf "\n";
  printf "================================\n";
  printf "ACTUAL L0 VERIFICATION TEST\n";
  printf "================================\n\n";
  
  test_macro_initialization ();
  test_tokenization ();
  test_performance ();
  
  printf "================================\n";
  printf "END OF VERIFICATION\n";
  printf "================================\n"