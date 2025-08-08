open Printf

(* Test the fixed L0 lexer recognizes all built-in macros *)

let test_display_math () =
  printf "=== TESTING L0 MACRO FIX ===\n";
  
  (* Test 1: Display math macros *)
  let test_input = "\\[x^2 + y^2 = z^2\\]" in
  printf "Test 1 - Display math: %s\n" test_input;
  
  let tokens = L0_lexer_track_a_arena_fixed.tokenize test_input in
  printf "Tokens: %d\n" (List.length tokens);
  
  tokens |> List.iteri (fun i token ->
    match token with
    | Lexer_v25.TMacro name -> 
        printf "  [%d] TMacro(\"%s\") %s\n" i name 
          (if name = "[" || name = "]" then "✅ FIXED!" else "")
    | Lexer_v25.TChar (c, cat) ->
        let code = Uchar.to_int c in
        if code < 128 then
          printf "  [%d] TChar('%c', %s)\n" i (Char.chr code) (Catcode.catcode_to_string cat)
        else
          printf "  [%d] TChar(U+%04X, %s)\n" i code (Catcode.catcode_to_string cat)
    | Lexer_v25.TParam n ->
        printf "  [%d] TParam(%d)\n" i n
    | Lexer_v25.TGroupOpen ->
        printf "  [%d] TGroupOpen\n" i
    | Lexer_v25.TGroupClose ->
        printf "  [%d] TGroupClose\n" i
    | Lexer_v25.TEOF ->
        printf "  [%d] TEOF\n" i
  );
  
  (* Check if display math macros are recognized *)
  let has_display_begin = List.exists (function 
    | Lexer_v25.TMacro "[" -> true 
    | _ -> false) tokens in
  let has_display_end = List.exists (function 
    | Lexer_v25.TMacro "]" -> true 
    | _ -> false) tokens in
  
  if has_display_begin && has_display_end then
    printf "✅ SUCCESS: Display math macros recognized!\n\n"
  else
    printf "❌ FAILED: Display math macros still unknown\n\n";
    
  (* Test 2: Other built-in macros *)
  let test_macros = [
    ("\\LaTeX", "LaTeX");
    ("\\alpha", "alpha");
    ("\\section{Title}", "section");
    ("\\textbf{bold}", "textbf");
    ("\\infty", "infty");
    ("\\centering", "centering")
  ] in
  
  printf "Test 2 - Other built-in macros:\n";
  test_macros |> List.iter (fun (input, expected) ->
    let tokens = L0_lexer_track_a_arena_fixed.tokenize input in
    let found = List.exists (function
      | Lexer_v25.TMacro name -> name = expected
      | _ -> false) tokens in
    printf "  %s -> %s %s\n" input expected (if found then "✅" else "❌")
  );
  
  printf "\n"

let test_performance () =
  printf "=== PERFORMANCE TEST ===\n";
  
  (* Create a 1MB test document *)
  let large_doc = String.concat "\n" [
    "\\documentclass{article}";
    "\\begin{document}";
    String.concat " " (List.init 10000 (fun i -> 
      sprintf "This is paragraph %d with some \\textbf{bold} and \\emph{emphasis} and math $x_%d$." i i));
    "\\[";
    "E = mc^2";
    "\\]";
    "\\end{document}"
  ] in
  
  printf "Document size: %d bytes\n" (String.length large_doc);
  
  let start_time = Unix.gettimeofday () in
  let tokens = L0_lexer_track_a_arena_fixed.tokenize large_doc in
  let end_time = Unix.gettimeofday () in
  
  let elapsed_ms = (end_time -. start_time) *. 1000.0 in
  printf "Tokenization time: %.2f ms\n" elapsed_ms;
  printf "Tokens produced: %d\n" (List.length tokens);
  printf "Performance: %s (target ≤20ms)\n" 
    (if elapsed_ms <= 20.0 then "✅ PASS" else "❌ FAIL");
  
  printf "\n"

let () =
  test_display_math ();
  test_performance ()