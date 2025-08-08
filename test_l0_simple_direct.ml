(* Simple direct test of L0 arena lexer *)

open Printf

let test_basic_tokenization () =
  printf "=== BASIC L0 TOKENIZATION TEST ===\n";
  
  (* Test simple input *)
  let input = "Hello world" in
  printf "Input: '%s'\n" input;
  
  try
    (* This should initialize macros automatically *)
    let tokens = L0_lexer_track_a_arena.tokenize input in
    printf "✅ Tokenization succeeded: %d tokens\n" (List.length tokens);
    
    (* Show first few tokens *)
    tokens |> List.iteri (fun i tok ->
      if i < 5 then
        match tok with
        | Lexer_v25.TChar (c, cat) ->
            printf "  [%d] TChar('%c', %s)\n" i 
              (try Uchar.to_char c with _ -> '?')
              (Catcode.catcode_to_string cat)
        | _ -> printf "  [%d] Other token\n" i
    )
  with e ->
    printf "❌ ERROR: %s\n" (Printexc.to_string e)

let test_display_math () =
  printf "\n=== DISPLAY MATH TEST ===\n";
  
  let input = "\\[x^2\\]" in
  printf "Input: '%s'\n" input;
  
  try
    let tokens = L0_lexer_track_a_arena.tokenize input in
    printf "Tokens: %d\n" (List.length tokens);
    
    (* Look for macros *)
    let macros = ref [] in
    tokens |> List.iter (function
      | Lexer_v25.TMacro name -> macros := name :: !macros
      | _ -> ()
    );
    
    printf "Macros found: [%s]\n" (String.concat ", " (List.rev !macros));
    
    if List.mem "[" !macros && List.mem "]" !macros then
      printf "✅ Display math macros recognized!\n"
    else
      printf "❌ Display math macros NOT found\n"
      
  with e ->
    printf "❌ ERROR: %s\n" (Printexc.to_string e)

let test_performance () =
  printf "\n=== PERFORMANCE TEST (100KB) ===\n";
  
  (* Create 100KB test doc *)
  let doc = String.make 100_000 'x' in
  
  try
    (* Warm-up *)
    let _ = L0_lexer_track_a_arena.tokenize doc in
    
    (* Timed run *)
    let start = Unix.gettimeofday () in
    let tokens = L0_lexer_track_a_arena.tokenize doc in
    let elapsed = Unix.gettimeofday () -. start in
    let elapsed_ms = elapsed *. 1000.0 in
    
    printf "Time for 100KB: %.2f ms\n" elapsed_ms;
    printf "Tokens produced: %d\n" (List.length tokens);
    printf "Extrapolated to 1.1MB: ~%.2f ms\n" (elapsed_ms *. 11.0);
    
    if elapsed_ms *. 11.0 <= 20.0 then
      printf "✅ Performance target MET!\n"
    else if elapsed_ms *. 11.0 <= 25.0 then
      printf "⚠️ Performance close to target\n"
    else
      printf "❌ Performance needs work\n"
      
  with e ->
    printf "❌ ERROR: %s\n" (Printexc.to_string e)

let () =
  printf "\n================================\n";
  printf "L0 ARENA LEXER DIRECT TEST\n";
  printf "================================\n\n";
  
  test_basic_tokenization ();
  test_display_math ();
  test_performance ();
  
  printf "\n================================\n"