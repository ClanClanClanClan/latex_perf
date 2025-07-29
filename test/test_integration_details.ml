(** Detailed test of L0-L1 integration *)

module L0_v25 = Layer0.L0_v25
module L1_v25 = Layer1.L1_v25
module Types = Latex_perfectionist_core.Types

let test_lexer_details () =
  Printf.printf "=== LEXER DETAILED TEST ===\n\n";
  
  let test_cases = [
    ("Simple text", "Hello world");
    ("Command", "\\section{Test}");
    ("Math", "$x + y$");
    ("Multiple commands", "\\textbf{Bold} and \\emph{italic}");
    ("Comments", "Text % comment\nMore text");
  ] in
  
  List.iter (fun (name, input) ->
    Printf.printf "Test: %s\n" name;
    Printf.printf "Input: %S\n" input;
    
    let bytes = Bytes.of_string input in
    let (tokens, state) = L0_v25.lex_chunk bytes in
    
    Printf.printf "Tokens (%d):\n" (Array.length tokens);
    Array.iteri (fun i tok ->
      Printf.printf "  [%d] %s\n" i (Types.token_to_string tok)
    ) tokens;
    
    Printf.printf "State: chunk_id=%d, version=%Ld\n\n" 
      state.L0_v25.chunk_id state.L0_v25.version
  ) test_cases

let test_expander_details () =
  Printf.printf "=== EXPANDER DETAILED TEST ===\n\n";
  
  (* Test specific macros *)
  let test_macros = [
    ("\\LaTeX{}", [Types.TCommand "LaTeX"; Types.TBeginGroup; Types.TEndGroup]);
    ("\\TeX{}", [Types.TCommand "TeX"; Types.TBeginGroup; Types.TEndGroup]);
    ("\\textbf{text}", [Types.TCommand "textbf"; Types.TBeginGroup; 
                        Types.TText "text"; Types.TEndGroup]);
    ("\\emph{word}", [Types.TCommand "emph"; Types.TBeginGroup;
                      Types.TText "word"; Types.TEndGroup]);
  ] in
  
  List.iter (fun (name, tokens) ->
    Printf.printf "Test: %s\n" name;
    Printf.printf "Input tokens: ";
    List.iter (fun tok -> Printf.printf "%s " (Types.token_to_string tok)) tokens;
    Printf.printf "\n";
    
    let tokens_array = Array.of_list tokens in
    let l0_key = { L0_v25.chunk_id = 0; hash = 0L } in
    let l1_env = L1_v25.initial_state l0_key in
    let delta = { 
      L1_v25.unexpanded = tokens_array; 
      expanded = [||]; 
      macros_used = [] 
    } in
    
    let fuel = 100 in
    let (expanded_delta, new_state) = L1_v25.expand_delta ~fuel ~env:l1_env delta in
    
    Printf.printf "Expanded tokens: ";
    Array.iter (fun tok -> Printf.printf "%s " (Types.token_to_string tok)) 
      expanded_delta.L1_v25.expanded;
    Printf.printf "\n";
    Printf.printf "Fuel consumed: %d\n" new_state.L1_v25.fuel_consumed;
    Printf.printf "Macros used: %s\n\n" (String.concat ", " expanded_delta.L1_v25.macros_used)
  ) test_macros

let test_caching () =
  Printf.printf "=== CACHE TEST ===\n\n";
  
  let input = "\\LaTeX{} is great!" in
  let bytes = Bytes.of_string input in
  
  (* First call - cache miss *)
  let start1 = Unix.gettimeofday () in
  let (tokens1, _state1) = L0_v25.lex_chunk bytes in
  let time1 = (Unix.gettimeofday () -. start1) *. 1000. in
  Printf.printf "First call (cache miss): %.3fms\n" time1;
  
  (* Second call - should hit cache *)
  let start2 = Unix.gettimeofday () in
  let (tokens2, _state2) = L0_v25.lex_chunk bytes in
  let time2 = (Unix.gettimeofday () -. start2) *. 1000. in
  Printf.printf "Second call (cache hit?): %.3fms\n" time2;
  
  (* Verify same results *)
  let same_tokens = 
    Array.length tokens1 = Array.length tokens2 &&
    Array.for_all2 (=) tokens1 tokens2 in
  
  Printf.printf "Same tokens: %b\n" same_tokens;
  Printf.printf "Cache speedup: %.1fx\n\n" (time1 /. time2)

let () =
  test_lexer_details ();
  test_expander_details ();
  test_caching ()