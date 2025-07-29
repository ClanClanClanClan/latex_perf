(** Basic test to verify the code actually compiles and runs *)

open Latex_perfectionist_core.Types
module L0_v25 = Layer0.L0_v25
module L1_v25 = Layer1.L1_v25

let test_types () =
  Printf.printf "Testing types module...\n";
  let tok = TText "hello" in
  Printf.printf "Token: %s\n" (token_to_string tok);
  
  let cmd = TCommand "section" in
  Printf.printf "Command: %s\n" (token_to_string cmd);
  
  assert (token_to_string TMathShift = "MathShift($)");
  Printf.printf "✓ Types module works\n\n"

let test_lexer () =
  Printf.printf "Testing L0 lexer...\n";
  
  let input = Bytes.of_string "Hello \\LaTeX{} world!" in
  let (tokens, _state) = L0_v25.lex_chunk input in
  
  Printf.printf "Lexed %d tokens\n" (Array.length tokens);
  Array.iteri (fun i tok ->
    Printf.printf "  [%d] %s\n" i (token_to_string tok)
  ) tokens;
  
  assert (Array.length tokens > 0);
  Printf.printf "✓ L0 lexer works\n\n"

let test_expander () =
  Printf.printf "Testing L1 expander...\n";
  
  let tokens = [|TText "Hello"; TCommand "LaTeX"; TText "world"|] in
  let l0_key = { L0_v25.chunk_id = 0; hash = 0L } in
  let l1_env = L1_v25.initial_state l0_key in
  
  let delta = { 
    L1_v25.unexpanded = tokens; 
    expanded = [||]; 
    macros_used = [] 
  } in
  
  let fuel = 100 in
  let (result, _) = L1_v25.expand_delta ~fuel ~env:l1_env delta in
  
  Printf.printf "Expanded to %d tokens\n" (Array.length result.L1_v25.expanded);
  Printf.printf "✓ L1 expander works\n\n"

let () =
  Printf.printf "=== LaTeX Perfectionist v25 Basic Test ===\n\n";
  
  test_types ();
  test_lexer ();
  test_expander ();
  
  Printf.printf "All tests passed! ✅\n"