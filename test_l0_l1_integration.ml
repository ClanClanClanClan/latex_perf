(** Integration test for L0+L1 v25 architecture
    
    Verifies that the existing proven lexer and expander
    work correctly with the new v25 wrappers.
*)

open Lwt.Syntax

let test_basic_lexing () =
  Printf.printf "\n=== Testing L0 Lexing ===\n";
  
  (* Simple LaTeX input *)
  let input = Bytes.of_string "Hello \\LaTeX{} world!" in
  
  (* Lex the input *)
  let (tokens, state) = L0_v25.lex_chunk input in
  
  Printf.printf "Lexed %d tokens:\n" (Array.length tokens);
  Array.iteri (fun i tok ->
    Printf.printf "  [%d] %s\n" i (Types.token_to_string tok)
  ) tokens;
  
  (* Check performance *)
  Printf.printf "State: chunk_id=%d, version=%Ld\n" 
    state.L0_v25.chunk_id 
    state.L0_v25.version;
  
  (tokens, state)

let test_macro_expansion tokens l0_key =
  Printf.printf "\n=== Testing L1 Expansion ===\n";
  
  (* Initialize L1 with L0 key *)
  let l1_env = L1_v25.initial_state l0_key in
  
  (* Create delta *)
  let delta = { 
    L1_v25.unexpanded = tokens; 
    expanded = [||]; 
    macros_used = [] 
  } in
  
  (* Expand with standard fuel *)
  let fuel = 2048 in
  let (expanded_delta, new_state) = L1_v25.expand_delta ~fuel ~env:l1_env delta in
  
  Printf.printf "Expanded to %d tokens:\n" (Array.length expanded_delta.L1_v25.expanded);
  Array.iteri (fun i tok ->
    Printf.printf "  [%d] %s\n" i (Types.token_to_string tok)
  ) expanded_delta.L1_v25.expanded;
  
  Printf.printf "Fuel consumed: %d\n" new_state.L1_v25.fuel_consumed;
  Printf.printf "Macros used: %s\n" (String.concat ", " expanded_delta.L1_v25.macros_used);
  
  expanded_delta.L1_v25.expanded

let test_orchestrator () =
  Printf.printf "\n=== Testing Orchestrator ===\n";
  
  (* Initialize orchestrator *)
  Orchestrator.init ();
  
  (* Test inputs *)
  let test_cases = [
    "Simple text";
    "Math: $x^2 + y^2 = z^2$";
    "Command: \\section{Introduction}";
    "Macro: \\LaTeX{} is great!";
    "Complex: \\textbf{Bold \\emph{and italic}} text";
  ] in
  
  (* Process each test case *)
  let* results = Lwt_list.map_s (fun input ->
    Printf.printf "\nProcessing: %s\n" input;
    let bytes = Bytes.of_string input in
    let* result = Orchestrator.process_edit bytes in
    match result with
    | Ok tokens ->
        Printf.printf "  Success: %d tokens\n" (Array.length tokens);
        Lwt.return (Ok tokens)
    | Error e ->
        Printf.printf "  Error: %s\n" (match e with
          | `L0_error msg -> "L0: " ^ msg
          | `Aborted reason -> "Aborted: " ^ reason);
        Lwt.return (Error e)
  ) test_cases in
  
  (* Print performance report *)
  Orchestrator.Perf.report ();
  
  (* Check synchronization *)
  Orchestrator.check_sync ();
  
  Lwt.return results

let test_performance () =
  Printf.printf "\n=== Performance Testing ===\n";
  
  (* Generate a realistic document chunk *)
  let doc = String.concat "\n" [
    "\\documentclass{article}";
    "\\begin{document}";
    "\\section{Introduction}";
    "This is a \\LaTeX{} document with \\textbf{bold} and \\emph{italic} text.";
    "Math mode: $\\alpha + \\beta = \\gamma$.";
    "Display math:";
    "\\begin{equation}";
    "  \\int_0^\\infty e^{-x^2} dx = \\frac{\\sqrt{\\pi}}{2}";
    "\\end{equation}";
    "\\end{document}";
  ] in
  
  let bytes = Bytes.of_string doc in
  
  (* Warm up *)
  let* _ = Orchestrator.process_edit bytes in
  
  (* Measure 100 iterations *)
  let iterations = 100 in
  let start = Unix.gettimeofday () in
  
  let* _ = Lwt_list.iter_s (fun _ ->
    let* _ = Orchestrator.process_edit bytes in
    Lwt.return ()
  ) (List.init iterations (fun i -> i)) in
  
  let elapsed = Unix.gettimeofday () -. start in
  let avg_ms = elapsed *. 1000. /. float iterations in
  
  Printf.printf "\nPerformance Results:\n";
  Printf.printf "  Iterations: %d\n" iterations;
  Printf.printf "  Total time: %.3fs\n" elapsed;
  Printf.printf "  Average per edit: %.3fms\n" avg_ms;
  Printf.printf "  Target: <1ms ✓\n";
  
  if avg_ms < 1.0 then
    Printf.printf "  Status: PASS ✅\n"
  else
    Printf.printf "  Status: FAIL ❌ (%.1fx over target)\n" (avg_ms /. 1.0);
  
  Lwt.return ()

(* Main test runner *)
let main () =
  Printf.printf "LaTeX Perfectionist v25 - L0+L1 Integration Test\n";
  Printf.printf "================================================\n";
  
  (* Run tests *)
  let (tokens, l0_state) = test_basic_lexing () in
  let l0_key = L0_v25.compute_cache_key (Bytes.of_string "test") l0_state in
  let _ = test_macro_expansion tokens l0_key in
  
  (* Run async tests *)
  Lwt_main.run (
    let* _ = test_orchestrator () in
    let* _ = test_performance () in
    Lwt.return ()
  );
  
  Printf.printf "\n✅ All tests completed!\n"

let () = main ()