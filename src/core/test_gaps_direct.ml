(** Direct test of all gap fixes in the src/core directory *)

open Types
open Common_macros  
open Expander_stub
open L0_v25
open L1_v25

let test_end_to_end_pipeline () =
  Printf.printf "=== END-TO-END PIPELINE TEST ===\n";
  
  let test_document = {tex|
\documentclass{article}
\begin{document}
\section{Test}
Hello \LaTeX{} with \textbf{bold} and \textit{italic} text.
Math symbols: $\alpha + \beta = \sum_{i=1}^n x_i$.
More symbols: \gamma, \delta, \pi, \sigma.
Spacing: \quad text \qquad more text.
Dots: \ldots and \cdots and \vdots.
\end{document}
|tex} in
  
  Printf.printf "Processing document (%d chars)...\n" (String.length test_document);
  
  let start_time = Unix.gettimeofday () in
  
  (* Step 1: L0 Lexing *)
  let bytes = Bytes.of_string test_document in
  let l0_start = Unix.gettimeofday () in
  let (lexed_tokens, l0_state) = lex_chunk bytes in
  let l0_time = (Unix.gettimeofday () -. l0_start) *. 1_000_000. in
  
  Printf.printf "L0 Results:\n";
  Printf.printf "  Input: %d bytes\n" (Bytes.length bytes);
  Printf.printf "  Output: %d tokens\n" (Array.length lexed_tokens);
  Printf.printf "  Time: %.0fμs\n" l0_time;
  Printf.printf "  Performance: %.1f chars/μs\n" (float (String.length test_document) /. l0_time);
  
  (* Step 2: L1 Expansion *)
  let l0_key = { chunk_id = l0_state.chunk_id; hash = Int64.of_int (Hashtbl.hash test_document) } in
  let l1_env = initial_state l0_key in
  let delta = { 
    unexpanded = lexed_tokens; 
    expanded = [||]; 
    macros_used = [] 
  } in
  
  let l1_start = Unix.gettimeofday () in
  let (expanded_result, l1_state) = expand_delta ~fuel:1000 ~env:l1_env delta in
  let l1_time = (Unix.gettimeofday () -. l1_start) *. 1_000_000. in
  
  Printf.printf "L1 Results:\n";
  Printf.printf "  Input: %d tokens\n" (Array.length lexed_tokens);
  Printf.printf "  Output: %d tokens\n" (Array.length expanded_result.expanded);
  Printf.printf "  Time: %.0fμs\n" l1_time;
  Printf.printf "  Macros used: [%s]\n" (String.concat "; " expanded_result.macros_used);
  
  let total_time = (Unix.gettimeofday () -. start_time) *. 1_000_000. in
  
  Printf.printf "Pipeline Results:\n";
  Printf.printf "  Total time: %.0fμs (%.2fms)\n" total_time (total_time /. 1000.);
  Printf.printf "  Throughput: %.1f chars/μs\n" (float (String.length test_document) /. total_time);
  
  (* Verify macro expansions *)
  let expanded_list = Array.to_list expanded_result.expanded in
  let expansions = [
    ("LaTeX", fun tok -> match tok with TText "LaTeX" -> true | _ -> false);
    ("bold", fun tok -> match tok with TText "[bold]" -> true | _ -> false);
    ("italic", fun tok -> match tok with TText "[italic]" -> true | _ -> false);
    ("alpha", fun tok -> match tok with TText "α" -> true | _ -> false);
    ("sum", fun tok -> match tok with TText "∑" -> true | _ -> false);
    ("dots", fun tok -> match tok with TText "..." -> true | _ -> false);
  ] in
  
  Printf.printf "Macro Expansion Verification:\n";
  let all_expansions_ok = ref true in
  List.iter (fun (name, check_fn) ->
    let found = List.exists check_fn expanded_list in
    Printf.printf "  %s: %s\n" name (if found then "✅" else "❌");
    if not found then all_expansions_ok := false
  ) expansions;
  
  (* Performance check *)
  let claimed_4_43ms = 4430. in
  let performance_ok = total_time < claimed_4_43ms in
  Printf.printf "Performance vs 4.43ms claim: %s (%.1fx %s)\n"
    (if performance_ok then "✅" else "❌")
    (total_time /. claimed_4_43ms)
    (if performance_ok then "faster" else "slower");
  
  !all_expansions_ok && performance_ok

let test_macro_completeness () =
  Printf.printf "\n=== MACRO COMPLETENESS TEST ===\n";
  
  let macro_count = List.length builtin_macro_list in
  Printf.printf "Total built-in macros: %d\n" macro_count;
  
  (* Test key macro categories *)
  let test_macros = [
    ("LaTeX", "LaTeX");
    ("TeX", "TeX");
    ("textbf", "[bold]");
    ("textit", "[italic]");
    ("alpha", "α");
    ("beta", "β");
    ("sum", "∑");
    ("ldots", "...");
    ("quad", " ");
    ("today", "2025-07-29");
  ] in
  
  let failures = ref [] in
  
  List.iter (fun (macro_name, expected) ->
    match List.assoc_opt macro_name builtin_macro_list with
    | Some tokens ->
      let matches = List.exists (function
        | TText s when s = expected -> true
        | TSpace when expected = " " -> true
        | _ -> false
      ) tokens in
      if matches then
        Printf.printf "  ✅ %s -> %s\n" macro_name expected
      else begin
        Printf.printf "  ❌ %s -> unexpected expansion\n" macro_name;
        failures := macro_name :: !failures
      end
    | None ->
      Printf.printf "  ❌ %s -> NOT FOUND\n" macro_name;
      failures := macro_name :: !failures
  ) test_macros;
  
  let success_count = List.length test_macros - List.length !failures in
  Printf.printf "Macro test results: %d/%d passed\n" success_count (List.length test_macros);
  Printf.printf "Macro completeness: %s\n" 
    (if macro_count >= 86 then "✅ MEETS SPEC" else "❌ INSUFFICIENT");
  
  List.length !failures = 0 && macro_count >= 86

let () =
  Printf.printf "🔧 DIRECT SYSTEM VERIFICATION\n";
  Printf.printf "===============================\n";
  
  let pipeline_ok = test_end_to_end_pipeline () in
  let macro_ok = test_macro_completeness () in
  
  Printf.printf "\n=== FINAL SYSTEM RESULTS ===\n";
  Printf.printf "End-to-end pipeline: %s\n" (if pipeline_ok then "✅ WORKING" else "❌ FAILED");
  Printf.printf "Macro completeness: %s\n" (if macro_ok then "✅ COMPLETE" else "❌ INCOMPLETE");
  
  if pipeline_ok && macro_ok then begin
    Printf.printf "\n🎯 ✅ ALL SYSTEM GAPS FIXED!\n";
    Printf.printf "LaTeX Perfectionist v25 Week 1+2 foundation is fully functional.\n";
    exit 0
  end else begin
    Printf.printf "\n❌ SYSTEM ISSUES REMAIN\n";
    exit 1
  end