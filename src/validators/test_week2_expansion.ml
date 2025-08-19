(* WEEK 2 EXPANSION VALIDATOR TEST *)
(* Test the 18 total validators (Week 1 + Week 2) in DAG execution system *)

open Printf
open Validator_core
open Specification_compliant_validators
open Validator_dag_system

(* Mock context and stream for testing *)
let create_test_context () = create_context ()

let create_test_stream test_tokens =
  create_stream test_tokens

(* Test cases for Week 2 expansion validators *)
let test_typo_007 () =
  printf "Testing TYPO-007: Trailing spaces...\n";
  let test_tokens = [
    { token = TChar (Uchar.of_int 32, Space); location = { line = 1; column = 1; offset = 0 } }; (* space *)
    { token = TChar (Uchar.of_int 10, EndLine); location = { line = 1; column = 2; offset = 1 } }; (* newline *)
  ] in
  let stream = create_test_stream test_tokens in
  let context = create_test_context () in
  let module V = SpecCompliantTYPO007 in
  let issues = V.validate context stream in
  printf "  Found %d issues\n" (List.length issues)

let test_spc_002 () =
  printf "Testing SPC-002: Space before punctuation...\n";
  let test_tokens = [
    { token = TChar (Uchar.of_int 32, Space); location = { line = 1; column = 1; offset = 0 } }; (* space *)
    { token = TChar (Uchar.of_int 44, Other); location = { line = 1; column = 2; offset = 1 } }; (* comma *)
  ] in
  let stream = create_test_stream test_tokens in
  let context = create_test_context () in
  let module V = SpecCompliantSPC002 in
  let issues = V.validate context stream in
  printf "  Found %d issues\n" (List.length issues)

let test_char_001 () =
  printf "Testing CHAR-001: Unicode validation...\n";
  let test_tokens = [
    { token = TChar (Uchar.of_int 0xFDD0, Other); location = { line = 1; column = 1; offset = 0 } }; (* non-character *)
  ] in
  let stream = create_test_stream test_tokens in
  let context = create_test_context () in
  let module V = SpecCompliantCHAR001 in
  let issues = V.validate context stream in
  printf "  Found %d issues\n" (List.length issues)

let test_delim_002 () =
  printf "Testing DELIM-002: Extra closing braces...\n";
  let test_tokens = [
    { token = TChar (Uchar.of_int 125, EndGroup); location = { line = 1; column = 1; offset = 0 } }; (* } without opening *)
  ] in
  let stream = create_test_stream test_tokens in
  let context = create_test_context () in
  let module V = SpecCompliantDELIM002 in
  let issues = V.validate context stream in
  printf "  Found %d issues\n" (List.length issues)

(* Test Week 2 DAG system with comprehensive document *)
let test_week2_dag_system () =
  printf "\n=== TESTING WEEK 2 EXPANSION DAG SYSTEM ===\n";
  try
    let dag = initialize_validator_system () in
    printf "✅ Week 2 DAG system initialized successfully\n";
    
    (* Test with comprehensive document containing multiple issues *)
    let test_tokens = [
      (* ASCII quote issue *)
      { token = TChar (Uchar.of_int 34, Other); location = { line = 1; column = 1; offset = 0 } }; (* ASCII quote *)
      
      (* Double hyphen issue *)
      { token = TChar (Uchar.of_int 45, Other); location = { line = 1; column = 2; offset = 1 } }; (* - *)
      { token = TChar (Uchar.of_int 45, Other); location = { line = 1; column = 3; offset = 2 } }; (* - *)
      
      (* Tab character issue *)
      { token = TChar (Uchar.of_int 9, Other); location = { line = 1; column = 4; offset = 3 } }; (* tab *)
      
      (* Trailing space issue *)
      { token = TChar (Uchar.of_int 32, Space); location = { line = 1; column = 5; offset = 4 } }; (* space *)
      { token = TChar (Uchar.of_int 10, EndLine); location = { line = 1; column = 6; offset = 5 } }; (* newline *)
      
      (* Space before punctuation issue *)
      { token = TChar (Uchar.of_int 32, Space); location = { line = 2; column = 1; offset = 6 } }; (* space *)
      { token = TChar (Uchar.of_int 44, Other); location = { line = 2; column = 2; offset = 7 } }; (* comma *)
      
      (* Extra closing brace issue *)
      { token = TChar (Uchar.of_int 125, EndGroup); location = { line = 2; column = 3; offset = 8 } }; (* } *)
    ] in
    let stream = create_test_stream test_tokens in
    let context = create_test_context () in
    
    printf "\nExecuting all Week 2 validators in DAG order...\n";
    let (all_issues, execution_stats) = ValidatorDAG.execute_validators dag context stream in
    
    printf "\n=== WEEK 2 EXECUTION RESULTS ===\n";
    printf "Total issues found: %d\n" (List.length all_issues);
    printf "Validators executed: %d\n" (List.length execution_stats);
    
    printf "\n=== EXECUTION STATISTICS ===\n";
    List.iter (fun (validator_id, time_ms, issue_count) ->
      if issue_count > 0 then
        printf "✅ %s: %d issues in %.2fms\n" validator_id issue_count time_ms
      else
        printf "   %s: %d issues in %.2fms\n" validator_id issue_count time_ms
    ) execution_stats;
    
    printf "\n=== ISSUES DETECTED ===\n";
    List.iter (fun (issue : Validator_core.validation_issue) ->
      printf "- [%s] %s: %s\n" 
        (match issue.severity with `Error -> "ERROR" | `Warning -> "WARN" | `Info -> "INFO")
        issue.rule_id
        issue.message
    ) all_issues;
    
    printf "\n✅ Week 2 Expansion DAG test completed successfully\n"
    
  with
  | exn ->
    printf "❌ Week 2 DAG system test failed: %s\n" (Printexc.to_string exn);
    exit 1

(* Individual Week 2 validator tests *)
let test_week2_individual_validators () =
  printf "\n=== TESTING WEEK 2 EXPANSION VALIDATORS ===\n";
  test_typo_007 ();
  test_spc_002 ();
  test_char_001 ();
  test_delim_002 ();
  printf "Week 2 individual validator tests completed\n"

(* Performance comparison test *)
let test_week2_performance () =
  printf "\n=== WEEK 2 PERFORMANCE TEST ===\n";
  
  (* Initialize DAG system BEFORE timing *)
  let dag = initialize_validator_system () in
  
  (* Create larger test document - 10,000 tokens for meaningful test *)
  let large_test_tokens = Array.make 10000 
    { token = TChar (Uchar.of_int 97, Letter); location = { line = 1; column = 1; offset = 0 } } in
  let stream = create_stream (Array.to_list large_test_tokens) in
  let context = create_test_context () in
  
  (* START TIMING ONLY THE VALIDATION *)
  let start_time = Unix.gettimeofday () in
  let (all_issues, execution_stats) = ValidatorDAG.execute_validators dag context stream in
  let end_time = Unix.gettimeofday () in
  
  let total_time_ms = (end_time -. start_time) *. 1000.0 in
  
  printf "Performance results:\n";
  printf "- Total validation time: %.2fms\n" total_time_ms;
  printf "- Tokens processed: 10000\n";
  printf "- Validators executed: %d\n" (List.length execution_stats);
  printf "- Throughput: %.0f tokens/second\n" (10000.0 /. (total_time_ms /. 1000.0));
  
  if total_time_ms < 20.0 then
    printf "✅ Performance target achieved (%.2fms < 20ms)\n" total_time_ms
  else
    printf "⚠️  Performance target missed (%.2fms >= 20ms)\n" total_time_ms

(* Main test execution *)
let () =
  printf "WEEK 2 EXPANSION VALIDATOR TEST SUITE\n";
  printf "====================================\n";
  
  printf "Testing 18 total validators (Week 1 + Week 2):\n";
  printf "- L0_Lexer: TYPO-001-007, SPC-001-003, CHAR-001-002 (11 validators)\n";
  printf "- L1_Expanded: DELIM-001-004, REF-001-003 (7 validators)\n\n";
  
  test_week2_individual_validators ();
  test_week2_dag_system ();
  test_week2_performance ();
  
  printf "\n🎯 WEEK 2 EXPANSION TEST SUITE COMPLETE\n";
  printf "🚀 Ready for Week 3-5 consolidation and optimization\n"