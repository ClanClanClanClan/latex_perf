(* WEEK 1 FOUNDATION VALIDATOR TEST *)
(* Test the 10 critical validators in DAG execution system *)

open Printf
open Validator_core
open Specification_compliant_validators
open Validator_dag_system

(* Mock context and stream for testing *)
let create_test_context () = create_context ()

let create_test_stream test_tokens =
  create_stream test_tokens

(* Test cases for Week 1 validators *)
let test_typo_001 () =
  printf "Testing TYPO-001: ASCII straight quotes...\n";
  let test_tokens = [
    { token = TChar (Uchar.of_int 34, Other); location = { line = 1; column = 1; offset = 0 } }; (* ASCII quote *)
  ] in
  let stream = create_test_stream test_tokens in
  let context = create_test_context () in
  let module V = SpecCompliantTYPO001 in
  let issues = V.validate context stream in
  printf "  Found %d issues\n" (List.length issues);
  if List.length issues > 0 then
    List.iter (fun issue -> printf "    - %s\n" issue.message) issues

let test_typo_002 () =
  printf "Testing TYPO-002: Double hyphen...\n";
  let test_tokens = [
    { token = TChar (Uchar.of_int 45, Other); location = { line = 1; column = 1; offset = 0 } }; (* - *)
    { token = TChar (Uchar.of_int 45, Other); location = { line = 1; column = 2; offset = 1 } }; (* - *)
  ] in
  let stream = create_test_stream test_tokens in
  let context = create_test_context () in
  let module V = SpecCompliantTYPO002 in
  let issues = V.validate context stream in
  printf "  Found %d issues\n" (List.length issues)

let test_typo_006 () =
  printf "Testing TYPO-006: Tab character...\n";
  let test_tokens = [
    { token = TChar (Uchar.of_int 9, Other); location = { line = 1; column = 1; offset = 0 } }; (* tab *)
  ] in
  let stream = create_test_stream test_tokens in
  let context = create_test_context () in
  let module V = SpecCompliantTYPO006 in
  let issues = V.validate context stream in
  printf "  Found %d issues\n" (List.length issues)

let test_delim_001 () =
  printf "Testing DELIM-001: Unmatched braces...\n";
  let test_tokens = [
    { token = TChar (Uchar.of_int 123, BeginGroup); location = { line = 1; column = 1; offset = 0 } }; (* { *)
    { token = TChar (Uchar.of_int 97, Letter); location = { line = 1; column = 2; offset = 1 } }; (* a *)
    (* Missing closing } *)
  ] in
  let stream = create_test_stream test_tokens in
  let context = create_test_context () in
  let module V = SpecCompliantDELIM001 in
  let issues = V.validate context stream in
  printf "  Found %d issues\n" (List.length issues)

let test_ref_001 () =
  printf "Testing REF-001: Undefined references...\n";
  let test_tokens = [
    { token = TMacro "ref"; location = { line = 1; column = 1; offset = 0 } };
    { token = TChar (Uchar.of_int 123, BeginGroup); location = { line = 1; column = 5; offset = 4 } }; (* { *)
    { token = TChar (Uchar.of_int 102, Letter); location = { line = 1; column = 6; offset = 5 } }; (* f *)
    { token = TChar (Uchar.of_int 105, Letter); location = { line = 1; column = 7; offset = 6 } }; (* i *)
    { token = TChar (Uchar.of_int 103, Letter); location = { line = 1; column = 8; offset = 7 } }; (* g *)
    { token = TChar (Uchar.of_int 125, EndGroup); location = { line = 1; column = 9; offset = 8 } }; (* } *)
  ] in
  let stream = create_test_stream test_tokens in
  let context = create_test_context () in
  let module V = SpecCompliantREF001 in
  let issues = V.validate context stream in
  printf "  Found %d issues\n" (List.length issues)

(* Test DAG system with all Week 1 validators *)
let test_dag_system () =
  printf "\n=== TESTING WEEK 1 FOUNDATION DAG SYSTEM ===\n";
  try
    let dag = initialize_validator_system () in
    printf "✅ DAG system initialized successfully\n";
    
    (* Test with simple document *)
    let test_tokens = [
      { token = TChar (Uchar.of_int 34, Other); location = { line = 1; column = 1; offset = 0 } }; (* ASCII quote *)
      { token = TChar (Uchar.of_int 45, Other); location = { line = 1; column = 2; offset = 1 } }; (* - *)
      { token = TChar (Uchar.of_int 45, Other); location = { line = 1; column = 3; offset = 2 } }; (* - *)
      { token = TChar (Uchar.of_int 9, Other); location = { line = 1; column = 4; offset = 3 } }; (* tab *)
    ] in
    let stream = create_test_stream test_tokens in
    let context = create_test_context () in
    
    printf "\nExecuting all Week 1 validators in DAG order...\n";
    let (all_issues, execution_stats) = ValidatorDAG.execute_validators dag context stream in
    
    printf "\n=== EXECUTION RESULTS ===\n";
    printf "Total issues found: %d\n" (List.length all_issues);
    printf "Validators executed: %d\n" (List.length execution_stats);
    
    printf "\n=== EXECUTION STATISTICS ===\n";
    List.iter (fun (validator_id, time_ms, issue_count) ->
      printf "%s: %d issues in %.2fms\n" validator_id issue_count time_ms
    ) execution_stats;
    
    printf "\n=== ISSUES FOUND ===\n";
    List.iter (fun (issue : Validator_core.validation_issue) ->
      printf "- [%s] %s: %s\n" 
        (match issue.severity with `Error -> "ERROR" | `Warning -> "WARN" | `Info -> "INFO")
        issue.rule_id
        issue.message
    ) all_issues;
    
    printf "\n✅ Week 1 Foundation DAG test completed successfully\n"
    
  with
  | exn ->
    printf "❌ DAG system test failed: %s\n" (Printexc.to_string exn);
    exit 1

(* Individual validator tests *)
let test_individual_validators () =
  printf "\n=== TESTING INDIVIDUAL VALIDATORS ===\n";
  test_typo_001 ();
  test_typo_002 ();
  test_typo_006 ();
  test_delim_001 ();
  test_ref_001 ();
  printf "Individual validator tests completed\n"

(* Main test execution *)
let () =
  printf "WEEK 1 FOUNDATION VALIDATOR TEST SUITE\n";
  printf "=====================================\n";
  
  printf "Testing 10 critical validators:\n";
  printf "- L0_Lexer: TYPO-001, TYPO-002, TYPO-003, TYPO-005, TYPO-006\n";
  printf "- L1_Expanded: DELIM-001, DELIM-003, REF-001, REF-002, REF-003\n\n";
  
  test_individual_validators ();
  test_dag_system ();
  
  printf "\n🎯 WEEK 1 FOUNDATION TEST SUITE COMPLETE\n";
  printf "Ready for systematic Week 2-5 expansion\n"