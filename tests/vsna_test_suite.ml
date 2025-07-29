(* VSNA Test Suite - Comprehensive tests for LaTeX Perfectionist v24 *)

(* Test framework *)
type test_result = Pass | Fail of string

let test_count = ref 0
let pass_count = ref 0
let fail_count = ref 0

let run_test name test_fn =
  incr test_count;
  Printf.printf "Running test: %s ... " name;
  flush stdout;
  try
    match test_fn () with
    | Pass -> 
        incr pass_count;
        Printf.printf "PASS\n"
    | Fail msg -> 
        incr fail_count;
        Printf.printf "FAIL: %s\n" msg
  with e ->
    incr fail_count;
    Printf.printf "FAIL: Exception %s\n" (Printexc.to_string e)

(* Test helpers *)
let validate_doc doc =
  let state = Vsna_core.init_unified_state [] in
  Vsna_core.validate_complete state doc

let expect_no_issues doc =
  let (_, issues) = validate_doc doc in
  if List.length issues = 0 then Pass
  else Fail (Printf.sprintf "Expected no issues, found %d" (List.length issues))

let expect_issue_count doc count =
  let (_, issues) = validate_doc doc in
  if List.length issues = count then Pass
  else Fail (Printf.sprintf "Expected %d issues, found %d" count (List.length issues))

let expect_issue_at doc pos =
  let (_, issues) = validate_doc doc in
  if List.exists (fun (_, p, _) -> p = pos) issues then Pass
  else Fail (Printf.sprintf "Expected issue at position %d" pos)

(* Test cases *)
let test_empty_document () =
  expect_no_issues ""

let test_simple_text () =
  expect_no_issues "Hello, world!"

let test_balanced_braces () =
  expect_no_issues "{Hello {nested} world}"

let test_balanced_brackets () =
  expect_no_issues "[Hello [nested] world]"

let test_balanced_parens () =
  expect_no_issues "(Hello (nested) world)"

let test_unmatched_closing_brace () =
  expect_issue_count "Hello } world" 1

let test_unmatched_closing_bracket () =
  expect_issue_count "Hello ] world" 1

let test_unmatched_closing_paren () =
  expect_issue_count "Hello ) world" 1

let test_unclosed_brace () =
  expect_issue_count "Hello { world" 1

let test_unclosed_bracket () =
  expect_issue_count "Hello [ world" 1

let test_unclosed_paren () =
  expect_issue_count "Hello ( world" 1

let test_mismatched_brace_bracket () =
  let doc = "Hello {world]" in
  let (_, issues) = validate_doc doc in
  if List.length issues >= 1 && List.exists (fun (_, _, msg) -> 
    String.length msg > 0 && msg.[0] = 'M') issues then Pass
  else Fail "Expected mismatched bracket error"

let test_mismatched_bracket_brace () =
  let doc = "Hello [world}" in
  let (_, issues) = validate_doc doc in
  if List.length issues >= 1 && List.exists (fun (_, _, msg) -> 
    String.length msg > 0 && msg.[0] = 'M') issues then Pass
  else Fail "Expected mismatched bracket error"

let test_complex_nesting () =
  expect_no_issues "{a [b (c (d) e) f] g}"

let test_latex_commands () =
  expect_no_issues "\\section{Title} \\emph{emphasized}"

let test_math_mode () =
  expect_no_issues "$x^2 + y^2 = z^2$"

let test_environment () =
  expect_no_issues "\\begin{equation} x = y \\end{equation}"

let test_multiple_errors () =
  let doc = "{ unclosed and ] unmatched" in
  expect_issue_count doc 2

let test_position_tracking () =
  expect_issue_at "Hello } world" 7

let test_nested_unclosed () =
  let doc = "{outer {inner}" in
  expect_issue_count doc 1

let test_empty_constructs () =
  expect_no_issues "{} [] ()"

let test_adjacent_constructs () =
  expect_no_issues "{}{}[][]()(){}[](){}[]"

let test_performance_small () =
  let doc = String.make 100 'x' in
  let start = Unix.gettimeofday () in
  let _ = validate_doc doc in
  let elapsed = (Unix.gettimeofday () -. start) *. 1000.0 in
  if elapsed < 1.0 then Pass
  else Fail (Printf.sprintf "Too slow: %.2fms" elapsed)

let test_performance_medium () =
  let doc = String.make 10000 'x' in
  let start = Unix.gettimeofday () in
  let _ = validate_doc doc in
  let elapsed = (Unix.gettimeofday () -. start) *. 1000.0 in
  if elapsed < 10.0 then Pass
  else Fail (Printf.sprintf "Too slow: %.2fms" elapsed)

let test_performance_large () =
  let doc = String.make 100000 'x' in
  let start = Unix.gettimeofday () in
  let _ = validate_doc doc in
  let elapsed = (Unix.gettimeofday () -. start) *. 1000.0 in
  if elapsed < 42.0 then Pass
  else Fail (Printf.sprintf "SLA violation: %.2fms > 42ms" elapsed)

(* Main test runner *)
let () =
  Printf.printf "=== VSNA Test Suite ===\n\n";
  
  (* Basic tests *)
  Printf.printf "Basic Tests:\n";
  run_test "empty_document" test_empty_document;
  run_test "simple_text" test_simple_text;
  
  (* Balanced construct tests *)
  Printf.printf "\nBalanced Constructs:\n";
  run_test "balanced_braces" test_balanced_braces;
  run_test "balanced_brackets" test_balanced_brackets;
  run_test "balanced_parens" test_balanced_parens;
  
  (* Unmatched closing tests *)
  Printf.printf "\nUnmatched Closing:\n";
  run_test "unmatched_closing_brace" test_unmatched_closing_brace;
  run_test "unmatched_closing_bracket" test_unmatched_closing_bracket;
  run_test "unmatched_closing_paren" test_unmatched_closing_paren;
  
  (* Unclosed opening tests *)
  Printf.printf "\nUnclosed Opening:\n";
  run_test "unclosed_brace" test_unclosed_brace;
  run_test "unclosed_bracket" test_unclosed_bracket;
  run_test "unclosed_paren" test_unclosed_paren;
  
  (* Mismatched bracket types *)
  Printf.printf "\nMismatched Types:\n";
  run_test "mismatched_brace_bracket" test_mismatched_brace_bracket;
  run_test "mismatched_bracket_brace" test_mismatched_bracket_brace;
  
  (* Complex tests *)
  Printf.printf "\nComplex Tests:\n";
  run_test "complex_nesting" test_complex_nesting;
  run_test "latex_commands" test_latex_commands;
  run_test "math_mode" test_math_mode;
  run_test "environment" test_environment;
  run_test "multiple_errors" test_multiple_errors;
  run_test "position_tracking" test_position_tracking;
  run_test "nested_unclosed" test_nested_unclosed;
  run_test "empty_constructs" test_empty_constructs;
  run_test "adjacent_constructs" test_adjacent_constructs;
  
  (* Performance tests *)
  Printf.printf "\nPerformance Tests:\n";
  run_test "performance_small" test_performance_small;
  run_test "performance_medium" test_performance_medium;
  run_test "performance_large" test_performance_large;
  
  (* Summary *)
  Printf.printf "\n=== Test Summary ===\n";
  Printf.printf "Total tests: %d\n" !test_count;
  Printf.printf "Passed: %d\n" !pass_count;
  Printf.printf "Failed: %d\n" !fail_count;
  Printf.printf "Coverage: %.1f%%\n" 
    (float_of_int !pass_count /. float_of_int !test_count *. 100.0);
  
  (* Exit code *)
  exit (if !fail_count = 0 then 0 else 1)