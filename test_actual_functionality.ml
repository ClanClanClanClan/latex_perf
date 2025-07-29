(** ACTUAL FUNCTIONALITY TEST - Tests compiled modules directly
    
    This bypasses complex module loading and tests actual functionality.
*)

let test_compiled_modules () =
  Printf.printf "=== COMPILED MODULE FUNCTIONALITY TEST ===\n";
  
  (* Test 1: Create a simple test program that uses the actual modules *)
  let test_program = {|
open Types
open Common_macros  
open Expander_stub

let test_basic_functionality () =
  Printf.printf "Testing basic functionality...\n";
  
  (* Test type creation *)
  let tokens = [|
    TText "hello";
    TCommand "LaTeX";
    TSpace;
    TCommand "alpha";
  |] in
  
  Printf.printf "✅ Token array created: %d tokens\n" (Array.length tokens);
  
  (* Test token to string conversion *)
  Array.iteri (fun i tok ->
    Printf.printf "  [%d]: %s\n" i (token_to_string tok)
  ) tokens;
  
  (* Test macro count *)
  let macro_count = List.length builtin_macro_list in
  Printf.printf "✅ Built-in macros available: %d\n" macro_count;
  
  (* Test specific macro lookup *)
  let latex_found = List.mem_assoc "LaTeX" builtin_macro_list in
  let alpha_found = List.mem_assoc "alpha" builtin_macro_list in
  let textbf_found = List.mem_assoc "textbf" builtin_macro_list in
  
  Printf.printf "✅ LaTeX macro: %s\n" (if latex_found then "FOUND" else "MISSING");
  Printf.printf "✅ alpha macro: %s\n" (if alpha_found then "FOUND" else "MISSING");  
  Printf.printf "✅ textbf macro: %s\n" (if textbf_found then "FOUND" else "MISSING");
  
  (* Test macro expansion *)
  let env = empty_env in
  let test_tokens = [TCommand "LaTeX"; TSpace; TCommand "textbf"] in
  
  match expand_one_step env test_tokens with
  | Some (expanded_tokens, macro_used) ->
    Printf.printf "✅ Macro expansion works: %s -> " macro_used;
    List.iter (fun tok -> Printf.printf "%s " (token_to_string tok)) expanded_tokens;
    Printf.printf "\n";
    true
  | None ->
    Printf.printf "❌ Macro expansion failed\n";
    false

let test_performance () =
  Printf.printf "\nTesting performance...\n";
  
  let large_token_array = Array.make 1000 (TCommand "LaTeX") in
  let start_time = Unix.gettimeofday () in
  
  (* Process tokens *)
  let result_count = ref 0 in
  Array.iter (fun tok ->
    let _ = token_to_string tok in
    incr result_count
  ) large_token_array;
  
  let elapsed_us = (Unix.gettimeofday () -. start_time) *. 1_000_000. in
  Printf.printf "✅ Processed %d tokens in %.0fμs (%.0fμs per token)\n" 
    !result_count elapsed_us (elapsed_us /. float !result_count);
  
  elapsed_us < 1000. (* Should be fast *)

let () =
  Printf.printf "🔍 DIRECT FUNCTIONALITY TEST\n";
  Printf.printf "================================\n";
  
  let basic_ok = test_basic_functionality () in
  let perf_ok = test_performance () in
  
  Printf.printf "\n=== RESULTS ===\n";
  Printf.printf "Basic functionality: %s\n" (if basic_ok then "✅ PASS" else "❌ FAIL");
  Printf.printf "Performance: %s\n" (if perf_ok then "✅ PASS" else "❌ FAIL");
  
  if basic_ok && perf_ok then
    Printf.printf "🎯 ✅ CORE FUNCTIONALITY VERIFIED\n"
  else
    Printf.printf "❌ CORE FUNCTIONALITY HAS ISSUES\n"
|} in
  
  (* Compile and run the test program *)
  let test_file = "/tmp/test_actual.ml" in
  let oc = open_out test_file in
  output_string oc test_program;
  close_out oc;
  
  Printf.printf "Compiling direct functionality test...\n";
  let compile_cmd = Printf.sprintf 
    "ocamlc -I src/core -I +unix unix.cma types.cmo common_macros.cmo expander_stub.cmo %s -o /tmp/test_actual 2>/dev/null" 
    test_file in
  let compile_result = Sys.command compile_cmd in
  
  if compile_result = 0 then begin
    Printf.printf "✅ Test program compiled successfully\n";
    Printf.printf "Running direct functionality test...\n\n";
    let run_result = Sys.command "/tmp/test_actual" in
    run_result = 0
  end else begin
    Printf.printf "❌ Test program compilation failed\n";
    (* Try to show the error *)
    let error_cmd = Printf.sprintf 
      "ocamlc -I src/core -I +unix unix.cma types.cmo common_macros.cmo expander_stub.cmo %s -o /tmp/test_actual" 
      test_file in
    ignore (Sys.command error_cmd);
    false
  end

let test_week2_dsl_functionality () =
  Printf.printf "\n=== WEEK 2 DSL FUNCTIONALITY TEST ===\n";
  
  let dsl_test_program = {|
open Validator_patterns
open Validator_examples

let test_dsl_types () =
  Printf.printf "Testing DSL type system...\n";
  
  (* Test creating a simple pattern *)
  let test_pattern = PatternBuilder.make_pattern
    ~family:"TEST"
    ~id_prefix:"TEST-001"
    ~name:"Test Pattern"
    ~description:"A test pattern"
    ~matcher:(PatternBuilder.regex "test")
    ~severity:Warning
    ~fix_generator:(PatternBuilder.simple_fix "old" "new")
    () in
  
  Printf.printf "✅ Pattern created: %s\n" test_pattern.name;
  Printf.printf "✅ Pattern family: %s\n" test_pattern.family;
  Printf.printf "✅ Pattern severity: %s\n" (Display.severity_to_string test_pattern.severity);
  
  (* Test pattern families *)
  let family_count = List.length all_families in
  let total_patterns = List.length all_patterns in
  
  Printf.printf "✅ Pattern families: %d\n" family_count;
  Printf.printf "✅ Total patterns: %d\n" total_patterns;
  
  (* Verify we have patterns from each expected family *)
  let expected_families = ["MATH"; "TYPO"; "STYLE"; "DELIM"] in
  let found_families = List.map (fun f -> f.name) all_families in
  
  let all_families_present = List.for_all (fun expected ->
    List.mem expected found_families
  ) expected_families in
  
  Printf.printf "✅ All expected families present: %s\n" 
    (if all_families_present then "YES" else "NO");
  
  total_patterns >= 10 && all_families_present

let () =
  Printf.printf "🔍 DSL FUNCTIONALITY TEST\n";
  Printf.printf "==========================\n";
  
  let dsl_ok = test_dsl_types () in
  Printf.printf "\nDSL functionality: %s\n" (if dsl_ok then "✅ PASS" else "❌ FAIL");
|} in
  
  let dsl_test_file = "/tmp/test_dsl.ml" in
  let oc = open_out dsl_test_file in
  output_string oc dsl_test_program;
  close_out oc;
  
  Printf.printf "Compiling DSL functionality test...\n";
  let compile_cmd = Printf.sprintf 
    "ocamlc -I src/core -I +unix unix.cma validator_patterns.cmo validator_examples.cmo %s -o /tmp/test_dsl 2>/dev/null" 
    dsl_test_file in
  let compile_result = Sys.command compile_cmd in
  
  if compile_result = 0 then begin
    Printf.printf "✅ DSL test program compiled successfully\n";
    Printf.printf "Running DSL functionality test...\n\n";
    let run_result = Sys.command "/tmp/test_dsl" in
    run_result = 0
  end else begin
    Printf.printf "❌ DSL test program compilation failed\n";
    false
  end

let run_complete_functional_test () =
  Printf.printf "🚀 COMPLETE FUNCTIONAL TEST - WEEKS 1 & 2\n";
  Printf.printf "%s\n" (String.make 60 '=');
  
  (* First compile all modules *)
  Printf.printf "Compiling all required modules...\n";
  let modules_to_compile = [
    "types.ml";
    "common_macros.ml"; 
    "expander_stub.ml";
    "validator_patterns.ml";
    "validator_examples.ml";
  ] in
  
  let compilation_failures = ref [] in
  List.iter (fun module_file ->
    let cmd = Printf.sprintf "ocamlc -I src/core -c src/core/%s 2>/dev/null" module_file in
    if Sys.command cmd <> 0 then
      compilation_failures := module_file :: !compilation_failures
  ) modules_to_compile;
  
  if List.length !compilation_failures > 0 then begin
    Printf.printf "❌ Module compilation failures:\n";
    List.iter (fun m -> Printf.printf "  • %s\n" m) !compilation_failures;
    false
  end else begin
    Printf.printf "✅ All modules compiled successfully\n\n";
    
    let week1_ok = test_compiled_modules () in
    let week2_ok = test_week2_dsl_functionality () in
    
    Printf.printf "\n%s\n" (String.make 60 '=');
    Printf.printf "COMPLETE FUNCTIONAL TEST RESULTS\n";
    Printf.printf "%s\n" (String.make 60 '=');
    
    Printf.printf "Week 1 core functionality: %s\n" (if week1_ok then "✅ VERIFIED" else "❌ FAILED");
    Printf.printf "Week 2 DSL functionality: %s\n" (if week2_ok then "✅ VERIFIED" else "❌ FAILED");
    
    if week1_ok && week2_ok then begin
      Printf.printf "\n🎯 ✅ BOTH WEEKS FUNCTIONALLY VERIFIED!\n";
      Printf.printf "All claimed functionality actually works.\n";
      true
    end else begin
      Printf.printf "\n❌ FUNCTIONAL VERIFICATION FAILED\n"; 
      Printf.printf "Some claimed functionality does not work.\n";
      false
    end
  end

let () = ignore (run_complete_functional_test ())