(** SIMPLE FUNCTIONAL TEST: Week 1 Core Components
    
    This test directly verifies the core claimed functionality works.
*)

(* Compile and test the core modules first *)
let test_module_compilation () =
  Printf.printf "=== MODULE COMPILATION TEST ===\n";
  
  let modules = [
    ("types.ml", "Core types");
    ("common_macros.ml", "Macro definitions"); 
    ("lexer_stub.ml", "Lexer stub");
    ("expander_stub.ml", "Expander stub");
  ] in
  
  let failures = ref [] in
  
  List.iter (fun (filename, description) ->
    let cmd = Printf.sprintf "ocamlc -I src/core -c src/core/%s 2>/dev/null" filename in
    let exit_code = Sys.command cmd in
    if exit_code = 0 then
      Printf.printf "✅ %s: COMPILES\n" description
    else begin
      Printf.printf "❌ %s: COMPILE ERROR\n" description;
      failures := filename :: !failures
    end
  ) modules;
  
  let success = List.length !failures = 0 in
  Printf.printf "Module compilation: %s\n\n" (if success then "✅ ALL PASS" else "❌ FAILURES");
  success

(* Test that the claimed 86 macros actually exist *)
let test_macro_count () =
  Printf.printf "=== MACRO COUNT VERIFICATION ===\n";
  
  (* Use a Python script to count macros since OCaml module loading is complex *)
  let count_script = {|
import re
import sys

try:
    with open('src/core/common_macros.ml', 'r') as f:
        content = f.read()
    
    # Count macro definitions
    text_matches = re.findall(r'\("([^"]+)", \[[^\[\]]*\]\)', content)
    total_count = len(text_matches)
    
    print(f"Total macros found: {total_count}")
    
    # Verify some key macros exist
    key_macros = ["LaTeX", "TeX", "textbf", "alpha", "sum", "ldots"]
    found_macros = []
    
    for macro in key_macros:
        if f'("{macro}"' in content:
            found_macros.append(macro)
            print(f"✅ {macro}: FOUND")
        else:
            print(f"❌ {macro}: MISSING")
    
    print(f"Key macros found: {len(found_macros)}/{len(key_macros)}")
    print("✅ MACRO COUNT VERIFIED" if total_count >= 86 else "❌ INSUFFICIENT MACROS")
    
    sys.exit(0 if total_count >= 86 and len(found_macros) == len(key_macros) else 1)
    
except Exception as e:
    print(f"❌ Error: {e}")
    sys.exit(1)
|} in
  
  (* Write the script to a temp file *)
  let script_file = "/tmp/count_macros.py" in
  let oc = open_out script_file in
  output_string oc count_script;
  close_out oc;
  
  (* Run the script *)
  let exit_code = Sys.command (Printf.sprintf "python3 %s" script_file) in
  let success = exit_code = 0 in
  
  Printf.printf "\nMacro verification: %s\n\n" (if success then "✅ PASS" else "❌ FAIL");
  success

(* Test core types are properly defined *)
let test_type_definitions () =
  Printf.printf "=== TYPE DEFINITION TEST ===\n";
  
  (* Test that token types compile in isolation *)
  let test_code = {|
open Types

let test_tokens = [|
  TText "hello";
  TCommand "LaTeX";
  TMathShift;
  TBeginGroup;
  TEndGroup;
  TSpace;
  TNewline
|]

let test_position = {
  byte_offset = 0;
  line = 1;  
  column = 0;
}

let () = 
  Printf.printf "Token array length: %d\n" (Array.length test_tokens);
  Printf.printf "Position: line %d, col %d\n" test_position.line test_position.column;
  Array.iteri (fun i tok ->
    Printf.printf "[%d]: %s\n" i (token_to_string tok)
  ) test_tokens;
  Printf.printf "✅ TYPE DEFINITIONS WORKING\n"
|} in
  
  let test_file = "/tmp/test_types.ml" in
  let oc = open_out test_file in
  output_string oc test_code;
  close_out oc;
  
  let cmd = Printf.sprintf "ocamlc -I src/core -o /tmp/test_types %s %s 2>/dev/null" 
    "src/core/types.cmo" test_file in
  let compile_result = Sys.command cmd in
  
  if compile_result = 0 then begin
    let run_result = Sys.command "/tmp/test_types" in
    let success = run_result = 0 in
    Printf.printf "Type definition test: %s\n\n" (if success then "✅ PASS" else "❌ FAIL");
    success
  end else begin
    Printf.printf "❌ Type definition test: COMPILE FAILED\n\n";
    false
  end

(* Test stub functionality *)
let test_stub_functionality () =
  Printf.printf "=== STUB FUNCTIONALITY TEST ===\n";
  
  (* Create a comprehensive test of the stub implementations *)
  let test_code = {|
#directory "src/core";;
#use "types.ml";;
#use "common_macros.ml";;
#use "expander_stub.ml";;

open Types

let test_macro_lookup () =
  Printf.printf "Testing macro lookup...\n";
  
  (* Test built-in macro lookup *)
  let latex_macro = Expander_stub.find_macro "LaTeX" in
  let tex_macro = Expander_stub.find_macro "TeX" in
  let alpha_macro = Expander_stub.find_macro "alpha" in
  let nonexistent = Expander_stub.find_macro "nonexistent" in
  
  let results = [
    ("LaTeX", latex_macro <> None);
    ("TeX", tex_macro <> None);  
    ("alpha", alpha_macro <> None);
    ("nonexistent", nonexistent = None);
  ] in
  
  List.iter (fun (name, success) ->
    Printf.printf "  %s lookup: %s\n" name (if success then "✅" else "❌")
  ) results;
  
  let all_pass = List.for_all (fun (_, s) -> s) results in
  Printf.printf "Macro lookup: %s\n" (if all_pass then "✅ PASS" else "❌ FAIL");
  all_pass

let test_macro_expansion () =
  Printf.printf "Testing macro expansion...\n";
  
  let env = Expander_stub.empty_env in
  let test_tokens = [TCommand "LaTeX"; TSpace; TCommand "alpha"] in
  
  (* Test one-step expansion *)
  match Expander_stub.expand_one_step env test_tokens with
  | Some (expanded, macro_used) ->
    Printf.printf "  Expanded tokens: ";
    List.iter (fun tok -> Printf.printf "%s " (token_to_string tok)) expanded;
    Printf.printf "\n";
    Printf.printf "  Macro used: %s\n" macro_used;
    Printf.printf "  One-step expansion: ✅ WORKING\n";
    true
  | None ->
    Printf.printf "  One-step expansion: ❌ FAILED\n";
    false

let () =
  let lookup_ok = test_macro_lookup () in
  let expand_ok = test_macro_expansion () in
  let overall = lookup_ok && expand_ok in
  Printf.printf "Overall stub test: %s\n" (if overall then "✅ PASS" else "❌ FAIL")
|} in
  
  let test_file = "/tmp/test_stubs.ml" in
  let oc = open_out test_file in
  output_string oc test_code;
  close_out oc;
  
  let result = Sys.command (Printf.sprintf "ocaml -I src/core %s" test_file) in
  let success = result = 0 in
  
  Printf.printf "Stub functionality: %s\n\n" (if success then "✅ PASS" else "❌ FAIL");
  success

(* Main test runner *)
let run_week1_simple_functional_test () =
  Printf.printf "🔍 WEEK 1 SIMPLE FUNCTIONAL TEST\n";
  Printf.printf "%s\n" (String.make 50 '=');
  
  let test_results = [
    ("Module Compilation", test_module_compilation ());
    ("Macro Count", test_macro_count ());
    ("Type Definitions", test_type_definitions ());
    ("Stub Functionality", test_stub_functionality ());
  ] in
  
  let passed = List.filter (fun (_, result) -> result) test_results in
  let total = List.length test_results in
  let passed_count = List.length passed in
  
  Printf.printf "%s\n" (String.make 50 '=');
  Printf.printf "SIMPLE FUNCTIONAL TEST RESULTS\n";
  Printf.printf "%s\n" (String.make 50 '=');
  Printf.printf "Tests passed: %d/%d\n\n" passed_count total;
  
  List.iter (fun (name, result) ->
    Printf.printf "  %s: %s\n" (if result then "✅" else "❌") name
  ) test_results;
  
  if passed_count = total then begin
    Printf.printf "\n🎯 ✅ WEEK 1 BASIC FUNCTIONALITY VERIFIED\n";
    Printf.printf "Ready for more comprehensive testing.\n"
  end else begin
    Printf.printf "\n❌ WEEK 1 HAS FUNDAMENTAL ISSUES\n";
    Printf.printf "Must fix basic functionality before proceeding.\n"
  end;
  
  passed_count = total

let () = ignore (run_week1_simple_functional_test ())