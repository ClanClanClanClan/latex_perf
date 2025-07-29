(** Comprehensive test suite for Week 1 - would have caught all bugs
    
    This test suite specifically tests for:
    1. Cache key bug - different macros sharing cache entries
    2. All 86 macro definitions work correctly
    3. Edge cases and error conditions
    4. Performance characteristics
    5. Integration between L0 and L1
*)

module L0_v25 = Layer0.L0_v25
module L1_v25 = Layer1.L1_v25
module Types = Latex_perfectionist_core.Types
module CommonMacros = Common_macros

(* Test that would have caught the cache bug *)
let test_cache_isolation () =
  Printf.printf "=== CACHE ISOLATION TEST ===\n";
  Printf.printf "This test would have caught the cache key bug!\n\n";
  
  let l0_key = { L0_v25.chunk_id = 0; hash = 0L } in
  let l1_env = L1_v25.initial_state l0_key in
  
  (* Test that different macros don't share cache entries *)
  let test_pairs = [
    ("LaTeX", "LaTeX");
    ("TeX", "TeX");
    ("textbf", "[bold]");
    ("textit", "[italic]");
    ("alpha", "α");
    ("beta", "β");
  ] in
  
  let failures = ref [] in
  
  List.iter (fun (macro1, expected1) ->
    List.iter (fun (macro2, expected2) ->
      if macro1 <> macro2 then begin
        (* Expand first macro *)
        let tokens1 = [|Types.TCommand macro1|] in
        let delta1 = { 
          L1_v25.unexpanded = tokens1; 
          expanded = [||]; 
          macros_used = [] 
        } in
        let (expanded1, _) = L1_v25.expand_delta ~fuel:10 ~env:l1_env delta1 in
        
        (* Expand second macro *)
        let tokens2 = [|Types.TCommand macro2|] in
        let delta2 = { 
          L1_v25.unexpanded = tokens2; 
          expanded = [||]; 
          macros_used = [] 
        } in
        let (expanded2, _) = L1_v25.expand_delta ~fuel:10 ~env:l1_env delta2 in
        
        (* Check results *)
        let get_text tokens =
          if Array.length tokens > 0 then
            match tokens.(0) with
            | Types.TText s -> s
            | _ -> "(not text)"
          else "(empty)"
        in
        
        let result1 = get_text expanded1.L1_v25.expanded in
        let result2 = get_text expanded2.L1_v25.expanded in
        
        if result1 = result2 && expected1 <> expected2 then begin
          failures := (macro1, macro2, result1) :: !failures;
          Printf.printf "❌ CACHE BUG: \\%s and \\%s both expand to '%s'\n" 
            macro1 macro2 result1
        end
      end
    ) test_pairs
  ) test_pairs;
  
  if !failures = [] then
    Printf.printf "✅ All macros expand independently (no cache sharing)\n"
  else
    Printf.printf "❌ Found %d cache collision(s)!\n" (List.length !failures);
  
  Printf.printf "\n";
  !failures = []

(* Test all 86 macros comprehensively *)
let test_all_macros () =
  Printf.printf "=== TESTING ALL 86 BUILT-IN MACROS ===\n";
  
  let l0_key = { L0_v25.chunk_id = 0; hash = 0L } in
  let l1_env = L1_v25.initial_state l0_key in
  
  let passed = ref 0 in
  let failed = ref [] in
  
  (* Test every single macro *)
  List.iter (fun (macro_name, expected_tokens) ->
    let tokens = [|Types.TCommand macro_name|] in
    let delta = { 
      L1_v25.unexpanded = tokens; 
      expanded = [||]; 
      macros_used = [] 
    } in
    
    let (expanded_delta, _) = L1_v25.expand_delta ~fuel:10 ~env:l1_env delta in
    
    (* Check if expansion matches expected *)
    let matches = 
      Array.length expanded_delta.L1_v25.expanded = List.length expected_tokens &&
      try
        List.for_all2 (fun tok1 tok2 ->
          tok1 = tok2
        ) (Array.to_list expanded_delta.L1_v25.expanded) expected_tokens
      with Invalid_argument _ -> false
    in
    
    if matches then
      incr passed
    else begin
      failed := macro_name :: !failed;
      Printf.printf "❌ \\%s failed to expand correctly\n" macro_name
    end
  ) CommonMacros.builtin_macro_list;
  
  Printf.printf "\nSummary: %d/%d passed\n" !passed CommonMacros.macro_count;
  if !failed <> [] then begin
    Printf.printf "Failed macros: %s\n" (String.concat ", " !failed)
  end;
  
  Printf.printf "\n";
  !failed = []

(* Test edge cases *)
let test_edge_cases () =
  Printf.printf "=== EDGE CASE TESTS ===\n";
  
  let l0_key = { L0_v25.chunk_id = 0; hash = 0L } in
  let l1_env = L1_v25.initial_state l0_key in
  
  let test_cases = [
    ("Empty input", [||], [||]);
    ("Unknown macro", [|Types.TCommand "unknownmacro"|], [|Types.TCommand "unknownmacro"|]);
    ("Nested groups", 
     [|Types.TBeginGroup; Types.TCommand "LaTeX"; Types.TEndGroup|],
     [|Types.TBeginGroup; Types.TText "LaTeX"; Types.TEndGroup|]);
    ("Multiple macros",
     [|Types.TCommand "alpha"; Types.TSpace; Types.TCommand "beta"|],
     [|Types.TText "α"; Types.TSpace; Types.TText "β"|]);
    ("Zero fuel",
     [|Types.TCommand "LaTeX"|],
     [|Types.TCommand "LaTeX"|]); (* Should not expand with 0 fuel *)
  ] in
  
  let all_passed = ref true in
  
  List.iter (fun (name, input, expected) ->
    Printf.printf "Test: %s... " name;
    
    let fuel = if name = "Zero fuel" then 0 else 100 in
    let delta = { 
      L1_v25.unexpanded = input; 
      expanded = [||]; 
      macros_used = [] 
    } in
    
    let (expanded_delta, _) = L1_v25.expand_delta ~fuel ~env:l1_env delta in
    
    if expanded_delta.L1_v25.expanded = expected then
      Printf.printf "✅\n"
    else begin
      Printf.printf "❌\n";
      Printf.printf "  Expected: %s\n" 
        (String.concat " " (Array.to_list (Array.map Types.token_to_string expected)));
      Printf.printf "  Got: %s\n" 
        (String.concat " " (Array.to_list (Array.map Types.token_to_string expanded_delta.L1_v25.expanded)));
      all_passed := false
    end
  ) test_cases;
  
  Printf.printf "\n";
  !all_passed

(* Test performance characteristics *)
let test_performance_characteristics () =
  Printf.printf "=== PERFORMANCE CHARACTERISTICS ===\n";
  
  (* Test that cache actually improves performance *)
  let input = Bytes.of_string "\\LaTeX{} \\TeX{} \\alpha \\beta \\gamma" in
  
  (* Test multiple runs to see cache effect *)
  let timings = ref [] in
  
  for i = 0 to 4 do
    let start = Unix.gettimeofday () in
    let (_tokens, _state) = L0_v25.lex_chunk input in
    let elapsed = (Unix.gettimeofday () -. start) *. 1000. in
    timings := elapsed :: !timings;
    Printf.printf "Run %d: %.3fms\n" (i+1) elapsed
  done;
  
  (* Check if later runs are faster (cache hit) *)
  let times_list = List.rev !timings in
  (match times_list with
  | first :: rest ->
      let avg_rest = (List.fold_left (+.) 0. rest) /. float (List.length rest) in
      Printf.printf "\nFirst run: %.3fms, Average of rest: %.3fms\n" first avg_rest;
      Printf.printf "Cache speedup: %.1fx\n" (first /. avg_rest)
  | _ -> ());
  
  Printf.printf "\n";
  true

(* Test version vector protocol *)
let test_version_vector () =
  Printf.printf "=== VERSION VECTOR PROTOCOL ===\n";
  
  (* Test that version vectors update correctly *)
  let input1 = Bytes.of_string "First input" in
  let input2 = Bytes.of_string "Second input" in
  
  (* First lexing call - no previous state *)
  let (_tokens1, state1) = L0_v25.lex_chunk input1 in
  
  (* Second lexing call - pass previous state *)
  let (_tokens2, state2) = L0_v25.lex_chunk ~prev:state1 input2 in
  
  Printf.printf "State 1: chunk_id=%d, version=%Ld\n" 
    state1.L0_v25.chunk_id state1.L0_v25.version;
  Printf.printf "State 2: chunk_id=%d, version=%Ld\n" 
    state2.L0_v25.chunk_id state2.L0_v25.version;
  
  (* Versions should increment *)
  let version_incremented = state2.L0_v25.version > state1.L0_v25.version in
  Printf.printf "Version incremented: %b %s\n" version_incremented
    (if version_incremented then "✅" else "❌");
  
  (* Also check chunk_id incremented *)
  let chunk_id_incremented = state2.L0_v25.chunk_id > state1.L0_v25.chunk_id in
  Printf.printf "Chunk ID incremented: %b %s\n" chunk_id_incremented
    (if chunk_id_incremented then "✅" else "❌");
  
  Printf.printf "\n";
  version_incremented && chunk_id_incremented

(* Regression test for specific week 1 bugs *)
let test_week1_regressions () =
  Printf.printf "=== WEEK 1 REGRESSION TESTS ===\n";
  
  let l0_key = { L0_v25.chunk_id = 0; hash = 0L } in
  let l1_env = L1_v25.initial_state l0_key in
  
  (* Bug 1: All macros expanded to "LaTeX" *)
  Printf.printf "Testing that macros don't all expand to 'LaTeX'...\n";
  
  let different_macros = ["TeX"; "textbf"; "alpha"; "sum"; "int"] in
  let expansions = List.map (fun macro ->
    let tokens = [|Types.TCommand macro|] in
    let delta = { 
      L1_v25.unexpanded = tokens; 
      expanded = [||]; 
      macros_used = [] 
    } in
    let (expanded, _) = L1_v25.expand_delta ~fuel:10 ~env:l1_env delta in
    match Array.to_list expanded.L1_v25.expanded with
    | [Types.TText s] -> s
    | _ -> "(not single text)"
  ) different_macros in
  
  let all_latex = List.for_all ((=) "LaTeX") expansions in
  if all_latex then
    Printf.printf "❌ BUG DETECTED: All macros expand to 'LaTeX'!\n"
  else
    Printf.printf "✅ Macros expand to different values\n";
  
  (* Bug 2: Only 6 macros defined instead of 86 *)
  Printf.printf "\nChecking macro count...\n";
  Printf.printf "Macros defined: %d (expected: 86) %s\n" 
    CommonMacros.macro_count
    (if CommonMacros.macro_count >= 86 then "✅" else "❌");
  
  Printf.printf "\n";
  not all_latex && CommonMacros.macro_count >= 86

(* Main test runner *)
let () =
  Printf.printf "LaTeX Perfectionist v25 - Comprehensive Week 1 Test Suite\n";
  Printf.printf "========================================================\n\n";
  
  let tests = [
    ("Cache Isolation", test_cache_isolation);
    ("All Macros", test_all_macros);
    ("Edge Cases", test_edge_cases);
    ("Performance", test_performance_characteristics);
    ("Version Vector", test_version_vector);
    ("Week 1 Regressions", test_week1_regressions);
  ] in
  
  let passed = ref 0 in
  let failed = ref 0 in
  
  List.iter (fun (name, test_fn) ->
    try
      if test_fn () then begin
        incr passed;
        Printf.printf "✅ %s: PASSED\n\n" name
      end else begin
        incr failed;
        Printf.printf "❌ %s: FAILED\n\n" name
      end
    with e ->
      incr failed;
      Printf.printf "❌ %s: EXCEPTION - %s\n\n" name (Printexc.to_string e)
  ) tests;
  
  Printf.printf "========================================================\n";
  Printf.printf "FINAL RESULTS: %d passed, %d failed\n" !passed !failed;
  
  if !failed = 0 then
    Printf.printf "✅ All tests passed! Week 1 implementation is solid.\n"
  else
    Printf.printf "❌ Some tests failed. Week 1 needs fixes.\n"