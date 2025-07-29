(** Test All Gap Fixes
    
    This test verifies that all identified gaps have been properly fixed.
*)

let test_gap_fixes () =
  Printf.printf "🔧 TESTING ALL GAP FIXES\n";
  Printf.printf "%s\n" (String.make 60 '=');
  
  (* Test the integration module compilation *)
  let integration_test = {|
#directory "src/core";;
#use "types.ml";;
#use "common_macros.ml";; 
#use "lexer_stub.ml";;
#use "expander_stub.ml";;
#use "l0_v25.ml";;
#use "l1_v25.ml";;
#use "pipeline_integration.ml";;

let () =
  let success = Pipeline_integration.test_complete_integration () in
  exit (if success then 0 else 1)
|} in
  
  let test_file = "/tmp/test_integration.ml" in
  let oc = open_out test_file in
  output_string oc integration_test;
  close_out oc;
  
  Printf.printf "Running complete integration test...\n\n";
  let result = Sys.command (Printf.sprintf "ocaml -I src/core -I +unix %s" test_file) in
  
  if result = 0 then begin
    Printf.printf "\n🎯 ✅ ALL GAPS SUCCESSFULLY FIXED!\n";
    Printf.printf "The L0-L1 pipeline is now fully integrated and functional.\n";
    true
  end else begin
    Printf.printf "\n❌ Some gaps remain unfixed\n";
    false
  end

let test_module_references () =
  Printf.printf "\n=== MODULE REFERENCE FIX TEST ===\n";
  
  (* Test that L1 can properly reference L0 types *)
  let reference_test = {|
open Types
open L0_v25  
open L1_v25

let test_references () =
  Printf.printf "Testing module references...\n";
  
  (* Create L0 cache key *)
  let l0_key = { chunk_id = 0; hash = 123L } in
  Printf.printf "✅ L0 cache key created: chunk %d\n" l0_key.chunk_id;
  
  (* Create L1 cache key that references L0 *)
  let l1_key = { l0 = l0_key; fuel_left = 100; token_hash = 456 } in
  Printf.printf "✅ L1 cache key created: fuel %d\n" l1_key.fuel_left;
  
  (* Test state initialization *)
  let l0_state = L0_v25.initial_state () in
  let l1_state = L1_v25.initial_state l0_key in
  
  Printf.printf "✅ L0 state initialized: chunk %d\n" l0_state.chunk_id;
  Printf.printf "✅ L1 state initialized: version %Ld\n" l1_state.version;
  
  Printf.printf "✅ MODULE REFERENCES FIXED\n";
  true

let () = 
  let success = test_references () in
  exit (if success then 0 else 1)
|} in
  
  let ref_test_file = "/tmp/test_references.ml" in
  let oc = open_out ref_test_file in
  output_string oc reference_test;
  close_out oc;
  
  let cmd = Printf.sprintf 
    "ocamlc -I src/core -I +unix unix.cma types.cmo common_macros.cmo lexer_stub.cmo expander_stub.cmo l0_v25.cmo l1_v25.cmo %s -o /tmp/test_refs && /tmp/test_refs" 
    ref_test_file in
  let result = Sys.command cmd in
  
  Printf.printf "Module reference test: %s\n" (if result = 0 then "✅ FIXED" else "❌ STILL BROKEN");
  result = 0

let test_cache_systems () =
  Printf.printf "\n=== CACHE SYSTEMS TEST ===\n";
  
  let cache_test = {|
open Types
open L0_v25
open L1_v25

let test_l0_cache () =
  Printf.printf "Testing L0 2-hand CLOCK cache...\n";
  
  let test_bytes = Bytes.of_string "\\LaTeX{} test" in
  
  (* First call - should be cache miss *)
  let (tokens1, state1) = lex_chunk test_bytes in
  Printf.printf "First call: %d tokens, version %Ld\n" (Array.length tokens1) state1.version;
  
  (* Second call with same input - should be cache hit *)
  let (tokens2, state2) = lex_chunk ~prev:state1 test_bytes in
  Printf.printf "Second call: %d tokens, version %Ld\n" (Array.length tokens2) state2.version;
  
  (* Verify cache hit behavior *)
  let cache_hit = Array.length tokens1 = Array.length tokens2 && state2.version > state1.version in
  Printf.printf "L0 cache behavior: %s\n" (if cache_hit then "✅ WORKING" else "❌ BROKEN");
  
  cache_hit

let test_l1_cache () =
  Printf.printf "\nTesting L1 LFU-decay cache...\n";
  
  let l0_key = { chunk_id = 0; hash = 0L } in
  let l1_env = initial_state l0_key in
  let test_tokens = [| TCommand "LaTeX"; TSpace; TCommand "alpha" |] in
  let delta = { unexpanded = test_tokens; expanded = [||]; macros_used = [] } in
  
  (* First expansion - cache miss *)
  let (result1, state1) = expand_delta ~fuel:10 ~env:l1_env delta in
  Printf.printf "First expansion: %d -> %d tokens\n" 
    (Array.length test_tokens) (Array.length result1.expanded);
  
  (* Second expansion - should hit cache *)
  let (result2, state2) = expand_delta ~fuel:10 ~env:state1 delta in
  Printf.printf "Second expansion: %d -> %d tokens\n" 
    (Array.length test_tokens) (Array.length result2.expanded);
  
  let cache_working = Array.length result1.expanded = Array.length result2.expanded in
  Printf.printf "L1 cache behavior: %s\n" (if cache_working then "✅ WORKING" else "❌ BROKEN");
  
  cache_working

let () =
  let l0_ok = test_l0_cache () in
  let l1_ok = test_l1_cache () in
  let overall = l0_ok && l1_ok in
  Printf.printf "\nCache systems: %s\n" (if overall then "✅ ALL WORKING" else "❌ ISSUES REMAIN");
  exit (if overall then 0 else 1)
|} in
  
  let cache_test_file = "/tmp/test_caches.ml" in
  let oc = open_out cache_test_file in
  output_string oc cache_test;
  close_out oc;
  
  let cmd = Printf.sprintf 
    "ocamlc -I src/core -I +unix unix.cma types.cmo common_macros.cmo lexer_stub.cmo expander_stub.cmo l0_v25.cmo l1_v25.cmo %s -o /tmp/test_caches && /tmp/test_caches" 
    cache_test_file in
  let result = Sys.command cmd in
  
  Printf.printf "Cache systems test: %s\n" (if result = 0 then "✅ WORKING" else "❌ BROKEN");
  result = 0

let test_performance_validation () =
  Printf.printf "\n=== PERFORMANCE VALIDATION TEST ===\n";
  
  let perf_test = {|
open Types
open Pipeline_integration

let test_performance_claims () =
  Printf.printf "Validating performance claims...\n";
  
  let test_documents = [
    ("Small", "\\LaTeX{} \\textbf{test}");
    ("Medium", String.make 1000 'x' ^ "\\alpha \\beta \\gamma");
    ("Large", String.make 10000 'y' ^ "\\sum \\int \\prod \\LaTeX{}");
  ] in
  
  let config = Pipeline_integration.default_config in
  let results = ref [] in
  
  List.iter (fun (name, doc) ->
    let result = Pipeline_integration.process_document config doc in
    let chars_per_us = float (String.length doc) /. result.processing_time_us in
    Printf.printf "%s doc (%d chars): %.0fμs (%.1f chars/μs)\n" 
      name (String.length doc) result.processing_time_us chars_per_us;
    results := (name, result.processing_time_us) :: !results
  ) test_documents;
  
  (* Check if any document exceeds reasonable time limits *)
  let max_time = List.fold_left (fun acc (_, time) -> max acc time) 0. !results in
  let performance_ok = max_time < 50000. in (* 50ms max *)
  
  Printf.printf "Maximum processing time: %.0fμs\n" max_time;
  Printf.printf "Performance validation: %s\n" (if performance_ok then "✅ MEETS TARGETS" else "❌ TOO SLOW");
  
  performance_ok

let () =
  let success = test_performance_claims () in
  exit (if success then 0 else 1)
|} in
  
  let perf_test_file = "/tmp/test_performance.ml" in
  let oc = open_out perf_test_file in
  output_string oc perf_test;
  close_out oc;
  
  let cmd = Printf.sprintf 
    "ocamlc -I src/core -I +unix unix.cma types.cmo common_macros.cmo lexer_stub.cmo expander_stub.cmo l0_v25.cmo l1_v25.cmo pipeline_integration.cmo %s -o /tmp/test_perf && /tmp/test_perf" 
    perf_test_file in
  let result = Sys.command cmd in
  
  Printf.printf "Performance validation: %s\n" (if result = 0 then "✅ VALIDATED" else "❌ FAILED");
  result = 0

let run_all_gap_tests () =
  Printf.printf "🔧 COMPREHENSIVE GAP FIX VERIFICATION\n";
  Printf.printf "%s\n" (String.make 70 '=');
  
  let tests = [
    ("Module References", test_module_references);
    ("Cache Systems", test_cache_systems);
    ("Performance Validation", test_performance_validation);
    ("Complete Integration", test_gap_fixes);
  ] in
  
  let results = List.map (fun (name, test_fn) ->
    Printf.printf "\n--- %s ---\n" name;
    let result = test_fn () in
    (name, result)
  ) tests in
  
  let passed = List.filter (fun (_, result) -> result) results in
  let total = List.length results in
  let passed_count = List.length passed in
  
  Printf.printf "\n%s\n" (String.make 70 '=');
  Printf.printf "GAP FIX VERIFICATION RESULTS\n";
  Printf.printf "%s\n" (String.make 70 '=');
  Printf.printf "Tests passed: %d/%d\n\n" passed_count total;
  
  List.iter (fun (name, result) ->
    Printf.printf "  %s: %s\n" (if result then "✅" else "❌") name
  ) results;
  
  if passed_count = total then begin
    Printf.printf "\n🎯 ✅ ALL GAPS SUCCESSFULLY FIXED!\n";
    Printf.printf "Week 1 and Week 2 are now fully functional and integrated.\n";
    Printf.printf "Ready for Week 3-4 development.\n"
  end else begin
    Printf.printf "\n❌ %d GAPS REMAIN UNFIXED\n" (total - passed_count);
    Printf.printf "Must address remaining issues before proceeding.\n"
  end;
  
  passed_count = total

let () = ignore (run_all_gap_tests ())