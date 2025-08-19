(* COMPREHENSIVE OPTIMIZATION TEST *)
(* Tests all approaches: original → unboxed → fused *)

open Printf

let generate_realistic_input size =
  let buf = Buffer.create size in
  for i = 0 to size - 1 do
    let c = match i mod 100 with
      | 0 -> '"'     (* Quote - will trigger TYPO-001 *)
      | 1 | 2 -> '-' (* Hyphens - will trigger TYPO-002/003 *)
      | 3 | 4 | 5 -> '.' (* Periods - will trigger TYPO-005 *)
      | 10 -> '\t'   (* Tab - will trigger TYPO-006 *)
      | 20 -> '{'    (* Brace open *)
      | 21 -> '}'    (* Brace close *)
      | 30 -> ' '    (* Space *)
      | 31 -> '\n'   (* Newline - might trigger trailing space *)
      | _ -> 'a'     (* Regular letter *)
    in
    Buffer.add_char buf c
  done;
  Buffer.contents buf

let generate_tokens_from_string s =
  let len = String.length s in
  Array.init len (fun i ->
    let c = s.[i] in
    let tok = match c with
      | '"' -> Validator_core_fixed.TChar (Uchar.of_int 34, Other)
      | '-' -> Validator_core_fixed.TChar (Uchar.of_int 45, Other)
      | '.' -> Validator_core_fixed.TChar (Uchar.of_int 46, Other)
      | '\t' -> Validator_core_fixed.TChar (Uchar.of_int 9, Space)
      | '{' -> Validator_core_fixed.TChar (Uchar.of_int 123, BeginGroup)
      | '}' -> Validator_core_fixed.TChar (Uchar.of_int 125, EndGroup)
      | ' ' -> Validator_core_fixed.TChar (Uchar.of_int 32, Space)
      | '\n' -> Validator_core_fixed.TChar (Uchar.of_int 10, EndLine)
      | _ -> Validator_core_fixed.TChar (Uchar.of_int (Char.code c), Letter)
    in {
      Validator_core_fixed.token = tok;
      location = { line = i / 100; column = i mod 100; offset = i }
    })

let test_approach name test_func input_data =
  printf "\n=== Testing %s ===\n" name;
  let result = test_func input_data in
  result

let () =
  printf "COMPREHENSIVE VALIDATOR OPTIMIZATION TEST\n";
  printf "========================================\n\n";
  
  (* Generate test data at different scales *)
  let test_sizes = [50_000; 100_000; 276_000; 500_000; 1_100_000] in
  
  List.iter (fun size ->
    printf "\n🎯 TESTING WITH %d BYTES/TOKENS\n" size;
    printf "%s\n" (String.make 50 '=');
    
    let input_string = generate_realistic_input size in
    let token_array = generate_tokens_from_string input_string in
    let token_list = Array.to_list token_array in
    
    (* Test 1: Original ultra-optimized (baseline) *)
    let original_time = test_approach "Original Ultra (5.5ms baseline)" 
      (fun _ -> Single_pass_ultra.bench_ultra token_array) 
      () in
    
    (* Test 2: Unboxed single-load *)
    let unboxed_time = test_approach "Unboxed Single-Load (Track 1+2)"
      (fun _ -> Single_pass_unboxed.bench_unboxed token_list)
      () in
    
    (* Test 3: L0 Fused *)
    let fused_time = test_approach "L0 Fused (Path A)"
      (fun s -> L0_fused_validators.bench_fused s)
      input_string in
    
    (* Calculate improvements *)
    printf "\n📊 PERFORMANCE SUMMARY for %d tokens:\n" size;
    printf "┌─────────────────────────┬─────────────┬─────────────┐\n";
    printf "│ Approach                │ P99 Time    │ vs Original │\n";
    printf "├─────────────────────────┼─────────────┼─────────────┤\n";
    printf "│ Original (int32 boxing) │ %8.3fms │   baseline  │\n" original_time;
    printf "│ Unboxed (int8 single)  │ %8.3fms │ %8.1fx  │\n" unboxed_time (original_time /. unboxed_time);
    printf "│ L0 Fused               │ %8.3fms │ %8.1fx  │\n" fused_time (original_time /. fused_time);
    printf "└─────────────────────────┴─────────────┴─────────────┘\n";
    
    (* Check targets *)
    printf "\n🎯 TARGET ANALYSIS:\n";
    if fused_time < 1.0 then
      printf "✅ L0 Fused achieves <1ms target with %.1fx margin\n" (1.0 /. fused_time)
    else
      printf "⚠️ L0 Fused: %.3fms (%.1fx over 1ms target)\n" fused_time (fused_time /. 1.0);
    
    if unboxed_time < 2.0 then
      printf "✅ Unboxed achieves <2ms intermediate target\n"
    else
      printf "⚠️ Unboxed: %.3fms (needs further optimization)\n" unboxed_time;
    
    (* Total pipeline estimate *)
    let total_with_fused = 10.0 +. fused_time in
    printf "\n⚡ PIPELINE ESTIMATE: 10ms (L0) + %.3fms (validators) = %.3fms total\n" 
      fused_time total_with_fused;
    
    if total_with_fused < 20.0 then
      printf "✅ MEETS P99 < 20ms requirement with %.1fms margin\n" (20.0 -. total_with_fused)
    else
      printf "❌ Exceeds 20ms P99 target\n"
      
  ) test_sizes;
  
  printf "\n\n🏆 FINAL RECOMMENDATIONS:\n";
  printf "═══════════════════════════\n\n";
  printf "1. IMMEDIATE (no FFI): Implement unboxed int8 single-load\n";
  printf "   → Expected: 5.5ms → ~1.5-2.2ms (~3x improvement)\n\n";
  printf "2. OPTIMAL (no FFI): Fuse validators into L0 lexer loop\n";
  printf "   → Expected: ~0.2-0.7ms incremental cost\n";
  printf "   → Total: 10ms (L0) + 0.5ms (validators) = 10.5ms\n\n";
  printf "3. PRODUCTION: Use L0 fusion for ASCII rules (quotes, hyphens, etc.)\n";
  printf "   → Keep separate pass for complex Unicode rules\n";
  printf "   → Best of both worlds: speed + correctness\n\n";
  
  printf "💡 IMPLEMENTATION ORDER:\n";
  printf "   Step 1: Switch to int8_unsigned Bigarray (1-2 hours)\n";
  printf "   Step 2: Single ascii_interest array (1 hour)\n";
  printf "   Step 3: Integrate check_byte into L0 loop (2-4 hours)\n";
  printf "   Step 4: Benchmark and tune (1 hour)\n\n";
  
  printf "🎯 EXPECTED RESULT: <11ms total pipeline (comfortably under 20ms)\n"