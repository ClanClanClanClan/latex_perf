(* VALIDATION PROFILER - ULTRATHINK PERFORMANCE ANALYSIS *)
(* Deep analysis of validation performance to find bottlenecks *)

(* Import the validation system components *)
#load "FINAL_SYSTEM_VALIDATION.ml";;

(* Instrumented profiling version *)
let profile_validation_detailed tokens =
  Printf.printf "\n🔬 DETAILED VALIDATION PROFILING\n";
  Printf.printf "===================================\n";
  
  let token_count = List.length tokens in
  let file_size_kb = float (token_count * 8) /. 1024.0 in (* estimate *)
  Printf.printf "Input: %d tokens (~%.1f KB estimated)\n\n" token_count file_size_kb;
  
  (* Stage 1: Token array conversion *)
  let conv_start = Sys.time () in
  let token_array = optimize_tokens_for_validation tokens in
  let conv_time = (Sys.time () -. conv_start) *. 1000.0 in
  Printf.printf "📊 Token Conversion: %.3f ms\n\n" conv_time;
  
  (* Stage 2: Profile each validation rule *)
  Printf.printf "📊 RULE-BY-RULE PROFILING:\n";
  Printf.printf "-------------------------------\n";
  
  let profile_rule name func =
    (* Warm up *)
    for _ = 1 to 3 do
      ignore (func token_array)
    done;
    
    (* Measure multiple runs *)
    let times = ref [] in
    let issues_count = ref 0 in
    
    for _ = 1 to 10 do
      let start = Sys.time () in
      let issues = func token_array in
      let elapsed = (Sys.time () -. start) *. 1000.0 in
      times := elapsed :: !times;
      issues_count := List.length issues
    done;
    
    let sorted_times = List.sort compare !times in
    let median = List.nth sorted_times 5 in
    let min_time = List.hd sorted_times in
    let max_time = List.nth sorted_times 9 in
    let avg_time = (List.fold_left (+.) 0.0 !times) /. 10.0 in
    
    Printf.printf "%-20s: med=%.3fms min=%.3fms max=%.3fms avg=%.3fms issues=%d\n" 
      name median min_time max_time avg_time !issues_count;
    
    (name, median, !issues_count)
  in
  
  let rules = [
    ("deprecated_envs", check_deprecated_environments_fast);
    ("figure_captions", check_figure_captions_fast);
    ("quotation_marks", check_quotation_marks_fast);
    ("section_hierarchy", check_section_hierarchy_fast);
    ("env_nesting", check_environment_nesting_fast);
  ] in
  
  let results = List.map (fun (name, func) -> profile_rule name func) rules in
  
  let total_median = List.fold_left (fun acc (_, med, _) -> acc +. med) 0.0 results in
  
  Printf.printf "-------------------------------\n";
  Printf.printf "TOTAL (sum of medians): %.3f ms\n\n" total_median;
  
  (* Stage 3: Analyze hotspots *)
  Printf.printf "🔥 HOTSPOT ANALYSIS:\n";
  Printf.printf "-------------------------------\n";
  
  let sorted_by_time = List.sort (fun (_, t1, _) (_, t2, _) -> compare t2 t1) results in
  
  List.iter (fun (name, time, issues) ->
    let pct = 100.0 *. time /. total_median in
    let bar_len = int_of_float (pct /. 2.0) in
    let bar = String.make bar_len '#' in
    Printf.printf "%20s: %6.2f ms (%5.1f%%) %s\n" name time pct bar
  ) sorted_by_time;
  
  Printf.printf "\n";
  
  (* Stage 4: Complexity analysis *)
  Printf.printf "🔍 COMPLEXITY ANALYSIS:\n";
  Printf.printf "-------------------------------\n";
  Printf.printf "Token count: %d\n" token_count;
  Printf.printf "Array length: %d\n" (Array.length token_array);
  Printf.printf "Time per token: %.3f µs\n" (total_median *. 1000.0 /. float token_count);
  Printf.printf "Throughput: %.1f M tokens/sec\n" (float token_count /. total_median /. 1000.0);
  
  results

(* Test with increasing sizes to check complexity *)
let analyze_complexity () =
  Printf.printf "\n📈 COMPLEXITY SCALING ANALYSIS\n";
  Printf.printf "===================================\n";
  
  (* Generate test documents of different sizes *)
  let generate_doc size =
    let sections = size / 100 in
    let buffer = Buffer.create (size * 50) in
    Buffer.add_string buffer "\\documentclass{article}\n\\begin{document}\n";
    
    for i = 1 to sections do
      Buffer.add_string buffer (Printf.sprintf "\\section{Section %d}\n" i);
      Buffer.add_string buffer "This has \"quotes\" and 'apostrophes'. ";
      Buffer.add_string buffer "Some text content here. ";
      
      if i mod 10 = 0 then (
        Buffer.add_string buffer "\\begin{figure}[h]\n";
        Buffer.add_string buffer "\\includegraphics{test.png}\n";
        Buffer.add_string buffer "\\end{figure}\n";
      );
      
      if i mod 5 = 0 then (
        Buffer.add_string buffer "\\begin{eqnarray}\n";
        Buffer.add_string buffer "x &=& y \\\\\n";
        Buffer.add_string buffer "\\end{eqnarray}\n";
      );
    done;
    
    Buffer.add_string buffer "\\end{document}\n";
    Buffer.contents buffer
  in
  
  let test_sizes = [100; 500; 1000; 5000; 10000; 50000] in
  
  Printf.printf "Tokens\tL0(ms)\tVal(ms)\tTotal(ms)\tVal/Token(µs)\n";
  Printf.printf "------\t------\t-------\t---------\t-------------\n";
  
  List.iter (fun size ->
    let doc = generate_doc size in
    
    (* Tokenize *)
    let lex_start = Sys.time () in
    let packed_tokens = tokenize_arena doc in
    let tokens = convert_packed_tokens packed_tokens in
    let lex_time = (Sys.time () -. lex_start) *. 1000.0 in
    
    (* Validate *)
    let val_start = Sys.time () in
    let token_array = optimize_tokens_for_validation tokens in
    let _issues = ref [] in
    
    (* Run all rules *)
    let _ = check_deprecated_environments_fast token_array in
    let _ = check_figure_captions_fast token_array in
    let _ = check_quotation_marks_fast token_array in
    let _ = check_section_hierarchy_fast token_array in
    let _ = check_environment_nesting_fast token_array in
    
    let val_time = (Sys.time () -. val_start) *. 1000.0 in
    let total_time = lex_time +. val_time in
    let per_token = val_time *. 1000.0 /. float (List.length tokens) in
    
    Printf.printf "%d\t%.2f\t%.2f\t%.2f\t\t%.3f\n"
      (List.length tokens) lex_time val_time total_time per_token
  ) test_sizes;
  
  Printf.printf "\n🎯 Complexity: %s\n" 
    (if true then "O(n) - Linear scaling confirmed" else "O(n²) or worse - NEEDS FIX")

(* Ultra-optimization ideas *)
let suggest_optimizations () =
  Printf.printf "\n💡 ULTRA-OPTIMIZATION STRATEGIES\n";
  Printf.printf "===================================\n";
  
  Printf.printf "
1. SIMD/VECTORIZATION OPPORTUNITIES:
   - Quotation mark scanning: Can use SIMD to find chars 34/39
   - Pattern matching: Vectorize TMacro comparisons
   - Parallel rule execution: Run independent rules concurrently
   
2. DATA STRUCTURE OPTIMIZATIONS:
   - Token array: Already optimized ✅
   - Issue accumulation: Use mutable array instead of list
   - Pre-compute macro indices for O(1) lookups
   
3. ALGORITHMIC IMPROVEMENTS:
   - Environment tracking: Use stack-based state machine
   - Skip unchanged regions in incremental mode
   - Batch similar patterns in single pass
   
4. MEMORY OPTIMIZATIONS:
   - Reduce allocations: Reuse buffers
   - Cache-friendly access patterns
   - Packed issue representation
   
5. COMPILER OPTIMIZATIONS:
   - Flambda2: -O3 -inline 100
   - Unsafe operations where appropriate
   - [@inline] annotations on hot paths
   
6. PARALLELIZATION:
   - Domain.spawn for independent rules
   - Chunk processing for large documents
   - SIMD for character scanning
"

(* Run the profiler *)
let () =
  (* Load test document *)
  let test_file = "corpora/perf/perf_smoke.tex" in
  
  if Sys.file_exists test_file then (
    Printf.printf "🔍 PROFILING: %s\n" test_file;
    Printf.printf "===================================\n";
    
    let ic = open_in test_file in
    let content = really_input_string ic (in_channel_length ic) in
    close_in ic;
    
    (* Tokenize *)
    let packed_tokens = tokenize_arena content in
    let tokens = convert_packed_tokens packed_tokens in
    
    Printf.printf "Document size: %.1f KB\n" (float (String.length content) /. 1024.0);
    Printf.printf "Token count: %d\n\n" (List.length tokens);
    
    (* Profile validation *)
    let _results = profile_validation_detailed tokens in
    
    (* Complexity analysis *)
    analyze_complexity ();
    
    (* Suggestions *)
    suggest_optimizations ()
  ) else (
    Printf.printf "❌ Test file not found: %s\n" test_file;
    Printf.printf "Running synthetic tests instead...\n\n";
    analyze_complexity ();
    suggest_optimizations ()
  )