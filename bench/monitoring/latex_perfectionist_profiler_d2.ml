(* D2: Micro-benchmark Profiling - Complete Expert Recommendation *)

open Printf
open Unix

(* ========== D2: Micro-benchmark Profiling Framework ========== *)
module MicroBenchmark = struct
  type benchmark_result = {
    operation: string;
    iterations: int;
    total_time_ms: float;
    average_time_ms: float;
    min_time_ms: float;
    max_time_ms: float;
    std_dev_ms: float;
  }
  
  type profiler_config = {
    warmup_iterations: int;
    measurement_iterations: int;
    gc_between_runs: bool;
    detailed_output: bool;
  }
  
  let default_config = {
    warmup_iterations = 100;
    measurement_iterations = 1000;
    gc_between_runs = true;
    detailed_output = false;
  }
  
  let time_operation f =
    let start = Unix.gettimeofday () in
    let result = f () in
    let elapsed = (Unix.gettimeofday () -. start) *. 1000.0 in
    (result, elapsed)
  
  let calculate_stats times =
    let count = List.length times in
    let total = List.fold_left (+.) 0.0 times in
    let average = total /. float_of_int count in
    let min_time = List.fold_left min max_float times in
    let max_time = List.fold_left max 0.0 times in
    
    let variance = List.fold_left (fun acc t -> 
      acc +. (t -. average) ** 2.0) 0.0 times /. float_of_int count in
    let std_dev = sqrt variance in
    
    (total, average, min_time, max_time, std_dev)
  
  let run_benchmark config operation_name operation =
    printf "🔬 D2 Micro-benchmark: %s\n" operation_name;
    
    (* Warmup phase *)
    printf "  Warmup: %d iterations..." config.warmup_iterations;
    flush_all ();
    for i = 1 to config.warmup_iterations do
      ignore (operation ())
    done;
    printf " ✓\n";
    
    (* Optional GC *)
    if config.gc_between_runs then (
      Gc.major ();
      printf "  GC major collection complete\n"
    );
    
    (* Measurement phase *)
    printf "  Measuring: %d iterations..." config.measurement_iterations;
    flush_all ();
    
    let times = ref [] in
    for i = 1 to config.measurement_iterations do
      let (_, elapsed) = time_operation operation in
      times := elapsed :: !times
    done;
    
    let times_list = List.rev !times in
    let (total, average, min_time, max_time, std_dev) = calculate_stats times_list in
    
    printf " ✓\n";
    
    {
      operation = operation_name;
      iterations = config.measurement_iterations;
      total_time_ms = total;
      average_time_ms = average;
      min_time_ms = min_time;
      max_time_ms = max_time;
      std_dev_ms = std_dev;
    }
  
  let print_result result =
    printf "\n📊 Benchmark Results: %s\n" result.operation;
    printf "  Iterations: %d\n" result.iterations;
    printf "  Average: %.6f ms\n" result.average_time_ms;
    printf "  Min: %.6f ms\n" result.min_time_ms;
    printf "  Max: %.6f ms\n" result.max_time_ms;
    printf "  Std Dev: %.6f ms\n" result.std_dev_ms;
    printf "  Total: %.3f ms\n" result.total_time_ms;
    printf "\n"
end

(* ========== D2: LaTeX Processing Micro-benchmarks ========== *)
module LaTeXBenchmarks = struct
  
  (* Mock L0 lexing operation *)
  let bench_l0_token_extraction () =
    let text = "\\documentclass{article}\\begin{document}Hello \\textbf{world}\\end{document}" in
    let tokens = Array.make 20 "" in
    let count = ref 0 in
    for i = 0 to String.length text - 1 do
      if text.[i] = '\\' then incr count
    done;
    tokens.(!count mod 20) <- "\\token";
    !count
  
  (* Mock L1 macro expansion *)
  let bench_l1_macro_expansion () =
    let macros = [("\\alpha", "α"); ("\\beta", "β"); ("\\gamma", "γ")] in
    let token = "\\alpha" in
    let result = ref token in
    List.iter (fun (macro, expansion) ->
      if macro = token then result := expansion
    ) macros;
    String.length !result
  
  (* Mock SoA token insertion *)
  let bench_soa_insertion () =
    let capacity = 1000 in
    let token_types = Array.make capacity 0 in
    let positions = Array.make capacity 0 in
    let count = ref 0 in
    
    for i = 0 to 50 do
      if !count < capacity then (
        token_types.(!count) <- i mod 5;
        positions.(!count) <- i * 10;
        incr count
      )
    done;
    !count
  
  (* Mock validation check *)
  let bench_validation_check () =
    let issues = ref 0 in
    let tokens = [|"\\begin{document}"; "text"; "\\end{document}"|] in
    let stack = ref 0 in
    
    Array.iter (fun token ->
      if String.contains token 'b' && String.contains token 'e' then (
        if String.contains token '{' then incr stack
        else if String.contains token '}' then (
          decr stack;
          if !stack < 0 then incr issues
        )
      )
    ) tokens;
    !issues
  
  (* Mock JSON generation *)
  let bench_json_generation () =
    let buffer = Buffer.create 1024 in
    Buffer.add_string buffer "{\"file\":\"test.tex\",";
    Buffer.add_string buffer "\"tokens\":1234,";
    Buffer.add_string buffer "\"issues\":5,";
    Buffer.add_string buffer "\"processing_time_ms\":12.345}";
    Buffer.length buffer
  
  let run_all_benchmarks config =
    printf "🔬 D2: LaTeX Processing Micro-benchmark Suite\n";
    printf "============================================\n\n";
    
    let l0_result = MicroBenchmark.run_benchmark config "L0 Token Extraction" bench_l0_token_extraction in
    MicroBenchmark.print_result l0_result;
    
    let l1_result = MicroBenchmark.run_benchmark config "L1 Macro Expansion" bench_l1_macro_expansion in
    MicroBenchmark.print_result l1_result;
    
    let soa_result = MicroBenchmark.run_benchmark config "SoA Token Insertion" bench_soa_insertion in
    MicroBenchmark.print_result soa_result;
    
    let validation_result = MicroBenchmark.run_benchmark config "Validation Check" bench_validation_check in
    MicroBenchmark.print_result validation_result;
    
    let json_result = MicroBenchmark.run_benchmark config "JSON Generation" bench_json_generation in
    MicroBenchmark.print_result json_result;
    
    printf "📈 D2 Profiling Summary:\n";
    printf "  L0 Lexing: %.6f ms/op\n" l0_result.average_time_ms;
    printf "  L1 Expansion: %.6f ms/op\n" l1_result.average_time_ms;
    printf "  SoA Insertion: %.6f ms/op\n" soa_result.average_time_ms;
    printf "  Validation: %.6f ms/op\n" validation_result.average_time_ms;
    printf "  JSON Generation: %.6f ms/op\n" json_result.average_time_ms;
    printf "\n🎯 D2: Micro-benchmark profiling complete!\n"
end

(* ========== D2: Performance Analysis Tools ========== *)
module PerformanceAnalysis = struct
  let analyze_hotspots results =
    printf "🔥 Performance Hotspot Analysis (D2):\n";
    printf "=====================================\n";
    
    let sorted_results = List.sort (fun a b -> 
      compare b.MicroBenchmark.average_time_ms a.MicroBenchmark.average_time_ms) results in
    
    List.iteri (fun i result ->
      let percentage = if i = 0 then 100.0 else
        (result.MicroBenchmark.average_time_ms /. 
         (List.hd sorted_results).MicroBenchmark.average_time_ms) *. 100.0 in
      printf "%d. %s: %.6f ms (%.1f%% of slowest)\n" 
        (i+1) result.MicroBenchmark.operation result.MicroBenchmark.average_time_ms percentage
    ) sorted_results;
    
    printf "\n💡 Optimization Recommendations:\n";
    match sorted_results with
    | slowest :: _ ->
        printf "  • Primary target: %s (%.6f ms)\n" slowest.operation slowest.average_time_ms;
        if slowest.std_dev_ms > slowest.average_time_ms *. 0.1 then
          printf "  • High variance detected (%.6f ms std dev) - investigate inconsistency\n" slowest.std_dev_ms;
        if slowest.average_time_ms > 0.1 then
          printf "  • Consider optimization: operation exceeds 0.1ms threshold\n"
    | [] -> printf "  • No results to analyze\n"
  
  let export_csv_report results filename =
    let oc = open_out filename in
    fprintf oc "Operation,Iterations,Average_ms,Min_ms,Max_ms,StdDev_ms,Total_ms\n";
    List.iter (fun result ->
      fprintf oc "%s,%d,%.6f,%.6f,%.6f,%.6f,%.3f\n"
        result.MicroBenchmark.operation
        result.MicroBenchmark.iterations
        result.MicroBenchmark.average_time_ms
        result.MicroBenchmark.min_time_ms
        result.MicroBenchmark.max_time_ms
        result.MicroBenchmark.std_dev_ms
        result.MicroBenchmark.total_time_ms
    ) results;
    close_out oc;
    printf "📄 D2: Exported results to %s\n" filename
end

let () =
  match Sys.argv with
  | [| _; "--profile-d2" |] ->
      let config = MicroBenchmark.{ default_config with 
        measurement_iterations = 5000; detailed_output = true } in
      LaTeXBenchmarks.run_all_benchmarks config
  | [| _; "--profile-quick" |] ->
      let config = MicroBenchmark.{ default_config with 
        warmup_iterations = 50; measurement_iterations = 500 } in
      LaTeXBenchmarks.run_all_benchmarks config
  | [| _; "--export-csv"; filename |] ->
      printf "D2 CSV export feature - run benchmarks first\n"
  | _ -> 
      printf "Usage: %s --profile-d2 | --profile-quick | --export-csv filename\n" Sys.argv.(0);
      printf "D2: Micro-benchmark profiling for LaTeX processing components\n"