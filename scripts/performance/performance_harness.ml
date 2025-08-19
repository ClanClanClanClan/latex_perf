(* Performance Measurement Harness - LaTeX Perfectionist v25 *)
(* Automated benchmarking and performance tracking system *)

open Unix
open Printf

(* Benchmark configuration *)
type benchmark_config = {
  name: string;
  iterations: int;
  warmup_iterations: int;
  timeout_ms: int;
  min_runtime_ms: float;  (* Minimum time to run for statistical significance *)
  max_runtime_ms: float;  (* Maximum time before stopping *)
  target_percentiles: float list;  (* Which percentiles to report *)
}

(* Performance measurement *)
type measurement = {
  iteration: int;
  runtime_ms: float;
  memory_mb: float option;
  gc_stats: Gc.stat option;
}

type statistics = {
  mean_ms: float;
  median_ms: float;
  std_dev_ms: float;
  min_ms: float;
  max_ms: float;
  percentiles: (float * float) list;  (* percentile, value *)
}

(* Benchmark result *)
type benchmark_result = {
  config: benchmark_config;
  measurements: measurement array;
  statistics: statistics;
  total_runtime_s: float;
  throughput_per_second: float;
}

(* Default configuration *)
let default_config name = {
  name;
  iterations = 100;
  warmup_iterations = 10;
  timeout_ms = 60000;  (* 1 minute *)
  min_runtime_ms = 1000.0;  (* 1 second minimum *)
  max_runtime_ms = 30000.0;  (* 30 seconds maximum *)
  target_percentiles = [50.0; 90.0; 95.0; 99.0];
}

(* Run single measurement *)
let measure_once ?(measure_memory=false) ?(measure_gc=false) fn =
  let start_gc = if measure_gc then Some (Gc.stat ()) else None in
  let start_memory = if measure_memory then 
    Some ((Gc.stat ()).heap_words * (Sys.word_size / 8) / 1024 / 1024) 
  else None in
  
  let start_time = Unix.gettimeofday () in
  let result = fn () in
  let end_time = Unix.gettimeofday () in
  
  let runtime_ms = (end_time -. start_time) *. 1000. in
  let memory_mb = match start_memory with
    | Some start_mb -> 
        let end_mb = (Gc.stat ()).heap_words * (Sys.word_size / 8) / 1024 / 1024 in
        Some (float_of_int (max 0 (end_mb - start_mb)))
    | None -> None
  in
  let gc_stats = if measure_gc then Some (Gc.stat ()) else None in
  
  (result, { iteration = 0; runtime_ms; memory_mb; gc_stats })

(* Calculate percentile *)
let percentile arr p =
  let sorted = Array.copy arr in
  Array.sort compare sorted;
  let len = Array.length sorted in
  if len = 0 then 0.0
  else if len = 1 then sorted.(0)
  else
    let rank = p /. 100.0 *. float_of_int (len - 1) in
    let lower = int_of_float (floor rank) in
    let upper = int_of_float (ceil rank) in
    if lower = upper then sorted.(lower)
    else
      let weight = rank -. float_of_int lower in
      sorted.(lower) *. (1.0 -. weight) +. sorted.(upper) *. weight

(* Calculate statistics *)
let calculate_statistics measurements config =
  let runtimes = Array.map (fun m -> m.runtime_ms) measurements in
  let len = Array.length runtimes in
  
  if len = 0 then
    {
      mean_ms = 0.0;
      median_ms = 0.0;
      std_dev_ms = 0.0;
      min_ms = 0.0;
      max_ms = 0.0;
      percentiles = [];
    }
  else
    let mean = (Array.fold_left (+.) 0.0 runtimes) /. float_of_int len in
    let variance = Array.fold_left (fun acc x -> 
      acc +. (x -. mean) *. (x -. mean)) 0.0 runtimes /. float_of_int len in
    let std_dev = sqrt variance in
    
    let min_val = Array.fold_left min runtimes.(0) runtimes in
    let max_val = Array.fold_left max runtimes.(0) runtimes in
    let median = percentile runtimes 50.0 in
    
    let percentiles = List.map (fun p -> (p, percentile runtimes p)) config.target_percentiles in
    
    {
      mean_ms = mean;
      median_ms = median;
      std_dev_ms = std_dev;
      min_ms = min_val;
      max_ms = max_val;
      percentiles;
    }

(* Run benchmark *)
let benchmark ?(config=default_config "unnamed") fn =
  printf "Running benchmark: %s\n" config.name;
  printf "  Iterations: %d (+ %d warmup)\n" config.iterations config.warmup_iterations;
  printf "  Timeout: %dms\n" config.timeout_ms;
  printf "\n";
  
  (* Warmup phase *)
  printf "Warmup phase...\n";
  for i = 1 to config.warmup_iterations do
    let (_result, _measurement) = measure_once fn in
    if i mod 5 = 0 then printf "  Warmup %d/%d\n" i config.warmup_iterations
  done;
  
  printf "Measurement phase...\n";
  let measurements = Array.make config.iterations {
    iteration = 0;
    runtime_ms = 0.0;
    memory_mb = None;
    gc_stats = None;
  } in
  
  let start_benchmark = Unix.gettimeofday () in
  let completed = ref 0 in
  let total_time = ref 0.0 in
  
  for i = 0 to config.iterations - 1 do
    if !total_time *. 1000. < float_of_int config.timeout_ms then (
      let (_result, measurement) = measure_once ~measure_memory:true ~measure_gc:true fn in
      measurements.(i) <- { measurement with iteration = i + 1 };
      total_time := Unix.gettimeofday () -. start_benchmark;
      completed := i + 1;
      
      (* Progress reporting *)
      if (i + 1) mod 10 = 0 then
        printf "  Progress %d/%d (%.1fs)\n" (i + 1) config.iterations !total_time;
      
      (* Early termination checks *)
      if !total_time *. 1000. >= config.max_runtime_ms then (
        printf "  Early termination: max runtime reached\n";
        raise Exit
      )
    )
  done;
  
  let end_benchmark = Unix.gettimeofday () in
  let total_runtime_s = end_benchmark -. start_benchmark in
  
  printf "Completed %d/%d iterations in %.2fs\n" !completed config.iterations total_runtime_s;
  
  (* Trim array to completed measurements *)
  let final_measurements = Array.sub measurements 0 !completed in
  let statistics = calculate_statistics final_measurements config in
  
  let throughput = float_of_int !completed /. total_runtime_s in
  
  {
    config;
    measurements = final_measurements;
    statistics;
    total_runtime_s;
    throughput_per_second = throughput;
  }

(* Pretty print results *)
let pp_result result =
  printf "\n=== Benchmark Results: %s ===\n" result.config.name;
  printf "Completed: %d iterations in %.2fs\n" 
    (Array.length result.measurements) result.total_runtime_s;
  printf "Throughput: %.1f ops/second\n" result.throughput_per_second;
  printf "\nLatency Statistics:\n";
  printf "  Mean:     %.3f ms\n" result.statistics.mean_ms;
  printf "  Median:   %.3f ms\n" result.statistics.median_ms;
  printf "  Std Dev:  %.3f ms\n" result.statistics.std_dev_ms;
  printf "  Min:      %.3f ms\n" result.statistics.min_ms;
  printf "  Max:      %.3f ms\n" result.statistics.max_ms;
  printf "\nPercentiles:\n";
  List.iter (fun (p, v) ->
    printf "  P%.0f:      %.3f ms\n" p v
  ) result.statistics.percentiles;
  
  (* Memory statistics if available *)
  let memory_measurements = Array.to_list result.measurements |> 
    List.filter_map (fun m -> m.memory_mb) in
  if List.length memory_measurements > 0 then (
    let total_memory = List.fold_left (+.) 0.0 memory_measurements in
    let avg_memory = total_memory /. float_of_int (List.length memory_measurements) in
    printf "\nMemory Usage:\n";
    printf "  Average:  %.2f MB per operation\n" avg_memory
  );
  
  printf "\n"

(* Export results to CSV *)
let export_csv result filename =
  let oc = open_out filename in
  fprintf oc "iteration,runtime_ms,memory_mb\n";
  Array.iter (fun m ->
    let memory_str = match m.memory_mb with
      | Some mb -> sprintf "%.3f" mb
      | None -> ""
    in
    fprintf oc "%d,%.6f,%s\n" m.iteration m.runtime_ms memory_str
  ) result.measurements;
  close_out oc;
  printf "Exported %d measurements to %s\n" (Array.length result.measurements) filename

(* Compare two benchmark results *)
let compare_results baseline current =
  let baseline_median = baseline.statistics.median_ms in
  let current_median = current.statistics.median_ms in
  let improvement_pct = (baseline_median -. current_median) /. baseline_median *. 100. in
  
  printf "\n=== Performance Comparison ===\n";
  printf "Baseline (%s): %.3f ms median\n" baseline.config.name baseline_median;
  printf "Current (%s):  %.3f ms median\n" current.config.name current_median;
  if improvement_pct > 0. then
    printf "Improvement: %.1f%% faster 🚀\n" improvement_pct
  else
    printf "Regression:  %.1f%% slower ⚠️\n" (abs_float improvement_pct);
  printf "\n"

(* Benchmark suite *)
type 'a benchmark_suite = {
  name: string;
  benchmarks: (string * (unit -> 'a)) list;
  config_template: benchmark_config;
}

let run_suite suite =
  printf "\n🚀 Running Benchmark Suite: %s\n" suite.name;
  printf "%s\n\n" ("=" ^ String.make (String.length suite.name + 30) '=');
  
  let results = List.map (fun (name, fn) ->
    let config = { suite.config_template with name } in
    let result = benchmark ~config fn in
    pp_result result;
    (name, result)
  ) suite.benchmarks in
  
  printf "📊 Suite Summary:\n";
  List.iter (fun (name, result) ->
    printf "  %-20s: %.3f ms median, %.1f ops/s\n" 
      name result.statistics.median_ms result.throughput_per_second
  ) results;
  printf "\n";
  
  results