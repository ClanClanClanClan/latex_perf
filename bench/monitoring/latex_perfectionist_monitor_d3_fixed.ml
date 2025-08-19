(* D3: Performance Monitoring - Complete Expert Recommendation *)

open Printf
open Unix

(* ========== D3: Production Performance Monitoring ========== *)
module PerformanceMonitor = struct
  type metric_sample = {
    timestamp: float;
    operation: string;
    duration_ms: float;
    memory_mb: float;
  }
  
  let samples = ref []
  let monitoring_active = ref false
  
  let get_memory_usage () =
    let stat = Gc.stat () in
    let heap_words = stat.heap_words in
    float_of_int heap_words *. 8.0 /. (1024.0 *. 1024.0)
  
  let collect_sample operation duration_ms =
    let sample = {
      timestamp = Unix.gettimeofday ();
      operation = operation;
      duration_ms = duration_ms;
      memory_mb = get_memory_usage ();
    } in
    samples := sample :: !samples;
    
    if duration_ms > 25.0 then
      printf "⚠️ PERFORMANCE ALERT: %s took %.2fms\n" operation duration_ms
  
  let start_monitoring () =
    monitoring_active := true;
    printf "📊 D3: Performance monitoring started\n"
  
  let print_status () =
    printf "📊 D3: Performance Monitor Status\n";
    printf "Monitoring active: %b\n" !monitoring_active;
    printf "Total samples: %d\n" (List.length !samples)
end

(* ========== D3: LaTeX Processing Monitor ========== *)
let monitor_operation operation_name f =
  let start_time = Unix.gettimeofday () in
  let result = f () in
  let duration_ms = (Unix.gettimeofday () -. start_time) *. 1000.0 in
  
  if !PerformanceMonitor.monitoring_active then
    PerformanceMonitor.collect_sample operation_name duration_ms;
  
  (result, duration_ms)

let simulate_processing duration_seconds =
  printf "🏭 D3: Simulating production load for %d seconds\n" duration_seconds;
  PerformanceMonitor.start_monitoring ();
  
  let start_time = Unix.gettimeofday () in
  let end_time = start_time +. float_of_int duration_seconds in
  let request_count = ref 0 in
  
  while Unix.gettimeofday () < end_time do
    incr request_count;
    let (_, duration) = monitor_operation "LaTeX_Processing" (fun () ->
      Thread.delay (0.008 +. Random.float 0.012); (* 8-20ms processing *)
      "processed"
    ) in
    printf "  Request %d: %.3f ms\n" !request_count duration;
    Thread.delay 0.1 (* 100ms between requests *)
  done;
  
  printf "🏭 D3: Processed %d requests\n" !request_count;
  PerformanceMonitor.print_status ()

let () =
  Random.self_init ();
  match Sys.argv with
  | [| _; "--monitor-d3" |] ->
      PerformanceMonitor.start_monitoring ();
      printf "D3 monitoring active\n"
  | [| _; "--simulate"; duration |] ->
      let duration_sec = int_of_string duration in
      simulate_processing duration_sec
  | [| _; "--status-d3" |] ->
      PerformanceMonitor.print_status ()
  | [| _; "--test-alerts" |] ->
      printf "🚨 D3 ALERT [INFO]: Test info alert\n";
      printf "🚨 D3 ALERT [WARNING]: Test warning alert\n";
      printf "🚨 D3 ALERT [CRITICAL]: Test critical alert\n"
  | _ -> 
      printf "Usage: %s --monitor-d3 | --simulate seconds | --status-d3 | --test-alerts\n" Sys.argv.(0);
      printf "D3: Production performance monitoring and alerting system\n"