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
    gc_major_words: float;
    gc_minor_words: float;
  }
  
  type monitoring_config = {
    sample_interval_ms: int;
    retention_hours: int;
    alert_threshold_ms: float;
    memory_alert_mb: float;
    export_interval_minutes: int;
  }
  
  let production_config = {
    sample_interval_ms = 100;    (* Sample every 100ms *)
    retention_hours = 24;        (* Keep 24 hours of data *)
    alert_threshold_ms = 25.0;   (* Alert if operation > 25ms *)
    memory_alert_mb = 100.0;     (* Alert if memory > 100MB *)
    export_interval_minutes = 15; (* Export metrics every 15 minutes *)
  }
  
  let samples = ref []
  let alerts = ref []
  let monitoring_active = ref false
  
  let get_memory_usage () =
    let stat = Gc.stat () in
    let heap_words = stat.heap_words in
    float_of_int heap_words *. 8.0 /. (1024.0 *. 1024.0) (* Convert to MB *)
  
  let collect_sample operation duration_ms =
    let stat = Gc.stat () in
    let sample = {
      timestamp = Unix.gettimeofday ();
      operation = operation;
      duration_ms = duration_ms;
      memory_mb = get_memory_usage ();
      gc_major_words = stat.major_words;
      gc_minor_words = stat.minor_words;
    } in
    samples := sample :: !samples;
    
    (* Check alert thresholds *)
    if duration_ms > production_config.alert_threshold_ms then (
      let alert_msg = sprintf "PERFORMANCE ALERT: %s took %.2fms (threshold: %.2fms)" 
        operation duration_ms production_config.alert_threshold_ms in
      alerts := (Unix.gettimeofday (), alert_msg) :: !alerts;
      printf "⚠️ %s\n" alert_msg
    );
    
    if sample.memory_mb > production_config.memory_alert_mb then (
      let alert_msg = sprintf "MEMORY ALERT: %.2fMB used (threshold: %.2fMB)" 
        sample.memory_mb production_config.memory_alert_mb in
      alerts := (Unix.gettimeofday (), alert_msg) :: !alerts;
      printf "⚠️ %s\n" alert_msg
    )
  
  let start_monitoring () =
    monitoring_active := true;
    printf "📊 D3: Performance monitoring started\n";
    printf "  Sample interval: %dms\n" production_config.sample_interval_ms;
    printf "  Alert threshold: %.2fms\n" production_config.alert_threshold_ms;
    printf "  Memory threshold: %.2fMB\n" production_config.memory_alert_mb;
    printf "\n"
  
  let stop_monitoring () =
    monitoring_active := false;
    printf "📊 D3: Performance monitoring stopped\n"
  
  let get_statistics_window hours =
    let cutoff_time = Unix.gettimeofday () -. (float_of_int hours *. 3600.0) in
    let recent_samples = List.filter (fun s -> s.timestamp >= cutoff_time) !samples in
    
    if recent_samples = [] then None
    else
      let count = List.length recent_samples in
      let total_duration = List.fold_left (fun acc s -> acc +. s.duration_ms) 0.0 recent_samples in
      let avg_duration = total_duration /. float_of_int count in
      
      let durations = List.map (fun s -> s.duration_ms) recent_samples in
      let sorted_durations = List.sort compare durations in
      let p95_index = int_of_float (0.95 *. float_of_int count) in
      let p99_index = int_of_float (0.99 *. float_of_int count) in
      let p95 = List.nth sorted_durations (min p95_index (count - 1)) in
      let p99 = List.nth sorted_durations (min p99_index (count - 1)) in
      
      let max_memory = List.fold_left (fun acc s -> max acc s.memory_mb) 0.0 recent_samples in
      let avg_memory = (List.fold_left (fun acc s -> acc +. s.memory_mb) 0.0 recent_samples) /. float_of_int count in
      
      Some (count, avg_duration, p95, p99, avg_memory, max_memory)
  
  let print_status () =
    printf "📊 D3: Performance Monitor Status\n";
    printf "=================================\n";
    printf "Monitoring active: %b\n" !monitoring_active;
    printf "Total samples: %d\n" (List.length !samples);
    printf "Total alerts: %d\n" (List.length !alerts);
    
    match get_statistics_window 1 with
    | Some (count, avg, p95, p99, avg_mem, max_mem) ->
        printf "\nLast 1 hour statistics:\n";
        printf "  Samples: %d\n" count;
        printf "  Average duration: %.3f ms\n" avg;
        printf "  P95 duration: %.3f ms\n" p95;
        printf "  P99 duration: %.3f ms\n" p99;
        printf "  Average memory: %.2f MB\n" avg_mem;
        printf "  Peak memory: %.2f MB\n" max_mem
    | None ->
        printf "\nNo samples in last hour\n";
    
    printf "\nRecent alerts:\n";
    let recent_alerts = List.take (min 5 (List.length !alerts)) !alerts in
    List.iter (fun (timestamp, msg) ->
      let time_str = Printf.sprintf "%.0f" timestamp in
      printf "  %s: %s\n" time_str msg
    ) recent_alerts;
    printf "\n"
  
  let export_metrics filename =
    let oc = open_out filename in
    fprintf oc "timestamp,operation,duration_ms,memory_mb,gc_major_words,gc_minor_words\n";
    List.iter (fun sample ->
      fprintf oc "%.3f,%s,%.6f,%.3f,%.0f,%.0f\n"
        sample.timestamp
        sample.operation
        sample.duration_ms
        sample.memory_mb
        sample.gc_major_words
        sample.gc_minor_words
    ) (List.rev !samples);
    close_out oc;
    printf "📄 D3: Exported %d samples to %s\n" (List.length !samples) filename
end

(* ========== D3: LaTeX Processing Monitor Integration ========== *)
module LaTeXProcessingMonitor = struct
  let monitor_operation operation_name f =
    let start_time = Unix.gettimeofday () in
    let result = f () in
    let duration_ms = (Unix.gettimeofday () -. start_time) *. 1000.0 in
    
    if !PerformanceMonitor.monitoring_active then
      PerformanceMonitor.collect_sample operation_name duration_ms;
    
    (result, duration_ms)
  
  let monitor_file_processing file_path =
    printf "📊 D3: Monitoring processing of %s\n" (Filename.basename file_path);
    
    let (l0_result, l0_time) = monitor_operation "L0_Lexing" (fun () ->
      (* Mock L0 lexing *)
      Thread.delay 0.008; (* Simulate 8ms L0 processing *)
      "L0_tokens_extracted"
    ) in
    
    let (l1_result, l1_time) = monitor_operation "L1_Expansion" (fun () ->
      (* Mock L1 expansion *)
      Thread.delay 0.003; (* Simulate 3ms L1 processing *)
      "L1_macros_expanded"
    ) in
    
    let (validation_result, validation_time) = monitor_operation "Validation" (fun () ->
      (* Mock validation *)
      Thread.delay 0.002; (* Simulate 2ms validation *)
      "Validation_complete"
    ) in
    
    let (json_result, json_time) = monitor_operation "JSON_Generation" (fun () ->
      (* Mock JSON generation *)
      Thread.delay 0.001; (* Simulate 1ms JSON generation *)
      sprintf "{\"file\":\"%s\",\"total_time_ms\":%.3f}" file_path (l0_time +. l1_time +. validation_time)
    ) in
    
    let total_time = l0_time +. l1_time +. validation_time +. json_time in
    
    printf "  L0 Lexing: %.3f ms\n" l0_time;
    printf "  L1 Expansion: %.3f ms\n" l1_time;
    printf "  Validation: %.3f ms\n" validation_time;
    printf "  JSON Generation: %.3f ms\n" json_time;
    printf "  Total: %.3f ms\n" total_time;
    
    json_result
  
  let simulate_production_load duration_seconds =
    printf "🏭 D3: Simulating production load for %d seconds\n" duration_seconds;
    PerformanceMonitor.start_monitoring ();
    
    let start_time = Unix.gettimeofday () in
    let end_time = start_time +. float_of_int duration_seconds in
    let request_count = ref 0 in
    
    while Unix.gettimeofday () < end_time do
      incr request_count;
      let file_name = sprintf "document_%d.tex" !request_count in
      ignore (monitor_file_processing file_name);
      
      (* Variable request intervals (50-200ms) *)
      let interval = 0.05 +. Random.float 0.15 in
      Thread.delay interval;
      
      (* Occasional spike simulation *)
      if !request_count mod 20 = 0 then (
        let (spike_result, spike_time) = monitor_operation "Processing_Spike" (fun () ->
          Thread.delay 0.030; (* Simulate 30ms spike *)
          "spike_processed"
        ) in
        printf "  ⚡ Simulated processing spike: %.3f ms\n" spike_time
      )
    done;
    
    printf "🏭 D3: Production simulation complete - %d requests processed\n" !request_count;
    PerformanceMonitor.print_status ()
end

(* ========== D3: Alert System ========== *)
module AlertSystem = struct
  type alert_level = Info | Warning | Critical
  
  let send_alert level message =
    let level_str = match level with
      | Info -> "INFO"
      | Warning -> "WARNING" 
      | Critical -> "CRITICAL" in
    
    let timestamp = Unix.gettimeofday () in
    printf "🚨 D3 ALERT [%s] %.0f: %s\n" level_str timestamp message;
    
    (* In production, this would integrate with:
       - PagerDuty/OpsGenie for critical alerts
       - Slack/Teams for warnings  
       - Log aggregation systems
       - Metrics dashboards (Grafana, etc.) *)
  
  let check_system_health () =
    let memory_usage = PerformanceMonitor.get_memory_usage () in
    
    if memory_usage > 200.0 then
      send_alert Critical (sprintf "Memory usage critical: %.2f MB" memory_usage)
    else if memory_usage > 150.0 then
      send_alert Warning (sprintf "Memory usage elevated: %.2f MB" memory_usage);
    
    match PerformanceMonitor.get_statistics_window 1 with
    | Some (count, avg, p95, p99, _, _) ->
        if p99 > 50.0 then
          send_alert Critical (sprintf "P99 latency critical: %.2f ms" p99)
        else if p99 > 30.0 then
          send_alert Warning (sprintf "P99 latency elevated: %.2f ms" p99);
        
        if count < 10 then
          send_alert Info "Low request volume detected"
    | None ->
        send_alert Warning "No performance data available"
end

let () =
  Random.self_init ();
  match Sys.argv with
  | [| _; "--monitor-d3" |] ->
      PerformanceMonitor.start_monitoring ();
      printf "D3 monitoring active. Use Ctrl+C to stop.\n";
      (try
        while true do
          Thread.delay 1.0;
          if Random.float 1.0 < 0.1 then (* 10% chance each second *)
            AlertSystem.check_system_health ()
        done
      with _ -> PerformanceMonitor.stop_monitoring ())
  | [| _; "--simulate"; duration |] ->
      let duration_sec = int_of_string duration in
      LaTeXProcessingMonitor.simulate_production_load duration_sec
  | [| _; "--status-d3" |] ->
      PerformanceMonitor.print_status ()
  | [| _; "--export"; filename |] ->
      PerformanceMonitor.export_metrics filename
  | [| _; "--test-alerts" |] ->
      AlertSystem.send_alert Info "Test info alert";
      AlertSystem.send_alert Warning "Test warning alert";
      AlertSystem.send_alert Critical "Test critical alert"
  | _ -> 
      printf "Usage: %s --monitor-d3 | --simulate seconds | --status-d3 | --export filename | --test-alerts\n" Sys.argv.(0);
      printf "D3: Production performance monitoring and alerting system\n"