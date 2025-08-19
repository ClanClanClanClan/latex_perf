(* Production Monitoring System - Phase 3 *)
(* Observability for L0+L1+12Validators pipeline *)

open Unix
open Printf

(* ========== Monitoring Metrics ========== *)
type metric_sample = {
  timestamp: float;
  latency_ms: float;
  l0_tokens: int;
  l1_expansions: int;
  validation_issues: int;
  file_size: int;
  memory_mb: float;
  gc_collections: int;
}

type performance_stats = {
  mutable total_requests: int;
  mutable total_latency_ms: float;
  mutable min_latency_ms: float;
  mutable max_latency_ms: float;
  mutable p50_latency_ms: float;
  mutable p95_latency_ms: float;
  mutable p99_latency_ms: float;
  recent_samples: metric_sample Queue.t;
  mutable last_reset: float;
}

let create_stats () = {
  total_requests = 0;
  total_latency_ms = 0.0;
  min_latency_ms = Float.max_float;
  max_latency_ms = 0.0;
  p50_latency_ms = 0.0;
  p95_latency_ms = 0.0;
  p99_latency_ms = 0.0;
  recent_samples = Queue.create ();
  last_reset = Unix.gettimeofday ();
}

let global_stats = create_stats ()

(* ========== Metric Collection ========== *)
let collect_gc_stats () =
  let gc_stats = Gc.stat () in
  gc_stats.major_collections + gc_stats.minor_collections

let collect_memory_usage () =
  let gc_stats = Gc.stat () in
  let heap_words = gc_stats.heap_words in
  let word_size = Sys.word_size / 8 in
  float_of_int (heap_words * word_size) /. (1024.0 *. 1024.0)

let rec add_sample stats sample =
  (* Keep last 1000 samples for percentile calculation *)
  Queue.push sample stats.recent_samples;
  if Queue.length stats.recent_samples > 1000 then
    ignore (Queue.pop stats.recent_samples);
  
  (* Update aggregate stats *)
  stats.total_requests <- stats.total_requests + 1;
  stats.total_latency_ms <- stats.total_latency_ms +. sample.latency_ms;
  stats.min_latency_ms <- min stats.min_latency_ms sample.latency_ms;
  stats.max_latency_ms <- max stats.max_latency_ms sample.latency_ms;
  
  (* Update percentiles every 10 samples *)
  if stats.total_requests mod 10 = 0 then
    calculate_percentiles stats

and calculate_percentiles stats =
  let samples = Queue.fold (fun acc sample -> sample.latency_ms :: acc) [] stats.recent_samples in
  let sorted_samples = List.sort compare samples in
  let len = List.length sorted_samples in
  
  if len > 0 then (
    let get_percentile p =
      let index = max 0 (min (len - 1) (int_of_float (float_of_int len *. p /. 100.0))) in
      List.nth sorted_samples index
    in
    stats.p50_latency_ms <- get_percentile 50.0;
    stats.p95_latency_ms <- get_percentile 95.0;
    stats.p99_latency_ms <- get_percentile 99.0
  )

(* ========== Monitoring Protocol ========== *)
let write_length_prefixed oc data =
  let len = String.length data in
  output_binary_int oc len;
  output_string oc data;
  flush oc

let read_length_prefixed ic =
  let len = input_binary_int ic in
  if len < 0 || len > 10_000_000 then
    failwith "Invalid message length";
  really_input_string ic len

let forward_request file_path =
  let worker_sock = socket PF_UNIX SOCK_STREAM 0 in
  let worker_path = "/tmp/latex_perfectionist_complete.sock" in
  
  try
    connect worker_sock (ADDR_UNIX worker_path);
    let ic = in_channel_of_descr worker_sock in
    let oc = out_channel_of_descr worker_sock in
    
    (* Measure end-to-end latency *)
    let t0 = Unix.gettimeofday () in
    write_length_prefixed oc file_path;
    let response = read_length_prefixed ic in
    let t1 = Unix.gettimeofday () in
    
    close worker_sock;
    
    let latency_ms = (t1 -. t0) *. 1000.0 in
    (response, latency_ms)
  with exn ->
    close worker_sock;
    let error_response = sprintf "{\"error\":\"Worker failed: %s\",\"file\":\"%s\"}" 
      (Printexc.to_string exn) file_path in
    (error_response, -1.0)

(* ========== JSON Parsing (Simple) ========== *)
let extract_json_field json field =
  try
    let pattern = sprintf "\"%s\":" field in
    let rec find_pattern str pattern pos =
      if pos + String.length pattern > String.length str then raise Not_found
      else if String.sub str pos (String.length pattern) = pattern then pos
      else find_pattern str pattern (pos + 1)
    in
    let pattern_pos = find_pattern json pattern 0 in
    let start_pos = pattern_pos + String.length pattern in
    let rec find_end pos depth in_string =
      if pos >= String.length json then pos
      else match json.[pos] with
        | '"' when not in_string -> find_end (pos + 1) depth true
        | '"' when in_string -> find_end (pos + 1) depth false
        | '{' when not in_string -> find_end (pos + 1) (depth + 1) in_string
        | '}' when not in_string && depth > 0 -> find_end (pos + 1) (depth - 1) in_string
        | '}' when not in_string && depth = 0 -> pos
        | ',' when not in_string && depth = 0 -> pos
        | _ -> find_end (pos + 1) depth in_string
    in
    let end_pos = find_end start_pos 0 false in
    let value_str = String.sub json start_pos (end_pos - start_pos) in
    Some (String.trim value_str)
  with _ -> None

let parse_worker_response response =
  try
    let l0_tokens = match extract_json_field response "l0_tokens" with
      | Some s -> int_of_string s | None -> 0 in
    let l1_expansions = match extract_json_field response "l1_expansions" with
      | Some s -> int_of_string s | None -> 0 in
    let validation_issues = match extract_json_field response "validation_issues" with
      | Some s -> int_of_string s | None -> 0 in
    let file_size = match extract_json_field response "file_size" with
      | Some s -> int_of_string s | None -> 0 in
    Some (l0_tokens, l1_expansions, validation_issues, file_size)
  with _ -> None

(* ========== Request Handler with Monitoring ========== *)
let handle_monitored_request payload =
  let file_path = String.trim payload in
  
  (* Collect pre-request metrics *)
  let gc_before = collect_gc_stats () in
  let memory_before = collect_memory_usage () in
  
  (* Forward to worker *)
  let (response, latency_ms) = forward_request file_path in
  
  (* Collect post-request metrics *)
  let gc_after = collect_gc_stats () in
  let memory_after = collect_memory_usage () in
  
  (* Parse worker response *)
  if latency_ms > 0.0 then (
    match parse_worker_response response with
    | Some (l0_tokens, l1_expansions, validation_issues, file_size) ->
        let sample = {
          timestamp = Unix.gettimeofday ();
          latency_ms = latency_ms;
          l0_tokens = l0_tokens;
          l1_expansions = l1_expansions;
          validation_issues = validation_issues;
          file_size = file_size;
          memory_mb = memory_after;
          gc_collections = gc_after - gc_before;
        } in
        add_sample global_stats sample;
        
        Printf.printf "Monitor: %s -> %.2fms [L0:%d L1:%d Issues:%d] GC:%d Mem:%.1fMB\n"
          (Filename.basename file_path) latency_ms l0_tokens l1_expansions 
          validation_issues sample.gc_collections memory_after;
        flush Stdlib.stdout
    | None ->
        Printf.printf "Monitor: %s -> %.2fms [parsing failed]\n"
          (Filename.basename file_path) latency_ms;
        flush Stdlib.stdout
  ) else (
    Printf.printf "Monitor: %s -> ERROR\n" (Filename.basename file_path);
    flush Stdlib.stdout
  );
  
  (* Add monitoring data to response *)
  let enhanced_response = 
    if String.contains response '{' && String.contains response '}' then
      let insert_pos = String.rindex response '}' in
      let before = String.sub response 0 insert_pos in
      sprintf "%s,\"monitor_latency_ms\":%.3f,\"monitor_memory_mb\":%.3f}" 
        before latency_ms memory_after
    else response
  in
  
  enhanced_response

(* ========== Statistics Reporting ========== *)
let generate_stats_report () =
  let stats = global_stats in
  let uptime_s = Unix.gettimeofday () -. stats.last_reset in
  let avg_latency = if stats.total_requests > 0 then 
    stats.total_latency_ms /. float_of_int stats.total_requests else 0.0 in
  let requests_per_sec = float_of_int stats.total_requests /. uptime_s in
  
  sprintf "{\"monitoring_stats\":{\"uptime_seconds\":%.1f,\"total_requests\":%d,\"requests_per_second\":%.2f,\"avg_latency_ms\":%.3f,\"min_latency_ms\":%.3f,\"max_latency_ms\":%.3f,\"p50_latency_ms\":%.3f,\"p95_latency_ms\":%.3f,\"p99_latency_ms\":%.3f,\"sample_count\":%d}}"
    uptime_s stats.total_requests requests_per_sec avg_latency 
    stats.min_latency_ms stats.max_latency_ms stats.p50_latency_ms 
    stats.p95_latency_ms stats.p99_latency_ms (Queue.length stats.recent_samples)

(* ========== Monitor Server ========== *)
let serve_monitor sock_path =
  (try Unix.unlink sock_path with _ -> ());
  
  let sock = socket PF_UNIX SOCK_STREAM 0 in
  bind sock (ADDR_UNIX sock_path);
  listen sock 32;
  
  Printf.printf "📊 PRODUCTION MONITORING ACTIVE\n";
  Printf.printf "===============================\n";
  Printf.printf "Monitor socket: %s\n" sock_path;
  Printf.printf "Worker socket: /tmp/latex_perfectionist_complete.sock\n";
  Printf.printf "Features: End-to-end latency, GC tracking, Memory monitoring\n";
  Printf.printf "Metrics: P50/P95/P99 percentiles, Request rate\n\n";
  flush Stdlib.stdout;
  
  Gc.full_major ();
  
  let rec loop () =
    try
      let (client_fd, _) = accept sock in
      let ic = in_channel_of_descr client_fd in
      let oc = out_channel_of_descr client_fd in
      
      let request = read_length_prefixed ic in
      
      let response = 
        if String.trim request = "--stats" then
          generate_stats_report ()
        else
          handle_monitored_request request
      in
      
      write_length_prefixed oc response;
      close client_fd;
      loop ()
    with
    | Unix_error (EINTR, _, _) -> loop ()
    | exn ->
        Printf.eprintf "Monitor error: %s\n" (Printexc.to_string exn);
        flush Stdlib.stderr;
        loop ()
  in
  loop ()

let () =
  let monitor_sock_path = 
    try Sys.getenv "LP_MONITOR_SOCKET"
    with Not_found -> "/tmp/latex_perfectionist_monitor.sock"
  in
  
  match Sys.argv with
  | [| _ |] | [| _; "--serve" |] -> 
      serve_monitor monitor_sock_path
  | [| _; "--stats" |] ->
      (* Quick stats query *)
      let sock = socket PF_UNIX SOCK_STREAM 0 in
      (try
        connect sock (ADDR_UNIX monitor_sock_path);
        let ic = in_channel_of_descr sock in
        let oc = out_channel_of_descr sock in
        write_length_prefixed oc "--stats";
        let response = read_length_prefixed ic in
        Printf.printf "%s\n" response;
        close sock
      with exn ->
        Printf.eprintf "Stats query failed: %s\n" (Printexc.to_string exn);
        close sock)
  | [| _; "--help" |] ->
      printf "Usage: %s [--serve|--stats]\n" Sys.argv.(0);
      printf "Production monitoring proxy for LaTeX Perfectionist\n";
      printf "Tracks latency, memory, GC, and provides P50/P95/P99 metrics\n"
  | _ ->
      Printf.eprintf "Unknown arguments\n";
      exit 1