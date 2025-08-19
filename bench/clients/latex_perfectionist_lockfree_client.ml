(* Lock-free Client with D1 Detailed Metrics *)

open Printf
open Unix

let sock_path = 
  let temp_dir = try Sys.getenv "TMPDIR" with Not_found -> "/tmp" in
  Filename.concat temp_dir "latex_perfectionist_lockfree.sock"

let is_lockfree_server_running () =
  try
    let sock = Unix.socket Unix.PF_UNIX Unix.SOCK_STREAM 0 in
    Unix.connect sock (Unix.ADDR_UNIX sock_path);
    Unix.close sock;
    true
  with
  | Unix.Unix_error _ -> false

let start_lockfree_worker () =
  if not (is_lockfree_server_running ()) then (
    printf "Starting lock-free worker (C1+D1)...\n";
    flush_all ();
    
    let compile_cmd = "OPAMSWITCH=l0-testing opam exec -- ocamlopt -I +unix -o latex_perfectionist_lockfree_worker unix.cmxa latex_perfectionist_lockfree_worker.ml 2>/dev/null" in
    let compile_result = Sys.command compile_cmd in
    
    if compile_result = 0 then (
      let start_cmd = "./latex_perfectionist_lockfree_worker --serve-lockfree &" in
      ignore (Sys.command start_cmd);
      
      let rec wait_for_server retries =
        if retries <= 0 then
          failwith "Lock-free worker failed to start"
        else if is_lockfree_server_running () then
          printf "Lock-free worker ready!\n"
        else (
          Unix.sleepf 0.2;
          wait_for_server (retries - 1)
        )
      in
      wait_for_server 30
    ) else
      failwith "Failed to compile lock-free worker"
  )

let send_request_to_lockfree_worker file_path =
  try
    let sock = Unix.socket Unix.PF_UNIX Unix.SOCK_STREAM 0 in
    Unix.connect sock (Unix.ADDR_UNIX sock_path);
    
    let oc = Unix.out_channel_of_descr sock in
    let ic = Unix.in_channel_of_descr sock in
    
    let len = String.length file_path in
    output_binary_int oc len;
    output_string oc file_path;
    flush oc;
    
    let response_len = input_binary_int ic in
    let response = really_input_string ic response_len in
    
    Unix.close sock;
    response
  with
  | Unix.Unix_error (Unix.ENOENT, _, _) | Unix.Unix_error (Unix.ECONNREFUSED, _, _) ->
      printf "Lock-free worker not available\n";
      sprintf "{\"error\": \"Lock-free worker unavailable\", \"file\": \"%s\"}" file_path

let measure_detailed_lockfree_request file_path =
  let t_start = Unix.gettimeofday () in
  let file_size = (Unix.stat file_path).st_size in
  
  try
    let t1 = Unix.gettimeofday () in
    let sock = Unix.socket Unix.PF_UNIX Unix.SOCK_STREAM 0 in
    Unix.connect sock (Unix.ADDR_UNIX sock_path);
    let oc = Unix.out_channel_of_descr sock in
    let ic = Unix.in_channel_of_descr sock in
    let t2 = Unix.gettimeofday () in
    
    let len = String.length file_path in
    output_binary_int oc len;
    output_string oc file_path;
    flush oc;
    let t3 = Unix.gettimeofday () in
    
    let response_len = input_binary_int ic in
    let t4 = Unix.gettimeofday () in
    let response = really_input_string ic response_len in
    let t5 = Unix.gettimeofday () in
    
    Unix.close sock;
    let t6 = Unix.gettimeofday () in
    
    let connect_ms = (t2 -. t1) *. 1000.0 in
    let send_ms = (t3 -. t2) *. 1000.0 in
    let wait_ms = (t4 -. t3) *. 1000.0 in
    let read_ms = (t5 -. t4) *. 1000.0 in
    let close_ms = (t6 -. t5) *. 1000.0 in
    let total_ms = (t6 -. t_start) *. 1000.0 in
    
    (response, total_ms, connect_ms, send_ms, wait_ms, read_ms, close_ms, file_size)
    
  with
  | exn ->
      let total_ms = (Unix.gettimeofday () -. t_start) *. 1000.0 in
      let error_response = sprintf "{\"error\":\"%s\"}" (Printexc.to_string exn) in
      (error_response, total_ms, 0.0, 0.0, 0.0, 0.0, 0.0, file_size)

let show_help () =
  printf "LaTeX Perfectionist v25 (Lock-free C1+D1 Client)\n";
  printf "Usage:\n";
  printf "  %s [OPTIONS] <file.tex>\n" Sys.argv.(0);
  printf "\n";
  printf "Options:\n";
  printf "  --start-lockfree    Start lock-free worker\n";
  printf "  --stop-lockfree     Stop lock-free worker\n";
  printf "  --status-lockfree   Check lock-free worker status\n";
  printf "  --detailed          Show detailed D1 metrics\n";
  printf "  --help              Show this help\n";
  printf "\n";
  printf "C1+D1 Optimizations:\n";
  printf "  • Lock-free atomic SoA operations\n";
  printf "  • Detailed client-side metrics\n";
  printf "  • Phase-by-phase timing breakdown\n";
  printf "  • Honest performance measurement\n"

let stop_lockfree_worker () =
  try
    let pid_cmd = "pgrep -f 'latex_perfectionist_lockfree_worker --serve-lockfree'" in
    let ic = Unix.open_process_in pid_cmd in
    let pid_str = input_line ic in
    ignore (Unix.close_process_in ic);
    let pid = int_of_string (String.trim pid_str) in
    Unix.kill pid Sys.sigterm;
    printf "Lock-free worker stopped (PID %d)\n" pid
  with
  | End_of_file -> printf "No lock-free worker running\n"
  | _ -> printf "Failed to stop lock-free worker\n"

let show_lockfree_status () =
  if is_lockfree_server_running () then
    printf "✅ Lock-free worker server (C1+D1) is running\n"
  else
    printf "❌ Lock-free worker server (C1+D1) is not running\n"

let () =
  let args = Array.to_list Sys.argv in
  match args with
  | [_; "--help"] -> show_help ()
  | [_; "--start-lockfree"] -> 
      start_lockfree_worker ();
      printf "Lock-free worker started\n"
  | [_; "--stop-lockfree"] -> stop_lockfree_worker ()
  | [_; "--status-lockfree"] -> show_lockfree_status ()
  | [_; file_path] ->
      start_lockfree_worker ();
      let response = send_request_to_lockfree_worker file_path in
      print_string response
  | [_; "--detailed"; file_path] ->
      start_lockfree_worker ();
      let (response, total_ms, connect_ms, send_ms, wait_ms, read_ms, close_ms, file_size) = 
        measure_detailed_lockfree_request file_path in
      printf "=== LOCK-FREE DETAILED METRICS (C1+D1) ===\n";
      printf "File: %s (%d bytes)\n" file_path file_size;
      printf "\n--- Timing Breakdown ---\n";
      printf "Socket connect:    %.3f ms\n" connect_ms;
      printf "Request send:      %.3f ms\n" send_ms;
      printf "Processing wait:   %.3f ms\n" wait_ms;
      printf "Response read:     %.3f ms\n" read_ms;
      printf "Socket close:      %.3f ms\n" close_ms;
      printf "TOTAL CLIENT:      %.3f ms\n" total_ms;
      printf "\n--- Performance Analysis ---\n";
      let overhead = total_ms -. wait_ms in
      printf "Processing time:   %.3f ms\n" wait_ms;
      printf "Client overhead:   %.3f ms\n" overhead;
      printf "Overhead ratio:    %.1f%%\n" (overhead /. total_ms *. 100.0);
      printf "Response:\n%s\n" response
  | _ ->
      show_help ();
      exit 1