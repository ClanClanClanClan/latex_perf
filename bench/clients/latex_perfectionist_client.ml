(* LaTeX Perfectionist Client - Fast wrapper for resident worker *)

open Printf
open Unix

let sock_path = 
  let temp_dir = try Sys.getenv "TMPDIR" with Not_found -> "/tmp" in
  Filename.concat temp_dir "latex_perfectionist_v25.sock"

let write_length_prefixed_string oc str =
  let len = String.length str in
  output_binary_int oc len;
  output_string oc str;
  flush oc

let read_length_prefixed_string ic =
  let len = input_binary_int ic in
  if len < 0 || len > 64 * 1024 * 1024 then (* 64MB limit for responses *)
    failwith "Response too large"
  else
    really_input_string ic len

let is_server_running () =
  try
    let sock = Unix.socket Unix.PF_UNIX Unix.SOCK_STREAM 0 in
    Unix.connect sock (Unix.ADDR_UNIX sock_path);
    Unix.close sock;
    true
  with
  | Unix.Unix_error _ -> false

let start_worker_if_needed () =
  if not (is_server_running ()) then (
    printf "Starting worker server...\n";
    flush_all ();
    
    (* Compile and start worker *)
    let compile_cmd = "OPAMSWITCH=l0-testing opam exec -- ocamlopt -I +unix -o latex_perfectionist_worker unix.cmxa latex_perfectionist_worker.ml 2>/dev/null" in
    let compile_result = Sys.command compile_cmd in
    
    if compile_result = 0 then (
      (* Start worker in background *)
      let start_cmd = "./latex_perfectionist_worker --serve &" in
      ignore (Sys.command start_cmd);
      
      (* Wait for server to be ready *)
      let rec wait_for_server retries =
        if retries <= 0 then
          failwith "Worker server failed to start"
        else if is_server_running () then
          printf "Worker server ready!\n"
        else (
          Unix.sleepf 0.1;
          wait_for_server (retries - 1)
        )
      in
      wait_for_server 50  (* 5 second timeout *)
    ) else
      failwith "Failed to compile worker"
  )

let send_request_to_worker file_path =
  try
    let sock = Unix.socket Unix.PF_UNIX Unix.SOCK_STREAM 0 in
    Unix.connect sock (Unix.ADDR_UNIX sock_path);
    
    let oc = Unix.out_channel_of_descr sock in
    let ic = Unix.in_channel_of_descr sock in
    
    (* Send file path *)
    write_length_prefixed_string oc file_path;
    
    (* Read response *)
    let response = read_length_prefixed_string ic in
    
    Unix.close sock;
    response
  with
  | Unix.Unix_error (Unix.ENOENT, _, _) | Unix.Unix_error (Unix.ECONNREFUSED, _, _) ->
      (* Server not running, fallback to direct execution *)
      printf "Worker not available, using direct execution...\n";
      let temp_file = Filename.temp_file "lpv25" ".json" in
      let cmd = sprintf "./latex_perfectionist_cli_phase3_ultra --summary %s > %s 2>/dev/null"
                  (Filename.quote file_path) (Filename.quote temp_file) in
      let exit_code = Sys.command cmd in
      if exit_code = 0 then (
        let ic = open_in temp_file in
        let content = really_input_string ic (in_channel_length ic) in
        close_in ic;
        Sys.remove temp_file;
        content
      ) else (
        if Sys.file_exists temp_file then Sys.remove temp_file;
        sprintf "{\"error\": \"Processing failed\", \"file\": \"%s\"}" file_path
      )

let measure_request_latency file_path =
  let start_time = Unix.gettimeofday () in
  let response = send_request_to_worker file_path in
  let end_time = Unix.gettimeofday () in
  let elapsed_ms = (end_time -. start_time) *. 1000.0 in
  (response, elapsed_ms)

let show_help () =
  printf "LaTeX Perfectionist v25 (Fast Client)\n";
  printf "Usage:\n";
  printf "  %s [OPTIONS] <file.tex>\n" Sys.argv.(0);
  printf "\n";
  printf "Options:\n";
  printf "  --json      JSON output (default)\n";
  printf "  --summary   Summary with timing\n";
  printf "  --measure   Show client-side latency\n";
  printf "  --start     Start worker server\n";
  printf "  --stop      Stop worker server\n";
  printf "  --status    Check worker status\n";
  printf "  --help      Show this help\n"

let stop_worker () =
  try
    let pid_cmd = "pgrep -f 'latex_perfectionist_worker --serve'" in
    let ic = Unix.open_process_in pid_cmd in
    let pid_str = input_line ic in
    ignore (Unix.close_process_in ic);
    let pid = int_of_string (String.trim pid_str) in
    Unix.kill pid Sys.sigterm;
    printf "Worker server stopped (PID %d)\n" pid
  with
  | End_of_file -> printf "No worker server running\n"
  | _ -> printf "Failed to stop worker server\n"

let show_status () =
  if is_server_running () then
    printf "✅ Worker server is running\n"
  else
    printf "❌ Worker server is not running\n"

let () =
  let args = Array.to_list Sys.argv in
  match args with
  | [_; "--help"] -> show_help ()
  | [_; "--start"] -> 
      start_worker_if_needed ();
      printf "Worker server started\n"
  | [_; "--stop"] -> stop_worker ()
  | [_; "--status"] -> show_status ()
  | [_; file_path] | [_; "--json"; file_path] ->
      start_worker_if_needed ();
      let response = send_request_to_worker file_path in
      print_string response
  | [_; "--summary"; file_path] ->
      start_worker_if_needed ();
      let response = send_request_to_worker file_path in
      print_string response
  | [_; "--measure"; file_path] ->
      start_worker_if_needed ();
      let (response, elapsed_ms) = measure_request_latency file_path in
      printf "=== CLIENT-SIDE LATENCY ===\n";
      printf "File: %s\n" file_path;
      printf "Request latency: %.2f ms\n" elapsed_ms;
      printf "Response:\n%s\n" response
  | _ ->
      show_help ();
      exit 1