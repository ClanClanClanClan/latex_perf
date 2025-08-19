(* Native Client for B5 Native Integration Worker *)

open Printf
open Unix

let sock_path = 
  let temp_dir = try Sys.getenv "TMPDIR" with Not_found -> "/tmp" in
  Filename.concat temp_dir "latex_perfectionist_native.sock"

let write_length_prefixed_string oc str =
  let len = String.length str in
  output_binary_int oc len;
  output_string oc str;
  flush oc

let read_length_prefixed_string ic =
  let len = input_binary_int ic in
  if len < 0 || len > 64 * 1024 * 1024 then
    failwith "Response too large"
  else
    really_input_string ic len

let is_native_server_running () =
  try
    let sock = Unix.socket Unix.PF_UNIX Unix.SOCK_STREAM 0 in
    Unix.connect sock (Unix.ADDR_UNIX sock_path);
    Unix.close sock;
    true
  with
  | Unix.Unix_error _ -> false

let start_native_worker () =
  if not (is_native_server_running ()) then (
    printf "Starting native worker (B5)...\n";
    flush_all ();
    
    let compile_cmd = "OPAMSWITCH=l0-testing opam exec -- ocamlopt -I +unix -I +bigarray -o latex_perfectionist_native_worker unix.cmxa bigarray.cmxa latex_perfectionist_native_worker.ml 2>/dev/null" in
    let compile_result = Sys.command compile_cmd in
    
    if compile_result = 0 then (
      let start_cmd = "./latex_perfectionist_native_worker --serve-native &" in
      ignore (Sys.command start_cmd);
      
      let rec wait_for_server retries =
        if retries <= 0 then
          failwith "Native worker failed to start"
        else if is_native_server_running () then
          printf "Native worker ready!\n"
        else (
          Unix.sleepf 0.2;
          wait_for_server (retries - 1)
        )
      in
      wait_for_server 50
    ) else
      failwith "Failed to compile native worker"
  )

let send_request_to_native_worker file_path =
  try
    let sock = Unix.socket Unix.PF_UNIX Unix.SOCK_STREAM 0 in
    Unix.connect sock (Unix.ADDR_UNIX sock_path);
    
    let oc = Unix.out_channel_of_descr sock in
    let ic = Unix.in_channel_of_descr sock in
    
    write_length_prefixed_string oc file_path;
    let response = read_length_prefixed_string ic in
    
    Unix.close sock;
    response
  with
  | Unix.Unix_error (Unix.ENOENT, _, _) | Unix.Unix_error (Unix.ECONNREFUSED, _, _) ->
      printf "Native worker not available\n";
      sprintf "{\"error\": \"Native worker unavailable\", \"file\": \"%s\"}" file_path

let measure_native_latency file_path =
  let start_time = Unix.gettimeofday () in
  let response = send_request_to_native_worker file_path in
  let end_time = Unix.gettimeofday () in
  let elapsed_ms = (end_time -. start_time) *. 1000.0 in
  (response, elapsed_ms)

let show_help () =
  printf "LaTeX Perfectionist v25 (Native B5 Client)\n";
  printf "Usage:\n";
  printf "  %s [OPTIONS] <file.tex>\n" Sys.argv.(0);
  printf "\n";
  printf "Options:\n";
  printf "  --start-native      Start native worker\n";
  printf "  --stop-native       Stop native worker\n";
  printf "  --status-native     Check native worker status\n";
  printf "  --measure           Show client-side latency\n";
  printf "  --help              Show this help\n";
  printf "\n";
  printf "B5 Native Integration:\n";
  printf "  • Direct L0→SoA tokenization\n";
  printf "  • Native L1 macro expansion\n";
  printf "  • Inline validation processing\n";
  printf "  • Streaming JSON response\n";
  printf "  • Target: P99 < 20ms\n"

let stop_native_worker () =
  try
    let pid_cmd = "pgrep -f 'latex_perfectionist_native_worker --serve-native'" in
    let ic = Unix.open_process_in pid_cmd in
    let pid_str = input_line ic in
    ignore (Unix.close_process_in ic);
    let pid = int_of_string (String.trim pid_str) in
    Unix.kill pid Sys.sigterm;
    printf "Native worker stopped (PID %d)\n" pid
  with
  | End_of_file -> printf "No native worker running\n"
  | _ -> printf "Failed to stop native worker\n"

let show_native_status () =
  if is_native_server_running () then
    printf "✅ Native worker server (B5) is running\n"
  else
    printf "❌ Native worker server (B5) is not running\n"

let () =
  let args = Array.to_list Sys.argv in
  match args with
  | [_; "--help"] -> show_help ()
  | [_; "--start-native"] -> 
      start_native_worker ();
      printf "Native worker started\n"
  | [_; "--stop-native"] -> stop_native_worker ()
  | [_; "--status-native"] -> show_native_status ()
  | [_; file_path] ->
      start_native_worker ();
      let response = send_request_to_native_worker file_path in
      print_string response
  | [_; "--measure"; file_path] ->
      start_native_worker ();
      let (response, elapsed_ms) = measure_native_latency file_path in
      printf "=== NATIVE (B5) CLIENT-SIDE LATENCY ===\n";
      printf "File: %s\n" file_path;
      printf "Request latency: %.2f ms\n" elapsed_ms;
      printf "Architecture: Native Integration (B5)\n";
      printf "Response:\n%s\n" response
  | _ ->
      show_help ();
      exit 1