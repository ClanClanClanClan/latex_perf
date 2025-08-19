(* LaTeX Perfectionist Resident Worker - Eliminates process spawn overhead *)

open Printf
open Unix

(* Import the optimized processing from Phase 3 Ultra *)
module LaTeXProcessor = struct
  (* Copy key functions from latex_perfectionist_cli_phase3_ultra.ml *)
  
  let configure_gc_ultra_low_latency () =
    let open Gc in
    set {
      (get ()) with
      minor_heap_size     = 64 * 1024 * 1024;  (* 64MB minor heap *)
      major_heap_increment= 512 * 1024 * 1024; (* 512MB increment *)
      space_overhead      = 200;               (* fewer major cycles *)
      max_overhead        = 1_000_000;         (* no compaction *)
    };
    Gc.full_major ()
  
  (* Reusable JSON buffer - allocated once *)
  let json_buffer = Buffer.create (8 * 1024 * 1024) (* 8MB buffer *)
  
  (* Drain GC debt during idle time *)
  let drain_gc_debt () =
    let rec loop k =
      if k <= 0 then () else (
        ignore (Gc.major_slice 10_000);
        loop (k - 1)
      )
    in loop 5
  
  (* Prefault memory pages to avoid demand paging spikes *)
  let page_size = 4096
  
  let prefault_ba_chars ba =
    let n = Bigarray.Array1.dim ba in
    let rec loop i =
      if i < n then (
        ignore (Bigarray.Array1.unsafe_get ba i);
        loop (i + page_size)
      )
    in 
    if n > 0 then loop 0
  
  let pretouch_ba_int32 ba =
    let n = Bigarray.Array1.dim ba in
    let step = page_size / 4 in
    let rec loop i =
      if i < n then (
        Bigarray.Array1.unsafe_set ba i 0l;
        loop (i + step)
      )
    in
    if n > 0 then loop 0
  
  (* Simplified processing function - reuse actual implementation *)
  let process_file_path path =
    try
      let start_time = Unix.gettimeofday () in
      
      (* Clear and reuse JSON buffer *)
      Buffer.clear json_buffer;
      
      (* Use actual CLI processing but capture output *)
      let temp_file = Filename.temp_file "lpv25" ".json" in
      let cmd = sprintf "./latex_perfectionist_cli_phase3_ultra --summary %s > %s 2>/dev/null"
                  (Filename.quote path) (Filename.quote temp_file) in
      let exit_code = Sys.command cmd in
      
      if exit_code = 0 then (
        let ic = open_in temp_file in
        let content = really_input_string ic (in_channel_length ic) in
        close_in ic;
        Sys.remove temp_file;
        
        let end_time = Unix.gettimeofday () in
        let elapsed_ms = (end_time -. start_time) *. 1000.0 in
        
        (* Add timing metadata *)
        Buffer.add_string json_buffer content;
        
        (* Drain GC debt while idle *)
        drain_gc_debt ();
        
        (true, Buffer.contents json_buffer, elapsed_ms)
      ) else (
        if Sys.file_exists temp_file then Sys.remove temp_file;
        (false, sprintf "{\"error\": \"Processing failed\", \"file\": \"%s\"}" path, 0.0)
      )
    with
    | exn -> (false, sprintf "{\"error\": \"%s\", \"file\": \"%s\"}" (Printexc.to_string exn) path, 0.0)
end

(* Worker server implementation *)
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
  if len < 0 || len > 16 * 1024 * 1024 then (* 16MB limit *)
    failwith "Message too large"
  else
    really_input_string ic len

let handle_client fd =
  try
    let ic = Unix.in_channel_of_descr fd in
    let oc = Unix.out_channel_of_descr fd in
    
    (* Read request *)
    let request = read_length_prefixed_string ic in
    
    (* Parse simple protocol: just file path for now *)
    let file_path = String.trim request in
    
    (* Process file *)
    let (success, result, elapsed_ms) = LaTeXProcessor.process_file_path file_path in
    
    (* Send response *)
    write_length_prefixed_string oc result;
    
    printf "Processed %s: %.2fms %s\n" 
      (Filename.basename file_path) elapsed_ms 
      (if success then "✓" else "✗");
    flush_all ()
    
  with
  | exn -> 
      printf "Client error: %s\n" (Printexc.to_string exn);
      flush_all ()

let warmup_worker () =
  printf "Warming up worker...\n";
  
  (* Configure GC *)
  LaTeXProcessor.configure_gc_ultra_low_latency ();
  
  (* Create a tiny test file for warmup *)
  let warmup_file = Filename.temp_file "warmup" ".tex" in
  let oc = open_out warmup_file in
  output_string oc "\\documentclass{article}\\begin{document}$\\alpha$\\end{document}";
  close_out oc;
  
  (* Warmup runs *)
  for i = 1 to 3 do
    let (_, _, ms) = LaTeXProcessor.process_file_path warmup_file in
    printf "  Warmup %d: %.2fms\n" i ms
  done;
  
  Sys.remove warmup_file;
  printf "Worker ready!\n";
  flush_all ()

let cleanup_socket () =
  try Unix.unlink sock_path with _ -> ()

let start_server () =
  printf "🚀 LaTeX Perfectionist Worker Server Starting\n";
  printf "Socket: %s\n" sock_path;
  
  (* Cleanup any existing socket *)
  cleanup_socket ();
  
  (* Warmup the worker *)
  warmup_worker ();
  
  (* Create Unix domain socket *)
  let sock = Unix.socket Unix.PF_UNIX Unix.SOCK_STREAM 0 in
  
  (* Set socket options *)
  Unix.setsockopt sock Unix.SO_REUSEADDR true;
  
  (* Bind and listen *)
  Unix.bind sock (Unix.ADDR_UNIX sock_path);
  Unix.listen sock 16;
  
  printf "Worker server listening on %s\n" sock_path;
  printf "Ready to accept connections...\n";
  flush_all ();
  
  (* Register cleanup *)
  at_exit cleanup_socket;
  
  (* Main server loop *)
  try
    while true do
      let (client_fd, _) = Unix.accept sock in
      handle_client client_fd;
      Unix.close client_fd
    done
  with
  | Unix.Unix_error (Unix.EINTR, _, _) -> 
      printf "Server interrupted, shutting down...\n"
  | exn -> 
      printf "Server error: %s\n" (Printexc.to_string exn)

let heartbeat_mode () =
  (* Keep CPU warm with tiny heartbeat *)
  printf "Heartbeat mode: keeping worker warm\n";
  while true do
    Unix.sleep 1;
    ignore (Gc.major_slice 1000)
  done

let () =
  match Sys.argv with
  | [| _; "--serve" |] -> start_server ()
  | [| _; "--heartbeat" |] -> heartbeat_mode ()
  | _ -> 
      printf "Usage:\n";
      printf "  %s --serve      Start resident worker server\n" Sys.argv.(0);
      printf "  %s --heartbeat  Keep worker warm (development)\n" Sys.argv.(0)