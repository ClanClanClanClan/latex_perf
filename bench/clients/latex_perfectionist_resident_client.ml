(* Thin Client for Persistent Worker *)

open Unix
open Printf

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

let connect_and_request sock_path file_path =
  let sock = socket PF_UNIX SOCK_STREAM 0 in
  connect sock (ADDR_UNIX sock_path);
  
  let ic = in_channel_of_descr sock in
  let oc = out_channel_of_descr sock in
  
  (* Send request *)
  write_length_prefixed oc file_path;
  
  (* Read response *)
  let response = read_length_prefixed ic in
  
  close sock;
  response

let () =
  let sock_path = 
    try Sys.getenv "LP_SOCKET"
    with Not_found -> "/tmp/latex_perfectionist.sock"
  in
  
  match Sys.argv with
  | [| _; file_path |] ->
      (try
        let response = connect_and_request sock_path file_path in
        print_endline response
      with
      | Unix_error (ENOENT, _, _) | Unix_error (ECONNREFUSED, _, _) ->
          eprintf "Error: Worker not running. Start with:\n";
          eprintf "  latex_perfectionist_resident_worker --serve &\n";
          exit 1
      | exn ->
          eprintf "Error: %s\n" (Printexc.to_string exn);
          exit 1)
  | _ ->
      eprintf "Usage: %s <file.tex>\n" Sys.argv.(0);
      exit 1