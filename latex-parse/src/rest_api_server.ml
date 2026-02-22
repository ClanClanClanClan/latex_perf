(* rest_api_server.ml — Thin dispatcher + server entry point.

   Transport lives in Rest_http; endpoint logic in Rest_handlers. This file owns
   the accept loop, route table, and catalogue loading. *)

open Printf

(* ── Server configuration ─────────────────────────────────────────── *)

let default_port = 8080

(* Global macro catalogue, set once at startup *)
let global_catalogue : Latex_parse_lib.Macro_catalogue.catalogue option ref =
  ref None

(* ── Route dispatch ───────────────────────────────────────────────── *)

let handle_client client_sock _client_addr =
  let buffer = Bytes.create Rest_http.max_request_size in
  try
    let n = Unix.read client_sock buffer 0 Rest_http.max_request_size in
    if n > 0 then (
      let request = Bytes.sub_string buffer 0 n in
      let method_opt, path_opt, body = Rest_http.parse_http_request request in

      let status, response_body =
        match (method_opt, path_opt) with
        | Some "OPTIONS", _ ->
            (* CORS preflight *)
            (Rest_http.http_ok, "")
        | Some "GET", Some "/health" -> Rest_handlers.handle_health ()
        | Some "GET", Some "/metrics" -> Rest_handlers.handle_metrics ()
        | Some "POST", Some "/tokenize" ->
            if String.length body > Rest_http.max_request_size then
              ( Rest_http.http_request_too_large,
                "{\"error\": \"Request too large\"}" )
            else Rest_handlers.handle_tokenize body ~catalogue:!global_catalogue
        | Some "POST", Some path
          when String.length path >= 7 && String.sub path 0 7 = "/expand" ->
            Rest_handlers.handle_expand body path ~catalogue:!global_catalogue
        | Some "POST", Some "/tokens" -> Rest_handlers.handle_tokens body
        | Some "GET", Some "/ready" -> Rest_handlers.handle_ready ()
        | Some "GET", Some "/" -> Rest_handlers.handle_welcome ()
        | _ -> (Rest_http.http_bad_request, "{\"error\": \"Unknown endpoint\"}")
      in

      let headers =
        Rest_http.cors_headers @ [ "Content-Type: application/json" ]
      in
      Rest_http.send_response client_sock status headers response_body;
      (* Clear per-thread validator context *)
      Latex_parse_lib.Validators_context.clear ())
  with
  | Unix.Unix_error (Unix.EAGAIN, _, _) -> ()
  | exn ->
      eprintf "Client handler error: %s\n%!" (Printexc.to_string exn);
      Unix.close client_sock

(* ── Server loop ──────────────────────────────────────────────────── *)

let start_server port =
  let server_sock = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
  Unix.setsockopt server_sock Unix.SO_REUSEADDR true;

  let addr = Unix.ADDR_INET (Unix.inet_addr_any, port) in
  Unix.bind server_sock addr;
  Unix.listen server_sock 10;

  printf "REST API Server listening on port %d\n%!" port;
  printf "Endpoints:\n";
  printf "  POST /tokenize - Tokenize LaTeX content\n";
  printf "  GET /health   - Health check\n";
  printf "  GET /metrics  - Prometheus metrics\n\n%!";

  while true do
    try
      let client_sock, client_addr = Unix.accept server_sock in
      ignore
        (Thread.create (fun () -> handle_client client_sock client_addr) ())
    with
    | Unix.Unix_error (Unix.EINTR, _, _) -> ()
    | exn -> eprintf "Accept error: %s\n%!" (Printexc.to_string exn)
  done

(* ── Macro catalogue loading ──────────────────────────────────────── *)

let default_v25r2_path = "data/macro_catalogue.v25r2.json"
let default_argsafe_path = "data/macro_catalogue.argsafe.v25r1.json"

let load_catalogue () =
  let v25r2_path =
    match Sys.getenv_opt "L0_CATALOGUE_V25R2" with
    | Some p -> p
    | None -> default_v25r2_path
  in
  let argsafe_path =
    match Sys.getenv_opt "L0_CATALOGUE_ARGSAFE" with
    | Some p -> p
    | None -> default_argsafe_path
  in
  if Sys.file_exists v25r2_path && Sys.file_exists argsafe_path then (
    try
      let cat =
        Latex_parse_lib.Macro_catalogue.load ~v25r2_path ~argsafe_path
      in
      printf "[rest] Loaded macro catalogue: %d symbols + %d argsafe macros\n%!"
        (Latex_parse_lib.Macro_catalogue.symbol_count cat)
        (Latex_parse_lib.Macro_catalogue.argsafe_count cat);
      Some cat
    with exn ->
      eprintf "[rest] WARNING: failed to load macro catalogue: %s\n%!"
        (Printexc.to_string exn);
      None)
  else (
    eprintf
      "[rest] Macro catalogue not found (%s, %s); using legacy expander\n%!"
      v25r2_path argsafe_path;
    None)

(* ── Entry point ──────────────────────────────────────────────────── *)

let () =
  let port =
    match Sys.argv with
    | [| _; "-p"; port_str |] -> (
        try int_of_string port_str with Failure _ -> default_port)
    | _ -> default_port
  in

  (* Load macro catalogue *)
  global_catalogue := load_catalogue ();

  (* Check if service is available *)
  match Rest_http.connect_to_service () with
  | None ->
      eprintf "Error: SIMD service not running at %s\n" Rest_http.socket_path;
      eprintf "Please start the service first with: make service-run\n";
      exit 1
  | Some sock -> (
      Unix.close sock;
      printf "Connected to SIMD service at %s\n%!" Rest_http.socket_path;

      try start_server port
      with exn ->
        eprintf "Server error: %s\n" (Printexc.to_string exn);
        exit 1)
