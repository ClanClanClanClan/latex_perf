(* REST API Server for SIMD v2 LaTeX Tokenizer Service *)

open Printf
module Y = Yojson.Safe

(* HTTP server configuration *)
let default_port = 8080
let socket_path = "/tmp/l0_lex_svc.sock"
let max_request_size = 10_000_000 (* 10MB max request *)

(* HTTP response codes *)
let http_ok = "200 OK"
let http_bad_request = "400 Bad Request"
let _http_internal_error = "500 Internal Server Error"
let http_service_unavailable = "503 Service Unavailable"
let http_request_too_large = "413 Request Entity Too Large"

(* CORS headers for browser compatibility *)
let cors_headers =
  [
    "Access-Control-Allow-Origin: *";
    "Access-Control-Allow-Methods: GET, POST, OPTIONS";
    "Access-Control-Allow-Headers: Content-Type";
  ]

(* Send HTTP response *)
let send_response client_sock status headers body =
  let response = sprintf "HTTP/1.1 %s\r\n" status in
  let response = response ^ String.concat "\r\n" headers ^ "\r\n" in
  let response =
    response ^ sprintf "Content-Length: %d\r\n\r\n" (String.length body)
  in
  let response = response ^ body in
  ignore
    (Unix.write client_sock (Bytes.of_string response) 0
       (String.length response))

(* Parse HTTP request *)
let parse_http_request request =
  let lines = String.split_on_char '\n' request in
  match lines with
  | [] -> (None, None, "")
  | first_line :: rest ->
      (* Parse request line *)
      let parts = String.split_on_char ' ' first_line in
      let method_opt = match parts with meth :: _ -> Some meth | _ -> None in
      let path_opt =
        match parts with _ :: path :: _ -> Some path | _ -> None
      in

      (* Find body (after empty line) *)
      let rec find_body lines in_header acc_header =
        match lines with
        | [] -> ("", acc_header)
        | line :: rest ->
            let line = String.trim line in
            if in_header && line = "" then
              (* Found empty line, rest is body *)
              (String.concat "\n" rest, List.rev acc_header)
            else if in_header then find_body rest true (line :: acc_header)
            else find_body rest false acc_header
      in
      let body, _headers = find_body rest true [] in
      (method_opt, path_opt, String.trim body)

(* Connect to SIMD service via Unix socket *)
let connect_to_service () =
  try
    let sock = Unix.socket Unix.PF_UNIX Unix.SOCK_STREAM 0 in
    Unix.connect sock (Unix.ADDR_UNIX socket_path);
    Some sock
  with _ -> None

let[@inline] put_u8 b off v =
  Bytes.unsafe_set b off (Char.unsafe_chr (v land 0xFF))

let[@inline] get_u8 b off = Char.code (Bytes.get b off)

let be32_put b off v =
  put_u8 b off ((v lsr 24) land 0xFF);
  put_u8 b (off + 1) ((v lsr 16) land 0xFF);
  put_u8 b (off + 2) ((v lsr 8) land 0xFF);
  put_u8 b (off + 3) (v land 0xFF)

let be32_get b off =
  (get_u8 b off lsl 24)
  lor (get_u8 b (off + 1) lsl 16)
  lor (get_u8 b (off + 2) lsl 8)
  lor get_u8 b (off + 3)

let be64_put b off v =
  let open Int64 in
  put_u8 b (off + 0) (to_int (shift_right_logical v 56));
  put_u8 b (off + 1) (to_int (shift_right_logical v 48));
  put_u8 b (off + 2) (to_int (shift_right_logical v 40));
  put_u8 b (off + 3) (to_int (shift_right_logical v 32));
  put_u8 b (off + 4) (to_int (shift_right_logical v 24));
  put_u8 b (off + 5) (to_int (shift_right_logical v 16));
  put_u8 b (off + 6) (to_int (shift_right_logical v 8));
  put_u8 b (off + 7) (to_int v)

let be64_get b off =
  let open Int64 in
  let byte i = of_int (get_u8 b (off + i)) in
  logor
    (shift_left (byte 0) 56)
    (logor
       (shift_left (byte 1) 48)
       (logor
          (shift_left (byte 2) 40)
          (logor
             (shift_left (byte 3) 32)
             (logor
                (shift_left (byte 4) 24)
                (logor
                   (shift_left (byte 5) 16)
                   (logor (shift_left (byte 6) 8) (byte 7)))))))

let rec read_exact fd buf ofs len =
  if len = 0 then ()
  else
    match Unix.read fd buf ofs len with
    | 0 -> failwith "short read"
    | n -> read_exact fd buf (ofs + n) (len - n)

let rec write_all fd buf ofs len =
  if len = 0 then ()
  else
    match Unix.write fd buf ofs len with
    | 0 -> failwith "short write"
    | n -> write_all fd buf (ofs + n) (len - n)

let req_counter = ref 0L

let next_req_id () =
  let id = !req_counter in
  req_counter := Int64.succ id;
  id

(* Send request to SIMD service and get response *)
let call_simd_service latex_content =
  match connect_to_service () with
  | None -> Error "Cannot connect to SIMD service"
  | Some service_sock -> (
      let cleanup () = Unix.close service_sock in
      try
        let len = String.length latex_content in
        if len > Latex_parse_lib.Config.max_req_bytes then (
          cleanup ();
          Error "request too large")
        else
          let payload_len = 4 + len in
          let payload = Bytes.create payload_len in
          be32_put payload 0 len;
          Bytes.blit_string latex_content 0 payload 4 len;
          let req_id = next_req_id () in
          let header = Bytes.create 16 in
          be32_put header 0 1;
          be64_put header 4 req_id;
          be32_put header 12 payload_len;
          write_all service_sock header 0 16;
          write_all service_sock payload 0 payload_len;

          let resp_header = Bytes.create 16 in
          read_exact service_sock resp_header 0 16;
          let msg_type = be32_get resp_header 0 in
          let resp_id = be64_get resp_header 4 in
          let resp_len = be32_get resp_header 12 in
          if msg_type <> 2 || resp_id <> req_id then (
            cleanup ();
            Error "invalid response header")
          else
            let response = Bytes.create resp_len in
            read_exact service_sock response 0 resp_len;
            cleanup ();
            Ok response
      with exn ->
        cleanup ();
        Error (sprintf "Service error: %s" (Printexc.to_string exn)))

(* Handle /tokenize endpoint *)
let log_error fmt = Printf.kfprintf (fun _ -> prerr_newline ()) stderr fmt

let json_error ?(code = 1) msg =
  Y.to_string @@ `Assoc [ ("error", `String msg); ("code", `Int code) ]

let service_name = "l0-lex"
let service_version = "v25"
let now_ts () = int_of_float (Unix.gettimeofday ())

let json_ok ~expanded ~status ~origin ~n_tokens ~issues_len ~req_bytes
    ~validators ~v_duration_ms ~v_timings =
  let svc =
    `Assoc
      [
        ("name", `String service_name);
        ("version", `String service_version);
        ("ts", `Int (now_ts ()));
      ]
  in
  let metrics =
    `Assoc
      [
        ("n_tokens", `Int n_tokens);
        ("issues_len", `Int issues_len);
        ("request_bytes", `Int req_bytes);
      ]
  in
  let v_applied = List.length validators in
  let v_errors =
    List.fold_left
      (fun acc (_id, sev, _msg, cnt) ->
        match sev with `String "error" -> acc + cnt | _ -> acc)
      0 validators
  in
  let v_results =
    `List
      (List.map
         (fun (id, sev, msg, cnt) ->
           `Assoc
             [
               ("id", `String id);
               ("severity", sev);
               ("message", `String msg);
               ("count", `Int cnt);
             ])
         validators)
  in
  let validators =
    `Assoc
      [
        ("applied", `Int v_applied);
        ("errors", `Int v_errors);
        ("results", v_results);
      ]
  in
  let validators =
    match Sys.getenv_opt "L0_INCLUDE_VALIDATORS_DURATION" with
    | Some ("1" | "true" | "on") -> (
        match validators with
        | `Assoc kv -> `Assoc (("duration_ms", `Float v_duration_ms) :: kv)
        | _ -> validators)
    | _ -> validators
  in
  let validators =
    match Sys.getenv_opt "L0_INCLUDE_VALIDATORS_TIMINGS" with
    | Some ("1" | "true" | "on") -> (
        let arr =
          `List
            (List.map
               (fun (id, ms) ->
                 `Assoc [ ("id", `String id); ("duration_ms", `Float ms) ])
               v_timings)
        in
        match validators with
        | `Assoc kv -> `Assoc (("timings", arr) :: kv)
        | _ -> validators)
    | _ -> validators
  in
  let base =
    [
      ("ok", `Bool (status = 0));
      ("status", `Int status);
      ("origin", `String origin);
      ("metrics", metrics);
      ("validators", validators);
      ("service", svc);
    ]
  in
  let base =
    match expanded with
    | None -> base
    | Some s -> ("expanded", `String s) :: base
  in
  Y.to_string @@ `Assoc base

let handle_tokenize body =
  (* Parse JSON request with Yojson: expect {"latex": "...", "expand": bool?,
     "catalogue": obj?} *)
  let extract_latex_content body =
    try
      match Y.from_string body with
      | `Assoc props -> (
          let latex =
            match List.assoc_opt "latex" props with
            | Some (`String s) -> Some s
            | _ -> None
          in
          let expand =
            match List.assoc_opt "expand" props with
            | Some (`Bool b) -> b
            | _ -> false
          in
          let cfg =
            match List.assoc_opt "catalogue" props with
            | Some j -> Rest_simple_expander.of_json j
            | _ -> Rest_simple_expander.default
          in
          match latex with
          | Some s ->
              let s' =
                if expand then Rest_simple_expander.expand_fix cfg s else s
              in
              Some (s', expand)
          | None -> None)
      | _ -> None
    with _ -> None
  in

  match extract_latex_content body with
  | None ->
      let error_json =
        json_error ~code:400
          "Invalid request format. Expected {\"latex\": \"...\"}"
      in
      (http_bad_request, error_json)
  | Some (latex_content, did_expand) -> (
      match call_simd_service latex_content with
      | Error msg ->
          log_error "[rest] service error: %s" msg;
          let error_json = json_error ~code:503 msg in
          (http_service_unavailable, error_json)
      | Ok resp -> (
          (* Expect 13-byte status payload; use shared parser *)
          match Latex_parse_lib.Service_payload.parse_payload resp with
          | Error e ->
              let json = json_error ~code:503 e in
              (http_service_unavailable, json)
          | Ok p ->
              let origin =
                match p.Latex_parse_lib.Service_payload.origin with
                | Latex_parse_lib.Service_payload.Primary -> "primary"
                | Latex_parse_lib.Service_payload.Hedge -> "hedge"
                | Latex_parse_lib.Service_payload.Unknown -> "unknown"
              in
              let vres, vdur, vtim =
                let open Latex_parse_lib in
                let xs, dur, timings =
                  Validators.run_all_with_timings latex_content
                in
                ( List.map
                    (fun (r : Latex_parse_lib.Validators.result) ->
                      let open Latex_parse_lib.Validators in
                      let { id; severity; message; count } = r in
                      (id, `String (severity_to_string severity), message, count))
                    xs,
                  dur,
                  timings )
              in
              let json =
                json_ok
                  ~expanded:(if did_expand then Some latex_content else None)
                  ~status:p.status ~origin ~n_tokens:p.n_tokens
                  ~issues_len:p.issues_len
                  ~req_bytes:(String.length latex_content)
                  ~validators:vres ~v_duration_ms:vdur ~v_timings:vtim
              in
              ( (if p.status = 0 then http_ok else http_service_unavailable),
                json )))

(* Handle /health endpoint *)
let handle_health () =
  (* Bond health to an actual processing path: send a minimal request. *)
  match call_simd_service " " with
  | Ok resp -> (
      match Latex_parse_lib.Service_payload.parse_payload resp with
      | Ok p when p.Latex_parse_lib.Service_payload.status = 0 ->
          let json =
            Y.to_string
            @@ `Assoc
                 [
                   ("status", `String "healthy"); ("n_tokens", `Int p.n_tokens);
                 ]
          in
          (http_ok, json)
      | Ok p ->
          let json =
            json_error ~code:503 (Printf.sprintf "status=%d" p.status)
          in
          (http_service_unavailable, json)
      | Error e ->
          let json = json_error ~code:503 e in
          (http_service_unavailable, json))
  | Error msg ->
      let json = json_error ~code:503 msg in
      (http_service_unavailable, json)

(* Handle /metrics endpoint (Prometheus format) *)
let handle_metrics () =
  let metrics =
    [
      "# HELP latex_tokenizer_requests_total Total number of tokenization \
       requests";
      "# TYPE latex_tokenizer_requests_total counter";
      "latex_tokenizer_requests_total 0";
      "";
      "# HELP latex_tokenizer_latency_seconds Tokenization latency in seconds";
      "# TYPE latex_tokenizer_latency_seconds histogram";
      "latex_tokenizer_latency_seconds_bucket{le=\"0.01\"} 0";
      "latex_tokenizer_latency_seconds_bucket{le=\"0.05\"} 0";
      "latex_tokenizer_latency_seconds_bucket{le=\"0.1\"} 0";
      "latex_tokenizer_latency_seconds_bucket{le=\"+Inf\"} 0";
      "latex_tokenizer_latency_seconds_sum 0";
      "latex_tokenizer_latency_seconds_count 0";
      "";
      "# HELP latex_tokenizer_up Service availability (1 = up, 0 = down)";
      "# TYPE latex_tokenizer_up gauge";
    ]
  in

  let is_up =
    match connect_to_service () with
    | None -> "0"
    | Some sock ->
        Unix.close sock;
        "1"
  in

  let metrics_text =
    String.concat "\n" metrics ^ sprintf "latex_tokenizer_up %s\n" is_up
  in
  (http_ok, metrics_text)

(* Handle client connection *)
let handle_client client_sock _client_addr =
  let buffer = Bytes.create max_request_size in
  try
    let n = Unix.read client_sock buffer 0 max_request_size in
    if n > 0 then (
      let request = Bytes.sub_string buffer 0 n in
      let method_opt, path_opt, body = parse_http_request request in

      let status, response_body =
        match (method_opt, path_opt) with
        | Some "OPTIONS", _ ->
            (* Handle CORS preflight *)
            (http_ok, "")
        | Some "GET", Some "/health" -> handle_health ()
        | Some "GET", Some "/metrics" -> handle_metrics ()
        | Some "POST", Some "/tokenize" ->
            if String.length body > max_request_size then
              (http_request_too_large, "{\"error\": \"Request too large\"}")
            else handle_tokenize body
        | Some "POST", Some path
          when String.length path >= 7 && String.sub path 0 7 = "/expand" -> (
            try
              match Y.from_string body with
              | `Assoc props -> (
                  match List.assoc_opt "latex" props with
                  | Some (`String s) ->
                      let cfg =
                        match List.assoc_opt "catalogue" props with
                        | Some j -> Rest_simple_expander.of_json j
                        | _ -> Rest_simple_expander.default
                      in
                      let expanded = Rest_simple_expander.expand_fix cfg s in
                      let open Latex_parse_lib in
                      let layer =
                        if String.contains path '?' then
                          try
                            let q =
                              String.sub path
                                (String.index path '?' + 1)
                                (String.length path
                                - (String.index path '?' + 1))
                            in
                            if String.contains q '=' then
                              let parts = String.split_on_char '&' q in
                              let rec find_layer = function
                                | [] -> Validators.L0
                                | kv :: rest -> (
                                    match String.split_on_char '=' kv with
                                    | [ k; v ] when k = "layer" && v = "l1" ->
                                        Validators.L1
                                    | _ -> find_layer rest)
                              in
                              find_layer parts
                            else Validators.L0
                          with _ -> Validators.L0
                        else Validators.L0
                      in
                      (* Tokenize expanded text and build per-request command
                         spans for validator context *)
                      let module T = Latex_parse_lib.Tokenizer_lite in
                      let toks = T.tokenize expanded in
                      let n = String.length expanded in
                      let cmd_spans =
                        List.fold_left
                          (fun acc (t : T.tok) ->
                            match t.kind with
                            | T.Command ->
                                let i' = t.s + 1 in
                                let k = ref i' in
                                while
                                  !k < n
                                  &&
                                  let ch = String.unsafe_get expanded !k in
                                  (ch >= 'a' && ch <= 'z')
                                  || (ch >= 'A' && ch <= 'Z')
                                do
                                  incr k
                                done;
                                if !k > i' then
                                  ({
                                     Latex_parse_lib.Validators_context.name =
                                       String.sub expanded i' (!k - i');
                                     s = t.s;
                                     e = t.e;
                                   }
                                    : Latex_parse_lib.Validators_context
                                      .post_command)
                                  :: acc
                                else acc
                            | _ -> acc)
                          [] toks
                        |> List.rev
                      in
                      Latex_parse_lib.Validators_context.set_post_commands
                        cmd_spans;
                      let xs, vdur, vtim =
                        Validators.run_all_with_timings_for_layer expanded layer
                      in
                      let tuples =
                        List.map
                          (fun (r : Latex_parse_lib.Validators.result) ->
                            let open Latex_parse_lib.Validators in
                            let { id; severity; message; count } = r in
                            ( id,
                              `String (severity_to_string severity),
                              message,
                              count ))
                          xs
                      in
                      (* Build JSON; include post-expansion tokens if debug flag
                         is set *)
                      let include_post =
                        match Sys.getenv_opt "L0_DEBUG_L1" with
                        | Some ("1" | "true" | "on") -> true
                        | _ -> false
                      in
                      let base_json =
                        json_ok ~expanded:(Some expanded) ~status:0
                          ~origin:"primary" ~n_tokens:0 ~issues_len:0
                          ~req_bytes:(String.length s) ~validators:tuples
                          ~v_duration_ms:vdur ~v_timings:vtim
                      in
                      let json =
                        if include_post then
                          let kind_to_string = function
                            | T.Word -> "word"
                            | T.Space -> "space"
                            | T.Newline -> "newline"
                            | T.Command -> "command"
                            | T.Bracket_open -> "bracket_open"
                            | T.Bracket_close -> "bracket_close"
                            | T.Quote -> "quote"
                            | T.Symbol -> "symbol"
                          in
                          let arr =
                            `List
                              (List.map
                                 (fun (t : T.tok) ->
                                   `Assoc
                                     [
                                       ("kind", `String (kind_to_string t.kind));
                                       ("s", `Int t.s);
                                       ("e", `Int t.e);
                                       ( "ch",
                                         match t.ch with
                                         | None -> `Null
                                         | Some c -> `String (String.make 1 c)
                                       );
                                     ])
                                 toks)
                          in
                          let cmds =
                            `List
                              (List.map
                                 (fun (pc :
                                        Latex_parse_lib.Validators_context
                                        .post_command) -> `String pc.name)
                                 cmd_spans)
                          in
                          let post_summary =
                            let ecmds =
                              `List
                                (List.map
                                   (fun (pc :
                                          Latex_parse_lib.Validators_context
                                          .post_command) ->
                                     `Assoc
                                       [
                                         ("name", `String pc.name);
                                         ("s", `Int pc.s);
                                         ("e", `Int pc.e);
                                       ])
                                   cmd_spans)
                            in
                            `Assoc [ ("commands", ecmds) ]
                          in
                          match Y.from_string base_json with
                          | `Assoc kv ->
                              Y.to_string
                                (`Assoc
                                  (("post_tokens", arr)
                                  :: ("post_commands", cmds)
                                  :: ("post_summary", post_summary)
                                  :: kv))
                          | _ -> base_json
                        else base_json
                      in
                      (http_ok, json)
                  | _ ->
                      ( http_bad_request,
                        json_error ~code:400 "Missing 'latex' field" ))
              | _ -> (http_bad_request, json_error ~code:400 "Invalid JSON")
            with _ ->
              (http_bad_request, json_error ~code:400 "Invalid request"))
        | Some "POST", Some "/tokens" -> (
            match Sys.getenv_opt "L0_DEBUG_TOKENS" with
            | Some ("1" | "true" | "on") -> (
                try
                  match Y.from_string body with
                  | `Assoc props -> (
                      match List.assoc_opt "latex" props with
                      | Some (`String s) ->
                          let module T = Latex_parse_lib.Tokenizer_lite in
                          let toks = T.tokenize s in
                          let kind_to_string = function
                            | T.Word -> "word"
                            | T.Space -> "space"
                            | T.Newline -> "newline"
                            | T.Command -> "command"
                            | T.Bracket_open -> "bracket_open"
                            | T.Bracket_close -> "bracket_close"
                            | T.Quote -> "quote"
                            | T.Symbol -> "symbol"
                          in
                          let arr =
                            `List
                              (List.map
                                 (fun (t : T.tok) ->
                                   `Assoc
                                     [
                                       ("kind", `String (kind_to_string t.kind));
                                       ("s", `Int t.s);
                                       ("e", `Int t.e);
                                       ( "ch",
                                         match t.ch with
                                         | None -> `Null
                                         | Some c -> `String (String.make 1 c)
                                       );
                                     ])
                                 toks)
                          in
                          ( http_ok,
                            Y.to_string
                              (`Assoc
                                [
                                  ("count", `Int (List.length toks));
                                  ("tokens", arr);
                                ]) )
                      | _ ->
                          ( http_bad_request,
                            json_error ~code:400 "Missing 'latex' field" ))
                  | _ -> (http_bad_request, json_error ~code:400 "Invalid JSON")
                with _ ->
                  (http_bad_request, json_error ~code:400 "Invalid request"))
            | _ ->
                ( http_bad_request,
                  json_error ~code:403 "token debugging disabled" ))
        | Some "GET", Some "/ready" -> (
            (* Cheap probe: only tests socket readiness, not full processing *)
            match connect_to_service () with
            | None ->
                ( http_service_unavailable,
                  json_error ~code:503 "service not ready" )
            | Some sock ->
                Unix.close sock;
                (http_ok, Y.to_string @@ `Assoc [ ("ready", `Bool true) ]))
        | Some "GET", Some "/" ->
            let welcome =
              {|{
  "service": "LaTeX Perfectionist v25 REST API",
  "version": "1.0.0",
  "endpoints": {
    "POST /tokenize": "Tokenize LaTeX content",
    "GET /health": "Health check",
    "GET /metrics": "Prometheus metrics"
  }
}|}
            in
            (http_ok, welcome)
        | _ -> (http_bad_request, "{\"error\": \"Unknown endpoint\"}")
      in

      let headers = cors_headers @ [ "Content-Type: application/json" ] in
      send_response client_sock status headers response_body;
      (* Clear per-thread validator context now that the response has been
         sent *)
      Latex_parse_lib.Validators_context.clear ())
  with
  | Unix.Unix_error (Unix.EAGAIN, _, _) -> ()
  | exn ->
      eprintf "Client handler error: %s\n%!" (Printexc.to_string exn);
      Unix.close client_sock

(* Main server loop *)
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

  (* Accept connections *)
  while true do
    try
      let client_sock, client_addr = Unix.accept server_sock in
      (* Handle in separate thread for concurrency *)
      ignore
        (Thread.create (fun () -> handle_client client_sock client_addr) ())
    with
    | Unix.Unix_error (Unix.EINTR, _, _) -> ()
    | exn -> eprintf "Accept error: %s\n%!" (Printexc.to_string exn)
  done

(* Entry point *)
let () =
  let port =
    match Sys.argv with
    | [| _; "-p"; port_str |] -> (
        try int_of_string port_str with _ -> default_port)
    | _ -> default_port
  in

  (* Check if service is available *)
  match connect_to_service () with
  | None ->
      eprintf "Error: SIMD service not running at %s\n" socket_path;
      eprintf "Please start the service first with: make service-run\n";
      exit 1
  | Some sock -> (
      Unix.close sock;
      printf "Connected to SIMD service at %s\n%!" socket_path;

      (* Start HTTP server *)
      try start_server port
      with exn ->
        eprintf "Server error: %s\n" (Printexc.to_string exn);
        exit 1)
