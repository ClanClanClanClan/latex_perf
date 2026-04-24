(* rest_handlers.ml — Endpoint handler functions for the REST API.

   Each handler returns [(status, body)] — the HTTP status string and JSON
   response body. The dispatcher in rest_api_server.ml calls these and forwards
   the result to Rest_http.send_response. *)

module Y = Yojson.Safe

(* ── JSON response builders ────────────────────────────────────────── *)

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

(* ── POST /tokenize ────────────────────────────────────────────────── *)

let handle_tokenize body ~catalogue =
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
          let cfg = Rest_simple_expander.with_catalogue cfg catalogue in
          match latex with
          | Some s ->
              let s' =
                if expand then Rest_simple_expander.expand_fix cfg s else s
              in
              Some (s', expand)
          | None -> None)
      | _ -> None
    with Yojson.Safe.Util.Type_error _ | Failure _ -> None
  in
  match extract_latex_content body with
  | None ->
      let error_json =
        json_error ~code:400
          "Invalid request format. Expected {\"latex\": \"...\"}"
      in
      (Rest_http.http_bad_request, error_json)
  | Some (latex_content, did_expand) -> (
      match Rest_http.call_simd_service latex_content with
      | Error msg ->
          log_error "[rest] service error: %s" msg;
          let error_json = json_error ~code:503 msg in
          (Rest_http.http_service_unavailable, error_json)
      | Ok resp -> (
          match Latex_parse_lib.Service_payload.parse_payload resp with
          | Error e ->
              let json = json_error ~code:503 e in
              (Rest_http.http_service_unavailable, json)
          | Ok p ->
              let origin =
                match p.Latex_parse_lib.Service_payload.origin with
                | Latex_parse_lib.Service_payload.Primary -> "primary"
                | Latex_parse_lib.Service_payload.Hedge -> "hedge"
                | Latex_parse_lib.Service_payload.Unknown -> "unknown"
              in
              (* Set up language profile context for PR #236 (memo §4).
                 L0_PROFILE_OVERRIDE takes precedence; otherwise
                 auto-classify. *)
              let _profile_tier =
                match Sys.getenv_opt "L0_PROFILE_OVERRIDE" with
                | Some s -> (
                    match Latex_parse_lib.Language_profile.tier_of_string s with
                    | Some t -> t
                    | None ->
                        fst
                          (Latex_parse_lib.Language_profile.classify_source
                             latex_content))
                | None ->
                    fst
                      (Latex_parse_lib.Language_profile.classify_source
                         latex_content)
              in
              Latex_parse_lib.Language_profile.Context.set _profile_tier;
              (* Set up user macro context for CMD-015/016/017 *)
              let _reg =
                Latex_parse_lib.User_macro_registry.create latex_content
              in
              Latex_parse_lib.User_macro_context.set _reg;
              let vres, vdur, vtim =
                let open Latex_parse_lib in
                let xs, dur, timings =
                  Validators.run_all_with_timings latex_content
                in
                ( List.map
                    (fun (r : Latex_parse_lib.Validators.result) ->
                      let open Latex_parse_lib.Validators in
                      let { id; severity; message; count; _ } = r in
                      (id, `String (severity_to_string severity), message, count))
                    xs,
                  dur,
                  timings )
              in
              Latex_parse_lib.User_macro_context.clear ();
              Latex_parse_lib.Language_profile.Context.clear ();
              let json =
                json_ok
                  ~expanded:(if did_expand then Some latex_content else None)
                  ~status:p.status ~origin ~n_tokens:p.n_tokens
                  ~issues_len:p.issues_len
                  ~req_bytes:(String.length latex_content)
                  ~validators:vres ~v_duration_ms:vdur ~v_timings:vtim
              in
              ( (if p.status = 0 then Rest_http.http_ok
                 else Rest_http.http_service_unavailable),
                json )))

(* ── GET /health ───────────────────────────────────────────────────── *)

let handle_health () =
  match Rest_http.call_simd_service " " with
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
          (Rest_http.http_ok, json)
      | Ok p ->
          let json =
            json_error ~code:503 (Printf.sprintf "status=%d" p.status)
          in
          (Rest_http.http_service_unavailable, json)
      | Error e ->
          let json = json_error ~code:503 e in
          (Rest_http.http_service_unavailable, json))
  | Error msg ->
      let json = json_error ~code:503 msg in
      (Rest_http.http_service_unavailable, json)

(* ── GET /metrics ──────────────────────────────────────────────────── *)

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
    match Rest_http.connect_to_service () with
    | None -> "0"
    | Some sock ->
        Unix.close sock;
        "1"
  in
  let metrics_text =
    String.concat "\n" metrics ^ Printf.sprintf "latex_tokenizer_up %s\n" is_up
  in
  (Rest_http.http_ok, metrics_text)

(* ── POST /expand ──────────────────────────────────────────────────── *)

let handle_expand body path ~catalogue =
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
            let cfg = Rest_simple_expander.with_catalogue cfg catalogue in
            let expanded = Rest_simple_expander.expand_fix cfg s in
            let open Latex_parse_lib in
            let layer =
              if String.contains path '?' then
                try
                  let q =
                    String.sub path
                      (String.index path '?' + 1)
                      (String.length path - (String.index path '?' + 1))
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
                with Not_found | Invalid_argument _ -> Validators.L0
              else Validators.L0
            in
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
                        (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z')
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
                          : Latex_parse_lib.Validators_context.post_command)
                        :: acc
                      else acc
                  | _ -> acc)
                [] toks
              |> List.rev
            in
            Latex_parse_lib.Validators_context.set_post_commands cmd_spans;
            let xs, vdur, vtim =
              Validators.run_all_with_timings_for_layer expanded layer
            in
            let tuples =
              List.map
                (fun (r : Latex_parse_lib.Validators.result) ->
                  let open Latex_parse_lib.Validators in
                  let { id; severity; message; count; _ } = r in
                  (id, `String (severity_to_string severity), message, count))
                xs
            in
            let include_post =
              match Sys.getenv_opt "L0_DEBUG_L1" with
              | Some ("1" | "true" | "on") -> true
              | _ -> false
            in
            let base_json =
              json_ok ~expanded:(Some expanded) ~status:0 ~origin:"primary"
                ~n_tokens:0 ~issues_len:0 ~req_bytes:(String.length s)
                ~validators:tuples ~v_duration_ms:vdur ~v_timings:vtim
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
                               | Some c -> `String (String.make 1 c) );
                           ])
                       toks)
                in
                let cmds =
                  `List
                    (List.map
                       (fun (pc :
                              Latex_parse_lib.Validators_context.post_command) ->
                         `String pc.name)
                       cmd_spans)
                in
                let post_summary =
                  let ecmds =
                    `List
                      (List.map
                         (fun (pc :
                                Latex_parse_lib.Validators_context.post_command) ->
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
            (Rest_http.http_ok, json)
        | _ ->
            ( Rest_http.http_bad_request,
              json_error ~code:400 "Missing 'latex' field" ))
    | _ -> (Rest_http.http_bad_request, json_error ~code:400 "Invalid JSON")
  with Yojson.Safe.Util.Type_error _ | Failure _ ->
    (Rest_http.http_bad_request, json_error ~code:400 "Invalid request")

(* ── POST /tokens ──────────────────────────────────────────────────── *)

let handle_tokens body =
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
                               | Some c -> `String (String.make 1 c) );
                           ])
                       toks)
                in
                ( Rest_http.http_ok,
                  Y.to_string
                    (`Assoc
                      [ ("count", `Int (List.length toks)); ("tokens", arr) ])
                )
            | _ ->
                ( Rest_http.http_bad_request,
                  json_error ~code:400 "Missing 'latex' field" ))
        | _ -> (Rest_http.http_bad_request, json_error ~code:400 "Invalid JSON")
      with Yojson.Safe.Util.Type_error _ | Failure _ ->
        (Rest_http.http_bad_request, json_error ~code:400 "Invalid request"))
  | _ ->
      ( Rest_http.http_bad_request,
        json_error ~code:403 "token debugging disabled" )

(* ── GET /ready ────────────────────────────────────────────────────── *)

let handle_ready () =
  match Rest_http.connect_to_service () with
  | None ->
      ( Rest_http.http_service_unavailable,
        json_error ~code:503 "service not ready" )
  | Some sock ->
      Unix.close sock;
      (Rest_http.http_ok, Y.to_string @@ `Assoc [ ("ready", `Bool true) ])

(* ── GET / ─────────────────────────────────────────────────────────── *)

let handle_welcome () =
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
  (Rest_http.http_ok, welcome)
