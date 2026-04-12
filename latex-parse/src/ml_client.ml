(* ══════════════════════════════════════════════════════════════════════
   Ml_client — HTTP client for the byte_classifier_server sidecar

   Sends batch requests to the Python ML server on port 8091. Falls back to
   empty results if unavailable. Availability cached 30s.
   ══════════════════════════════════════════════════════════════════════ *)

type classify_request = {
  bytes_b64 : string;
  rule_id : string;
  parser_features : float list;
}

type classify_response = { rule_id : string; p_violation : float }

(* ���─ Availability cache ────────────────────────────────────────────── *)

let _available = ref false
let _last_check = ref 0.0
let _cache_ttl = 30.0

let check_available ?(host = "127.0.0.1") ?(port = 8091) () : bool =
  try
    let sock = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
    Fun.protect
      ~finally:(fun () -> Unix.close sock)
      (fun () ->
        Unix.setsockopt_float sock Unix.SO_RCVTIMEO 0.05;
        Unix.setsockopt_float sock Unix.SO_SNDTIMEO 0.05;
        let addr = Unix.ADDR_INET (Unix.inet_addr_of_string host, port) in
        Unix.connect sock addr;
        true)
  with _ -> false

let is_available () : bool =
  let now = Unix.gettimeofday () in
  if now -. !_last_check < _cache_ttl then !_available
  else
    let avail = check_available () in
    _available := avail;
    _last_check := now;
    avail

(* ── Batch classification ──────────────────────────────────────────── *)

let classify_batch ?(host = "127.0.0.1") ?(port = 8091)
    (requests : classify_request list) : classify_response list =
  if requests = [] then []
  else if not (is_available ()) then []
  else
    try
      let sock = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
      Fun.protect
        ~finally:(fun () -> Unix.close sock)
        (fun () ->
          Unix.setsockopt_float sock Unix.SO_RCVTIMEO 0.2;
          Unix.setsockopt_float sock Unix.SO_SNDTIMEO 0.05;
          let addr = Unix.ADDR_INET (Unix.inet_addr_of_string host, port) in
          Unix.connect sock addr;
          (* Build JSON request *)
          let spans =
            List.map
              (fun r ->
                `Assoc
                  [
                    ("bytes", `String r.bytes_b64);
                    ("rule_id", `String r.rule_id);
                    ( "parser_features",
                      `List (List.map (fun f -> `Float f) r.parser_features) );
                  ])
              requests
          in
          let body =
            Yojson.Safe.to_string (`Assoc [ ("spans", `List spans) ])
          in
          let req =
            Printf.sprintf
              "POST /classify HTTP/1.1\r\n\
               Host: %s:%d\r\n\
               Content-Type: application/json\r\n\
               Content-Length: %d\r\n\
               Connection: close\r\n\
               \r\n\
               %s"
              host port (String.length body) body
          in
          let _ = Unix.write_substring sock req 0 (String.length req) in
          (* Read response *)
          let buf = Buffer.create 4096 in
          let chunk = Bytes.create 4096 in
          let rec read_loop () =
            let n = Unix.read sock chunk 0 4096 in
            if n > 0 then (
              Buffer.add_subbytes buf chunk 0 n;
              read_loop ())
          in
          (try read_loop () with _ -> ());
          let resp = Buffer.contents buf in
          (* Find JSON body after \r\n\r\n *)
          match String.split_on_char '{' resp with
          | _ :: rest ->
              let json_str = "{" ^ String.concat "{" rest in
              let json = Yojson.Safe.from_string json_str in
              let open Yojson.Safe.Util in
              let results = json |> member "results" |> to_list in
              List.map
                (fun r ->
                  {
                    rule_id = r |> member "rule_id" |> to_string;
                    p_violation = r |> member "p_violation" |> to_float;
                  })
                results
          | [] -> [])
    with _ -> []
