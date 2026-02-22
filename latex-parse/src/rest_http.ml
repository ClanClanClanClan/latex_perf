(* rest_http.ml — HTTP codec, binary wire helpers, and SIMD service client.

   Pure transport layer: no business logic, no Yojson, no validators. *)

open Printf

(* ── HTTP constants ────────────────────────────────────────────────── *)

let http_ok = "200 OK"
let http_bad_request = "400 Bad Request"
let _http_internal_error = "500 Internal Server Error"
let http_service_unavailable = "503 Service Unavailable"
let http_request_too_large = "413 Request Entity Too Large"

let cors_headers =
  [
    "Access-Control-Allow-Origin: *";
    "Access-Control-Allow-Methods: GET, POST, OPTIONS";
    "Access-Control-Allow-Headers: Content-Type";
  ]

let max_request_size = 10_000_000 (* 10 MB *)
let socket_path = "/tmp/l0_lex_svc.sock"

(* ── HTTP send / parse ─────────────────────────────────────────────── *)

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

let parse_http_request request =
  let lines = String.split_on_char '\n' request in
  match lines with
  | [] -> (None, None, "")
  | first_line :: rest ->
      let parts = String.split_on_char ' ' first_line in
      let method_opt = match parts with meth :: _ -> Some meth | _ -> None in
      let path_opt =
        match parts with _ :: path :: _ -> Some path | _ -> None
      in
      let rec find_body lines in_header acc_header =
        match lines with
        | [] -> ("", acc_header)
        | line :: rest ->
            let line = String.trim line in
            if in_header && line = "" then
              (String.concat "\n" rest, List.rev acc_header)
            else if in_header then find_body rest true (line :: acc_header)
            else find_body rest false acc_header
      in
      let body, _headers = find_body rest true [] in
      (method_opt, path_opt, String.trim body)

(* ── Binary encoding helpers ───────────────────────────────────────── *)

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

let read_exact fd buf ofs len =
  Latex_parse_lib.Net_io.read_exact_exn fd buf ofs len

let write_all fd buf ofs len =
  Latex_parse_lib.Net_io.write_all_exn fd buf ofs len

(* ── SIMD service client ───────────────────────────────────────────── *)

let connect_to_service () =
  try
    let sock = Unix.socket Unix.PF_UNIX Unix.SOCK_STREAM 0 in
    Unix.connect sock (Unix.ADDR_UNIX socket_path);
    Some sock
  with Unix.Unix_error _ -> None

let req_counter = ref 0L

let next_req_id () =
  let id = !req_counter in
  req_counter := Int64.succ id;
  id

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
