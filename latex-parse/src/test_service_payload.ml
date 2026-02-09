(** Unit tests for Service_payload binary wire format parser. *)

open Latex_parse_lib

let fails = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[svc-payload] FAIL: %s\n%!" msg;
    incr fails)

let cases = ref 0

let run msg f =
  incr cases;
  f msg

(* Helper: build a 13-byte payload with known fields *)
let mk_payload ~status ~n_tokens ~issues_len ~origin_byte =
  let b = Bytes.make 13 '\x00' in
  let put32 off v =
    Bytes.set b off (Char.chr ((v lsr 24) land 0xFF));
    Bytes.set b (off + 1) (Char.chr ((v lsr 16) land 0xFF));
    Bytes.set b (off + 2) (Char.chr ((v lsr 8) land 0xFF));
    Bytes.set b (off + 3) (Char.chr (v land 0xFF))
  in
  put32 0 status;
  put32 4 n_tokens;
  put32 8 issues_len;
  Bytes.set b 12 (Char.chr origin_byte);
  b

let () =
  (* --- Valid payloads --- *)
  run "parse Primary" (fun tag ->
      let b =
        mk_payload ~status:200 ~n_tokens:1000 ~issues_len:5 ~origin_byte:1
      in
      match Service_payload.parse_payload b with
      | Ok t ->
          expect (t.status = 200) (tag ^ ": status");
          expect (t.n_tokens = 1000) (tag ^ ": n_tokens");
          expect (t.issues_len = 5) (tag ^ ": issues_len");
          expect (t.origin = Primary) (tag ^ ": origin")
      | Error e -> expect false (tag ^ ": unexpected Error " ^ e));

  run "parse Hedge" (fun tag ->
      let b = mk_payload ~status:0 ~n_tokens:0 ~issues_len:0 ~origin_byte:2 in
      match Service_payload.parse_payload b with
      | Ok t -> expect (t.origin = Hedge) (tag ^ ": origin")
      | Error e -> expect false (tag ^ ": " ^ e));

  run "parse Unknown (0xFF)" (fun tag ->
      let b =
        mk_payload ~status:0 ~n_tokens:0 ~issues_len:0 ~origin_byte:0xFF
      in
      match Service_payload.parse_payload b with
      | Ok t -> expect (t.origin = Unknown) (tag ^ ": origin")
      | Error e -> expect false (tag ^ ": " ^ e));

  run "parse Unknown (0x00)" (fun tag ->
      let b = mk_payload ~status:0 ~n_tokens:0 ~issues_len:0 ~origin_byte:0 in
      match Service_payload.parse_payload b with
      | Ok t -> expect (t.origin = Unknown) (tag ^ ": origin")
      | Error e -> expect false (tag ^ ": " ^ e));

  run "all-zero 13 bytes" (fun tag ->
      let b = Bytes.make 13 '\x00' in
      match Service_payload.parse_payload b with
      | Ok t ->
          expect (t.status = 0) (tag ^ ": status");
          expect (t.n_tokens = 0) (tag ^ ": n_tokens");
          expect (t.issues_len = 0) (tag ^ ": issues_len");
          expect (t.origin = Unknown) (tag ^ ": origin")
      | Error _ -> expect false (tag ^ ": should parse"));

  run "big-endian 0x01020304 = 16909060" (fun tag ->
      let b =
        mk_payload ~status:16909060 ~n_tokens:0 ~issues_len:0 ~origin_byte:1
      in
      match Service_payload.parse_payload b with
      | Ok t -> expect (t.status = 16909060) (tag ^ ": be32 decode")
      | Error e -> expect false (tag ^ ": " ^ e));

  (* --- Error cases --- *)
  run "12-byte payload -> Error" (fun tag ->
      match Service_payload.parse_payload (Bytes.make 12 '\x00') with
      | Error msg -> expect (String.length msg > 0) (tag ^ ": msg non-empty")
      | Ok _ -> expect false (tag ^ ": should fail"));

  run "14-byte payload -> Error" (fun tag ->
      match Service_payload.parse_payload (Bytes.make 14 '\x00') with
      | Error _ -> ()
      | Ok _ -> expect false (tag ^ ": should fail"));

  run "empty payload -> Error" (fun tag ->
      match Service_payload.parse_payload Bytes.empty with
      | Error _ -> ()
      | Ok _ -> expect false (tag ^ ": should fail"));

  run "1-byte payload -> Error" (fun tag ->
      match Service_payload.parse_payload (Bytes.make 1 '\x00') with
      | Error _ -> ()
      | Ok _ -> expect false (tag ^ ": should fail"));

  if !fails > 0 then (
    Printf.eprintf "[svc-payload] %d failure(s)\n%!" !fails;
    exit 1)
  else Printf.printf "[svc-payload] PASS %d cases\n%!" !cases
