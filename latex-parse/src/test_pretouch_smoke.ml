(** Smoke tests for Pretouch (memory page pre-faulting). *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[pretouch] FAIL: %s\n%!" msg;
    incr fails)

let run msg f =
  incr cases;
  f msg

let () =
  (* 1. pre_touch_bytes on a normal page-sized buffer *)
  run "bytes 4096" (fun tag ->
      (try Pretouch.pre_touch_bytes (Bytes.create 4096) ~page:4096
       with exn -> expect false (tag ^ ": raised " ^ Printexc.to_string exn));
      expect true tag);

  (* 2. pre_touch_bytes on empty buffer *)
  run "bytes empty" (fun tag ->
      (try Pretouch.pre_touch_bytes Bytes.empty ~page:4096
       with exn -> expect false (tag ^ ": raised " ^ Printexc.to_string exn));
      expect true tag);

  (* 3. pre_touch_bytes on 1-byte buffer *)
  run "bytes 1 byte" (fun tag ->
      (try Pretouch.pre_touch_bytes (Bytes.create 1) ~page:4096
       with exn -> expect false (tag ^ ": raised " ^ Printexc.to_string exn));
      expect true tag);

  (* 4. pre_touch_bytes with small page stride *)
  run "bytes small page" (fun tag ->
      (try Pretouch.pre_touch_bytes (Bytes.create 100_000) ~page:256
       with exn -> expect false (tag ^ ": raised " ^ Printexc.to_string exn));
      expect true tag);

  (* 5. pre_touch_ba_1 on a Bigarray *)
  run "ba1 normal" (fun tag ->
      let ba = Bigarray.Array1.create Bigarray.float64 Bigarray.c_layout 1024 in
      (try Pretouch.pre_touch_ba_1 ba ~elem_bytes:8 ~elems:1024 ~page:4096
       with exn -> expect false (tag ^ ": raised " ^ Printexc.to_string exn));
      expect true tag);

  (* 6. pre_touch_ba_1 with elems > dim — clamped safely *)
  run "ba1 elems clamped" (fun tag ->
      let ba = Bigarray.Array1.create Bigarray.float64 Bigarray.c_layout 100 in
      (try Pretouch.pre_touch_ba_1 ba ~elem_bytes:8 ~elems:99999 ~page:4096
       with exn -> expect false (tag ^ ": raised " ^ Printexc.to_string exn));
      expect true tag);

  (* 7. pre_touch_bytes on large buffer *)
  run "bytes 1MB" (fun tag ->
      (try Pretouch.pre_touch_bytes (Bytes.create (1024 * 1024)) ~page:4096
       with exn -> expect false (tag ^ ": raised " ^ Printexc.to_string exn));
      expect true tag);

  (* 8. pre_touch_ba_1 with small Bigarray *)
  run "ba1 tiny" (fun tag ->
      let ba =
        Bigarray.Array1.create Bigarray.int8_unsigned Bigarray.c_layout 1
      in
      (try Pretouch.pre_touch_ba_1 ba ~elem_bytes:1 ~elems:1 ~page:4096
       with exn -> expect false (tag ^ ": raised " ^ Printexc.to_string exn));
      expect true tag);

  if !fails > 0 then (
    Printf.eprintf "[pretouch] %d failure(s)\n%!" !fails;
    exit 1)
  else Printf.printf "[pretouch] PASS %d cases\n%!" !cases
