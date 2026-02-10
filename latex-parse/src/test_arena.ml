(** Unit tests for Arena double-buffered token storage. *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[arena] FAIL: %s\n%!" msg;
    incr fails)

let run msg f =
  incr cases;
  f msg

let () =
  (* 1. create returns a valid arena *)
  run "create" (fun tag ->
      let a = Arena.create ~cap:128 in
      let buf = Arena.current a in
      expect (buf.Arena.next_ix = 0) tag);

  (* 2. Buffer arrays have correct capacity *)
  run "capacity" (fun tag ->
      let a = Arena.create ~cap:256 in
      let buf = Arena.current a in
      expect (Bigarray.Array1.dim buf.Arena.kinds = 256) (tag ^ ": kinds");
      expect (Bigarray.Array1.dim buf.Arena.offs = 256) (tag ^ ": offs");
      expect (Bigarray.Array1.dim buf.Arena.codes = 256) (tag ^ ": codes");
      expect (Bigarray.Array1.dim buf.Arena.issues = 256) (tag ^ ": issues");
      expect (Bigarray.Array1.dim buf.Arena.lines = 256) (tag ^ ": lines");
      expect (Bigarray.Array1.dim buf.Arena.cols = 256) (tag ^ ": cols"));

  (* 3. swap toggles buffers *)
  run "swap toggles" (fun tag ->
      let a = Arena.create ~cap:64 in
      let b1 = Arena.current a in
      Arena.swap a;
      let b2 = Arena.current a in
      expect (b1 != b2) (tag ^ ": different after swap");
      Arena.swap a;
      let b3 = Arena.current a in
      expect (b1 == b3) (tag ^ ": same after double swap"));

  (* 4. swap resets next_ix *)
  run "swap resets next_ix" (fun tag ->
      let a = Arena.create ~cap:64 in
      let buf = Arena.current a in
      buf.Arena.next_ix <- 42;
      Arena.swap a;
      let buf2 = Arena.current a in
      expect (buf2.Arena.next_ix = 0) (tag ^ ": reset to 0"));

  (* 5. Writing to one buffer doesn't affect the other *)
  run "buffer isolation" (fun tag ->
      let a = Arena.create ~cap:64 in
      let buf_a = Arena.current a in
      Bigarray.Array1.set buf_a.Arena.kinds 0 99l;
      Arena.swap a;
      let buf_b = Arena.current a in
      let v = Bigarray.Array1.get buf_b.Arena.kinds 0 in
      expect (v <> 99l) (tag ^ Printf.sprintf ": got %ld" v));

  (* 6. next_ix is mutable per-buffer *)
  run "next_ix per buffer" (fun tag ->
      let a = Arena.create ~cap:32 in
      let buf_a = Arena.current a in
      buf_a.Arena.next_ix <- 10;
      Arena.swap a;
      let buf_b = Arena.current a in
      expect (buf_b.Arena.next_ix = 0) (tag ^ ": b starts at 0");
      Arena.swap a;
      let buf_a2 = Arena.current a in
      (* After swap back, next_ix was reset by the swap call *)
      expect (buf_a2.Arena.next_ix = 0) (tag ^ ": a reset by swap"));

  (* 7. Small capacity works *)
  run "cap 1" (fun tag ->
      let a = Arena.create ~cap:1 in
      let buf = Arena.current a in
      expect (Bigarray.Array1.dim buf.Arena.kinds = 1) tag);

  if !fails > 0 then (
    Printf.eprintf "[arena] %d failure(s)\n%!" !fails;
    exit 1)
  else Printf.printf "[arena] PASS %d cases\n%!" !cases
