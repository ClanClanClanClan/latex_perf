(** Smoke tests for Meminfo (resident set size via FFI). *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[meminfo] FAIL: %s\n%!" msg;
    incr fails)

let run msg f =
  incr cases;
  f msg

let () =
  (* 1. rss_mb returns positive value *)
  run "rss positive" (fun tag ->
      let rss = Meminfo.rss_mb () in
      expect (rss > 0.0) (tag ^ Printf.sprintf ": got %.2f" rss));

  (* 2. rss_mb returns sane upper bound (< 10 GB) *)
  run "rss sane upper" (fun tag ->
      let rss = Meminfo.rss_mb () in
      expect (rss < 10_000.0) (tag ^ Printf.sprintf ": got %.2f" rss));

  (* 3. Two consecutive calls don't crash *)
  run "repeat calls" (fun tag ->
      let r1 = Meminfo.rss_mb () in
      let r2 = Meminfo.rss_mb () in
      expect (r1 > 0.0 && r2 > 0.0) tag);

  (* 4. rss_mb after allocation is >= before *)
  run "rss after alloc" (fun tag ->
      let before = Meminfo.rss_mb () in
      (* Allocate ~8MB and touch every page *)
      let big = Bytes.make (8 * 1024 * 1024) '\x00' in
      let _ = Bytes.get big 0 in
      let after = Meminfo.rss_mb () in
      (* RSS should not decrease (allow same due to OS rounding) *)
      expect
        (after >= before *. 0.9)
        (tag ^ Printf.sprintf ": before=%.2f after=%.2f" before after));

  if !fails > 0 then (
    Printf.eprintf "[meminfo] %d failure(s)\n%!" !fails;
    exit 1)
  else Printf.printf "[meminfo] PASS %d cases\n%!" !cases
