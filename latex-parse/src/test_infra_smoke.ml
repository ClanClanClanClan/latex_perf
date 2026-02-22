(** Smoke tests for infrastructure modules: Pretouch, Gc_prep, Meminfo, Mlock.
    Merged from: test_pretouch_smoke.ml, test_gc_prep_smoke.ml,
    test_meminfo_smoke.ml, test_mlock_smoke.ml. *)

open Latex_parse_lib
open Test_helpers

(* ── Pretouch smoke tests ──────────────────────────────────────────── *)

let () =
  (* 1. pre_touch_bytes on a normal page-sized buffer *)
  run "pretouch: bytes 4096" (fun tag ->
      (try Pretouch.pre_touch_bytes (Bytes.create 4096) ~page:4096
       with exn -> expect false (tag ^ ": raised " ^ Printexc.to_string exn));
      expect true tag);

  (* 2. pre_touch_bytes on empty buffer *)
  run "pretouch: bytes empty" (fun tag ->
      (try Pretouch.pre_touch_bytes Bytes.empty ~page:4096
       with exn -> expect false (tag ^ ": raised " ^ Printexc.to_string exn));
      expect true tag);

  (* 3. pre_touch_bytes on 1-byte buffer *)
  run "pretouch: bytes 1 byte" (fun tag ->
      (try Pretouch.pre_touch_bytes (Bytes.create 1) ~page:4096
       with exn -> expect false (tag ^ ": raised " ^ Printexc.to_string exn));
      expect true tag);

  (* 4. pre_touch_bytes with small page stride *)
  run "pretouch: bytes small page" (fun tag ->
      (try Pretouch.pre_touch_bytes (Bytes.create 100_000) ~page:256
       with exn -> expect false (tag ^ ": raised " ^ Printexc.to_string exn));
      expect true tag);

  (* 5. pre_touch_ba_1 on a Bigarray *)
  run "pretouch: ba1 normal" (fun tag ->
      let ba = Bigarray.Array1.create Bigarray.float64 Bigarray.c_layout 1024 in
      (try Pretouch.pre_touch_ba_1 ba ~elem_bytes:8 ~elems:1024 ~page:4096
       with exn -> expect false (tag ^ ": raised " ^ Printexc.to_string exn));
      expect true tag);

  (* 6. pre_touch_ba_1 with elems > dim — clamped safely *)
  run "pretouch: ba1 elems clamped" (fun tag ->
      let ba = Bigarray.Array1.create Bigarray.float64 Bigarray.c_layout 100 in
      (try Pretouch.pre_touch_ba_1 ba ~elem_bytes:8 ~elems:99999 ~page:4096
       with exn -> expect false (tag ^ ": raised " ^ Printexc.to_string exn));
      expect true tag);

  (* 7. pre_touch_bytes on large buffer *)
  run "pretouch: bytes 1MB" (fun tag ->
      (try Pretouch.pre_touch_bytes (Bytes.create (1024 * 1024)) ~page:4096
       with exn -> expect false (tag ^ ": raised " ^ Printexc.to_string exn));
      expect true tag);

  (* 8. pre_touch_ba_1 with small Bigarray *)
  run "pretouch: ba1 tiny" (fun tag ->
      let ba =
        Bigarray.Array1.create Bigarray.int8_unsigned Bigarray.c_layout 1
      in
      (try Pretouch.pre_touch_ba_1 ba ~elem_bytes:1 ~elems:1 ~page:4096
       with exn -> expect false (tag ^ ": raised " ^ Printexc.to_string exn));
      expect true tag)

(* ── Gc_prep smoke tests ───────────────────────────────────────────── *)

let () =
  (* 1. words_total returns non-negative, positive after allocation *)
  run "gc-prep: words_total non-negative" (fun tag ->
      let _ = Array.make 1000 0 in
      let w = Gc_prep.words_total () in
      expect (w >= 0.0) (tag ^ Printf.sprintf ": got %.0f" w));

  (* 2. drain_major completes without hanging *)
  run "gc-prep: drain_major" (fun tag ->
      (try Gc_prep.drain_major ()
       with exn -> expect false (tag ^ ": raised " ^ Printexc.to_string exn));
      expect true tag);

  (* 3. drain_major with custom slice completes *)
  run "gc-prep: drain_major slice" (fun tag ->
      (try Gc_prep.drain_major ~slice:512 ()
       with exn -> expect false (tag ^ ": raised " ^ Printexc.to_string exn));
      expect true tag);

  (* 4. prepay completes without crashing *)
  run "gc-prep: prepay" (fun tag ->
      (try Gc_prep.prepay ()
       with exn -> expect false (tag ^ ": raised " ^ Printexc.to_string exn));
      expect true tag);

  (* 5. init_gc applies config settings *)
  run "gc-prep: init_gc settings" (fun tag ->
      Gc_prep.init_gc ();
      let ctrl = Gc.get () in
      expect
        (ctrl.Gc.space_overhead = Config.gc_space_overhead)
        (tag
        ^ Printf.sprintf ": space_overhead=%d (expected %d)"
            ctrl.Gc.space_overhead Config.gc_space_overhead));

  (* 6. words_total is non-decreasing after allocation *)
  run "gc-prep: words monotonic" (fun tag ->
      let w0 = Gc_prep.words_total () in
      let _ = Array.make 100_000 0 in
      let w1 = Gc_prep.words_total () in
      expect (w1 >= w0) (tag ^ Printf.sprintf ": w0=%.0f w1=%.0f" w0 w1));

  (* 7. drain_major is idempotent — two consecutive calls don't crash *)
  run "gc-prep: drain_major idempotent" (fun tag ->
      Gc_prep.drain_major ();
      Gc_prep.drain_major ();
      expect true tag)

(* ── Meminfo smoke tests ───────────────────────────────────────────── *)

let () =
  (* 1. rss_mb returns positive value *)
  run "meminfo: rss positive" (fun tag ->
      let rss = Meminfo.rss_mb () in
      expect (rss > 0.0) (tag ^ Printf.sprintf ": got %.2f" rss));

  (* 2. rss_mb returns sane upper bound (< 10 GB) *)
  run "meminfo: rss sane upper" (fun tag ->
      let rss = Meminfo.rss_mb () in
      expect (rss < 10_000.0) (tag ^ Printf.sprintf ": got %.2f" rss));

  (* 3. Two consecutive calls don't crash *)
  run "meminfo: repeat calls" (fun tag ->
      let r1 = Meminfo.rss_mb () in
      let r2 = Meminfo.rss_mb () in
      expect (r1 > 0.0 && r2 > 0.0) tag);

  (* 4. rss_mb after allocation is >= before *)
  run "meminfo: rss after alloc" (fun tag ->
      let before = Meminfo.rss_mb () in
      (* Allocate ~8MB and touch every page *)
      let big = Bytes.make (8 * 1024 * 1024) '\x00' in
      let _ = Bytes.get big 0 in
      let after = Meminfo.rss_mb () in
      (* RSS should not decrease (allow same due to OS rounding) *)
      expect
        (after >= before *. 0.9)
        (tag ^ Printf.sprintf ": before=%.2f after=%.2f" before after))

(* ── Mlock smoke tests ─────────────────────────────────────────────── *)

let () =
  (* 1. With L0_NO_MLOCK=1: init returns without raising *)
  run "mlock: skip via env" (fun tag ->
      Unix.putenv "L0_NO_MLOCK" "1";
      (try Mlock.init ()
       with exn -> expect false (tag ^ ": raised " ^ Printexc.to_string exn));
      expect true tag);

  (* 2. Without env var: init returns (catches privilege errors internally) *)
  run "mlock: init graceful" (fun tag ->
      (* Remove the env var if present *)
      (try Unix.putenv "L0_NO_MLOCK" "" with Not_found -> ());
      (try Mlock.init ()
       with exn -> expect false (tag ^ ": raised " ^ Printexc.to_string exn));
      expect true tag);

  (* 3. Double init is safe *)
  run "mlock: double init" (fun tag ->
      Unix.putenv "L0_NO_MLOCK" "1";
      Mlock.init ();
      Mlock.init ();
      expect true tag)

let () = finalise "infra-smoke"
