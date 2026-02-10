(** Smoke tests for Gc_prep (GC tuning and major-heap drainage). *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[gc-prep] FAIL: %s\n%!" msg;
    incr fails)

let run msg f =
  incr cases;
  f msg

let () =
  (* 1. words_total returns non-negative, positive after allocation *)
  run "words_total non-negative" (fun tag ->
      let _ = Array.make 1000 0 in
      let w = Gc_prep.words_total () in
      expect (w >= 0.0) (tag ^ Printf.sprintf ": got %.0f" w));

  (* 2. drain_major completes without hanging *)
  run "drain_major" (fun tag ->
      (try Gc_prep.drain_major ()
       with exn -> expect false (tag ^ ": raised " ^ Printexc.to_string exn));
      expect true tag);

  (* 3. drain_major with custom slice completes *)
  run "drain_major slice" (fun tag ->
      (try Gc_prep.drain_major ~slice:512 ()
       with exn -> expect false (tag ^ ": raised " ^ Printexc.to_string exn));
      expect true tag);

  (* 4. prepay completes without crashing *)
  run "prepay" (fun tag ->
      (try Gc_prep.prepay ()
       with exn -> expect false (tag ^ ": raised " ^ Printexc.to_string exn));
      expect true tag);

  (* 5. init_gc applies config settings *)
  run "init_gc settings" (fun tag ->
      Gc_prep.init_gc ();
      let ctrl = Gc.get () in
      expect
        (ctrl.Gc.space_overhead = Config.gc_space_overhead)
        (tag
        ^ Printf.sprintf ": space_overhead=%d (expected %d)"
            ctrl.Gc.space_overhead Config.gc_space_overhead));

  (* 6. words_total is non-decreasing after allocation *)
  run "words monotonic" (fun tag ->
      let w0 = Gc_prep.words_total () in
      let _ = Array.make 100_000 0 in
      let w1 = Gc_prep.words_total () in
      expect (w1 >= w0) (tag ^ Printf.sprintf ": w0=%.0f w1=%.0f" w0 w1));

  (* 7. drain_major is idempotent — two consecutive calls don't crash *)
  run "drain_major idempotent" (fun tag ->
      Gc_prep.drain_major ();
      Gc_prep.drain_major ();
      expect true tag);

  if !fails > 0 then (
    Printf.eprintf "[gc-prep] %d failure(s)\n%!" !fails;
    exit 1)
  else Printf.printf "[gc-prep] PASS %d cases\n%!" !cases
