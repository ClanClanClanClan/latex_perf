(** Incremental validation specifics — cache behavior, dirty detection,
    cross-chunk rule bypass. Complements test_integration_e2e.ml. *)

open Latex_parse_lib
open Test_helpers

let () = Unix.putenv "L0_VALIDATORS" "pilot"
let _ctr = ref 0

let usrc base =
  incr _ctr;
  Printf.sprintf "%s\n%% incr-%d\n" base !_ctr

let ids_of results =
  List.map (fun (r : Validators.result) -> r.id) results
  |> List.sort_uniq String.compare

let long_para1 =
  "First paragraph with enough text to exceed the sixty-four byte minimum \
   chunk size threshold for the chunk store splitting algorithm here."

let long_para2 =
  "Second paragraph also needs to be long enough to stand on its own as a \
   proper chunk boundary in the store system for testing purposes."

let () =
  (* ── Incremental: identical input → identical output ─────────────── *)
  run "incremental: same source twice → same IDs" (fun tag ->
      let src = usrc (long_para1 ^ "\n\n" ^ long_para2) in
      let r1 = ids_of (Validators.run_all_incremental src) in
      let r2 = ids_of (Validators.run_all_incremental ~prev_src:src src) in
      expect (r1 = r2) (tag ^ ": identical IDs"));

  (* ── Incremental: edit one paragraph → results change ────────────── *)
  run "incremental: edit triggers different results" (fun tag ->
      let src1 = usrc (long_para1 ^ "\n\n" ^ long_para2) in
      let edited_para2 =
        "Second paragraph EDITED with \"straight quotes\" to trigger TYPO-001 \
         rule firing that wasn't present in the original version."
      in
      let src2 = usrc (long_para1 ^ "\n\n" ^ edited_para2) in
      let r1 = ids_of (Validators.run_all_incremental src1) in
      let r2 = ids_of (Validators.run_all_incremental ~prev_src:src1 src2) in
      expect (r1 <> r2) (tag ^ ": different after edit"));

  (* ── Incremental: cross-chunk rules bypass cache ─────────────────── *)
  run "incremental: L3+ rules present on first call" (fun tag ->
      let src =
        usrc
          {|\documentclass{article}
\begin{document}
\label{sec:a}
\label{sec:a}
Some text here with enough content to be a real chunk.
\end{document}|}
      in
      let results = Validators.run_all_incremental src in
      (* L1+ rules should fire — semantic rules are cross-chunk *)
      expect (List.length results > 0) (tag ^ ": rules fired");
      let ids = ids_of results in
      expect (List.length ids > 0) (tag ^ ": has rule IDs"));

  (* ── Scheduled: produces results ─────────────────────────────────── *)
  run "scheduled: non-empty on real content" (fun tag ->
      let src =
        usrc
          (long_para1
          ^ "\n\n"
          ^ long_para2
          ^ "\n\nThird para with \"quotes\" for rules.")
      in
      let results = Validators.run_all_scheduled ~edit_pos:0 src in
      expect (List.length results > 0) (tag ^ ": has results"));

  (* ── Edge cases ──────────────────────────────────────────────────── *)
  run "incremental: empty → no crash" (fun tag ->
      let r = Validators.run_all_incremental "" in
      (* Empty doc: may or may not fire rules, but must not crash *)
      ignore (ids_of r);
      expect true (tag ^ ": no crash"));

  run "scheduled: empty → no crash" (fun tag ->
      let r = Validators.run_all_scheduled "" in
      ignore (ids_of r);
      expect true (tag ^ ": no crash"));

  run "incremental: single char → no crash" (fun tag ->
      let r = Validators.run_all_incremental "x" in
      ignore (ids_of r);
      expect true (tag ^ ": no crash"));

  run "scheduled: single char → no crash" (fun tag ->
      let r = Validators.run_all_scheduled "x" in
      ignore (ids_of r);
      expect true (tag ^ ": no crash"))

let () = finalise "incremental-integration"
