(** Tests for PR #239 (memo §6): E2 dependency-boundary-aware repair.

    Complements the abstract Coq theorems in proofs/RepairMonotonicity.v with
    concrete OCaml fixtures. *)

open Latex_parse_lib
open Test_helpers

let mk_loc offset = { Parser_l2.line = 0; col = 0; offset }
let err msg offset = (msg, mk_loc offset)

let () =
  (* 1. Classic is_repaired: strict subset fewer errors. *)
  run "is_repaired strict subset" (fun tag ->
      let old_errs = [ err "A" 10; err "B" 20; err "C" 30 ] in
      let new_errs = [ err "A" 10; err "B" 20 ] in
      expect
        (Error_recovery.is_repaired ~old_errors:old_errs ~new_errors:new_errs)
        (tag ^ ": fewer errors should be repaired"));

  (* 2. is_repaired rejects introducing a new error. *)
  run "is_repaired rejects new error" (fun tag ->
      let old_errs = [ err "A" 10; err "B" 20 ] in
      let new_errs = [ err "A" 10; err "NEW" 25 ] in
      expect
        (not
           (Error_recovery.is_repaired ~old_errors:old_errs ~new_errors:new_errs))
        (tag ^ ": introduced error should not count as repaired"));

  (* 3. is_repaired_with_deps: empty deps reduces to is_repaired. *)
  run "is_repaired_with_deps with empty deps" (fun tag ->
      let old_errs = [ err "A" 10; err "B" 20 ] in
      let new_errs = [ err "A" 10 ] in
      expect
        (Error_recovery.is_repaired_with_deps ~old_errors:old_errs
           ~new_errors:new_errs ~deps:[])
        (tag ^ ": empty deps ⇒ is_repaired_with_deps = is_repaired"));

  (* 4. is_repaired_with_deps: fails when remaining error sits inside a dep
     boundary. *)
  run "is_repaired_with_deps rejects boundary overlap" (fun tag ->
      let old_errs = [ err "A" 10; err "B" 20; err "C" 30 ] in
      let new_errs = [ err "B" 20 ] in
      let deps =
        [ { Error_recovery.region = (15, 25); reason = "label-ref edge" } ]
      in
      expect
        (not
           (Error_recovery.is_repaired_with_deps ~old_errors:old_errs
              ~new_errors:new_errs ~deps))
        (tag ^ ": remaining error at 20 overlaps boundary [15, 25)"));

  (* 5. is_repaired_with_deps: passes when remaining errors are outside all
     boundaries. *)
  run "is_repaired_with_deps passes when disjoint" (fun tag ->
      let old_errs = [ err "A" 10; err "B" 20; err "C" 30 ] in
      let new_errs = [ err "A" 10; err "C" 30 ] in
      let deps =
        [ { Error_recovery.region = (15, 25); reason = "label-ref edge" } ]
      in
      expect
        (Error_recovery.is_repaired_with_deps ~old_errors:old_errs
           ~new_errors:new_errs ~deps)
        (tag ^ ": remaining errors outside boundary"));

  (* 6. Multiple boundaries: every remaining error must be disjoint from every
     boundary. *)
  run "multiple boundaries enforced" (fun tag ->
      let old_errs = [ err "A" 5; err "B" 50 ] in
      let new_errs = [ err "A" 5 ] in
      let deps =
        [
          { Error_recovery.region = (0, 10); reason = "b1" };
          { Error_recovery.region = (40, 60); reason = "b2" };
        ]
      in
      (* Remaining error at 5 is INSIDE boundary [0, 10) → fails. *)
      expect
        (not
           (Error_recovery.is_repaired_with_deps ~old_errors:old_errs
              ~new_errors:new_errs ~deps))
        (tag ^ ": remaining error inside first boundary"));

  finalise "repair_monotonic"
