(** E2E fix pipeline test (v26.2.1 PR #5).

    For each exemplar rule (STRUCT-001, TYPO-002, TYPO-003), walk the pipeline:
    source → `Validators.run_all` → collect fixes → `Cst_edit.apply_all` →
    re-run validators and assert the same rule no longer fires on the output.

    This is the semantic contract `--apply-fixes` promises: applying the fix set
    removes the problem. *)

open Test_helpers

let apply_all s edits =
  match Latex_parse_lib.Cst_edit.apply_all s edits with
  | Ok out -> out
  | Error _ -> failwith "overlapping fix edits"

let pipeline rule_id src =
  let edits = fix_edits rule_id src in
  let out = apply_all src edits in
  (edits, out)

let () =
  (* STRUCT-001: insert \documentclass at 0. After applying, the rule should not
     re-fire. STRUCT-001 gating uses L0_VALIDATORS default (non-pilot), so no
     env setup needed here. *)
  run "E2E STRUCT-001: apply fix removes the problem" (fun tag ->
      let src = "Body without a docclass line.\n" in
      let edits, out = pipeline "STRUCT-001" src in
      expect
        (List.length edits = 1
        && does_not_fire "STRUCT-001" out
        && String.length out > String.length src)
        (tag ^ ": fired once, applied, no longer fires"));

  (* TYPO rules live in the pilot set. *)
  Unix.putenv "L0_VALIDATORS" "pilot";

  run "E2E TYPO-002: apply fix removes --" (fun tag ->
      let src = "Alpha -- beta -- gamma.\n" in
      let edits, out = pipeline "TYPO-002" src in
      expect
        (List.length edits = 2
        && does_not_fire "TYPO-002" out
        && out = "Alpha – beta – gamma.\n")
        (tag ^ ": two edits applied, rule no longer fires"));

  run "E2E TYPO-003: apply fix removes ---" (fun tag ->
      let src = "Alpha --- beta --- gamma.\n" in
      let edits, out = pipeline "TYPO-003" src in
      expect
        (List.length edits = 2
        && does_not_fire "TYPO-003" out
        && out = "Alpha — beta — gamma.\n")
        (tag ^ ": two edits applied, rule no longer fires"));

  (* Combined TYPO-002 + TYPO-002 elsewhere in the same source. The CLI's
     `--apply-fixes` mode flattens multi-result fix lists. Here we verify that
     [Cst_edit.apply_all] over the collected set yields a clean output where the
     rule no longer fires.

     Note: STRUCT-001 + TYPO-003 cannot fire simultaneously because STRUCT-001
     is in `rules_basic` (L0_VALIDATORS unset) while TYPO-003 is in
     `rules_pilot` (L0_VALIDATORS=pilot). The env gate is mutually exclusive by
     design — see validators.ml:212. *)
  run "E2E collect-all: TYPO-002 multi-match, one pass" (fun tag ->
      let src = "Alpha -- beta. Gamma -- delta.\n" in
      let results = Latex_parse_lib.Validators.run_all src in
      let all_edits =
        List.concat_map
          (fun (r : Latex_parse_lib.Validators.result) ->
            match r.fix with Some edits -> edits | None -> [])
          results
      in
      let out = apply_all src all_edits in
      expect
        (does_not_fire "TYPO-002" out && out = "Alpha – beta. Gamma – delta.\n")
        (tag ^ ": collected fixes apply, rule no longer fires"));

  finalise "fix-integration"
