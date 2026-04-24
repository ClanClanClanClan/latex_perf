(** E2E fix pipeline test (v26.2.1 PR #5).

    For each exemplar rule (STRUCT-001, TYPO-002, TYPO-003), walk the pipeline:
    source → `Validators.run_all` → collect fixes → `Cst_edit.apply_all` →
    re-run validators and assert the same rule no longer fires on the output.

    This is the semantic contract `--apply-fixes` promises: applying the fix set
    removes the problem.

    Inputs are read from `corpora/fixtures/v26_2_1/` — one curated file per
    case. See `corpora/fixtures/v26_2_1/README.md`. *)

open Test_helpers

let repo_root = Sys.getcwd ()

let fixture_path name =
  let candidates =
    [
      Filename.concat repo_root ("corpora/fixtures/v26_2_1/" ^ name);
      Filename.concat repo_root ("../../corpora/fixtures/v26_2_1/" ^ name);
      Filename.concat repo_root ("../../../corpora/fixtures/v26_2_1/" ^ name);
    ]
  in
  match List.find_opt Sys.file_exists candidates with
  | Some p -> p
  | None ->
      Printf.eprintf "[fix-integration] FATAL: fixture %s not found (cwd=%s)\n"
        name repo_root;
      exit 1

let read_fixture name =
  let ic = open_in_bin (fixture_path name) in
  let src = really_input_string ic (in_channel_length ic) in
  close_in ic;
  src

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
     env setup needed. *)
  run "E2E STRUCT-001: apply fix removes the problem" (fun tag ->
      let src = read_fixture "struct_001_missing_docclass.tex" in
      let edits, out = pipeline "STRUCT-001" src in
      expect
        (List.length edits = 1
        && does_not_fire "STRUCT-001" out
        && String.length out > String.length src)
        (tag ^ ": fired once, applied, no longer fires"));

  (* Clean source should not trigger any fix-producing rule. *)
  run "E2E clean source: no edits, applying is a no-op" (fun tag ->
      let src = read_fixture "clean_docclass.tex" in
      let edits = fix_edits "STRUCT-001" src in
      let out = apply_all src edits in
      expect
        (List.length edits = 0 && out = src)
        (tag ^ ": no fix, source unchanged"));

  (* TYPO rules live in the pilot set. *)
  Unix.putenv "L0_VALIDATORS" "pilot";

  run "E2E TYPO-002: apply fix removes --" (fun tag ->
      let src = read_fixture "typo_002_multi_dashes.tex" in
      let edits, out = pipeline "TYPO-002" src in
      expect
        (List.length edits = 2
        && does_not_fire "TYPO-002" out
        && out = "Alpha – beta – gamma.\n")
        (tag ^ ": two edits applied, rule no longer fires"));

  run "E2E TYPO-003: apply fix removes ---" (fun tag ->
      let src = read_fixture "typo_003_multi_dashes.tex" in
      let edits, out = pipeline "TYPO-003" src in
      expect
        (List.length edits = 2
        && does_not_fire "TYPO-003" out
        && out = "Alpha — beta — gamma.\n")
        (tag ^ ": two edits applied, rule no longer fires"));

  (* Collect-all pipeline: simulates what `--apply-fixes` does in the CLI.
     STRUCT-001 + TYPO-003 cannot fire together (pilot gate is mutually
     exclusive — validators.ml:212), so we exercise the multi-match TYPO-002
     case instead. *)
  run "E2E collect-all: TYPO-002 multi-match, one pass" (fun tag ->
      let src = read_fixture "typo_002_collect_all.tex" in
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
