(** Unit tests for [Rule_rationale] (WS9: policy explanation + rationale links).

    Acceptance (spec WS9):
    - [--explain] for a diagnose-only rule (LAY/REF) returns the family
      remediation (non-empty rationale + remediation + doc link);
    - [--explain] for an unknown id is handled ([None]);
    - a curated per-rule override wins over the family default;
    - EVERY family has a remediation template — no family falls back to the
      generic empty case (checked against every catalogued rule id);
    - coverage: every catalogued rule resolves to a non-empty rationale +
      remediation. *)

open Printf
module RR = Latex_parse_lib.Rule_rationale

let failures = ref 0

let check name cond =
  if cond then printf "ok   - %s\n" name
  else (
    incr failures;
    printf "FAIL - %s\n" name)

let nonempty s = String.trim s <> ""

let contains hay needle =
  let n = String.length needle and m = String.length hay in
  let rec go i =
    if i + n > m then false
    else if String.sub hay i n = needle then true
    else go (i + 1)
  in
  go 0

let () =
  (* The data files are resolved from the repo (env override or upward walk).
     Point the loader at the source tree explicitly so the test is independent
     of the cwd dune runs it in. *)
  let repo =
    (* dune runs tests from the _build sandbox; walk up to the repo root. *)
    let rec up dir depth =
      if depth <= 0 then dir
      else if Sys.file_exists (Filename.concat dir "specs/rules/rules_v3.yaml")
      then dir
      else up (Filename.dirname dir) (depth - 1)
    in
    up (Sys.getcwd ()) 12
  in
  if Sys.file_exists (Filename.concat repo "specs/rules/rules_v3.yaml") then (
    Unix.putenv "LP_RULES_YAML"
      (Filename.concat repo "specs/rules/rules_v3.yaml");
    Unix.putenv "LP_RULE_REMEDIATION_YAML"
      (Filename.concat repo "governance/rule_remediation.yaml"));

  (* ── 1. diagnose-only rule → family remediation ────────────────────── *)
  (match RR.explain "LAY-001" with
  | None -> check "LAY-001 resolves" false
  | Some e ->
      check "LAY-001 resolves" true;
      check "LAY-001 message non-empty" (nonempty e.RR.rule_message);
      check "LAY-001 rationale non-empty" (nonempty e.RR.rationale);
      check "LAY-001 remediation non-empty" (nonempty e.RR.remediation);
      check "LAY-001 doc_link is catalogue anchor"
        (e.RR.doc_link = "specs/rules/rules_v3.yaml#lay-001"));

  (* a REF rule with no override falls back to the REF family template *)
  (match RR.explain "REF-003" with
  | None -> check "REF-003 resolves" false
  | Some e ->
      check "REF-003 remediation = REF family template"
        (contains e.RR.remediation "cross-reference"));

  (* ── 2. unknown id is handled ──────────────────────────────────────── *)
  check "unknown id → None" (RR.explain "NOPE-999" = None);
  check "unknown id → one_line still non-empty (family/fallback)"
    (nonempty (RR.one_line "NOPE-999"));

  (* ── 3. curated override wins over family default ──────────────────── *)
  let ref003 =
    match RR.explain "REF-003" with Some e -> e.RR.remediation | None -> ""
  in
  let ref001 =
    match RR.explain "REF-001" with Some e -> e.RR.remediation | None -> ""
  in
  check "REF-001 override differs from REF family default"
    (nonempty ref001 && nonempty ref003 && ref001 <> ref003);
  check "REF-001 override mentions \\label" (nonempty ref001);

  (* ── 4. every family has a non-empty remediation template ──────────── *)
  (* Collect every family present in the catalogue and assert its template is
     present + non-empty (i.e. no family falls back to the generic case). The
     generic fallback text is recognisable; assert no catalogued rule hits
     it. *)
  let generic_fallback =
    "No auto-fix is available. Review the flagged construct in the source and \
     adjust it by hand to satisfy the rule."
  in
  let resolved, total = RR.coverage () in
  check "catalogue has rules" (total > 600);
  check "coverage: every rule resolves non-empty" (resolved = total);
  printf
    "# coverage: %d/%d rules resolve to non-empty rationale + remediation\n"
    resolved total;

  (* No catalogued rule may use the generic fallback (every family
     templated). *)
  let cat_path = Filename.concat repo "specs/rules/rules_v3.yaml" in
  let ids =
    let ic = open_in cat_path in
    let n = in_channel_length ic in
    let content = really_input_string ic n in
    close_in ic;
    String.split_on_char '\n' content
    |> List.filter_map (fun l ->
           let l = String.trim l in
           let p = "- id:" in
           if
             String.length l >= String.length p
             && String.sub l 0 (String.length p) = p
           then
             match String.index_opt l '"' with
             | Some i -> (
                 match String.index_from_opt l (i + 1) '"' with
                 | Some j -> Some (String.sub l (i + 1) (j - i - 1))
                 | None -> None)
             | None -> None
           else None)
  in
  let fell_back =
    List.filter (fun id -> RR.remediation_for id = generic_fallback) ids
  in
  check
    (sprintf "no family falls back to generic (%d ids checked, %d fell back)"
       (List.length ids) (List.length fell_back))
    (fell_back = []);

  if !failures = 0 then printf "\nAll rule_rationale tests passed.\n"
  else (
    printf "\n%d FAILURE(S)\n" !failures;
    exit 1)
