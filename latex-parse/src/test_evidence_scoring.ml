(** Tests for evidence_scoring — confidence-weighted results (spec W75). *)

let fails = ref 0

let check name cond =
  if not cond then (
    Printf.eprintf "FAIL: %s\n%!" name;
    incr fails)
  else Printf.printf "  ok  %s\n%!" name

let () =
  Printf.printf "[test_evidence_scoring]\n%!";

  (* Test 1: default_config has reasonable values *)
  let cfg = Latex_parse_lib.Evidence_scoring.default_config in
  check "default min_weight = 0.0" (cfg.min_weight = 0.0);
  check "default boost_vpd = true" cfg.boost_vpd_rules;

  (* Test 2: score_result assigns correct confidence by family *)
  let mk_result id =
    {
      Latex_parse_lib.Validators_common.id;
      severity = Latex_parse_lib.Validators_common.Warning;
      message = "test";
      count = 1;
    }
  in
  let typo =
    Latex_parse_lib.Evidence_scoring.score_result (mk_result "TYPO-001") []
  in
  check "TYPO = High confidence"
    (typo.confidence = Latex_parse_lib.Evidence_scoring.High);

  let style =
    Latex_parse_lib.Evidence_scoring.score_result (mk_result "STYLE-001") []
  in
  check "STYLE = Low confidence"
    (style.confidence = Latex_parse_lib.Evidence_scoring.Low);

  let math =
    Latex_parse_lib.Evidence_scoring.score_result (mk_result "MATH-001") []
  in
  check "MATH = Medium confidence"
    (math.confidence = Latex_parse_lib.Evidence_scoring.Medium);

  (* Test 3a: VPD boost on non-Class-D rule → High. (STYLE-001 is Class D now,
     so use a non-D rule here.) *)
  let vpd_rule =
    Latex_parse_lib.Evidence_scoring.score_result (mk_result "MATH-001")
      [ "MATH-001" ]
  in
  check "VPD boost on non-D → High"
    (vpd_rule.confidence = Latex_parse_lib.Evidence_scoring.High);

  (* Test 3b: PR #241 (p1.6, memo §11.2) — VPD boost on Class D rule is capped
     at Low. Class D (advisory) results never claim certainty regardless of how
     trustworthy the pattern family is. *)
  let d_vpd_rule =
    Latex_parse_lib.Evidence_scoring.score_result (mk_result "STYLE-001")
      [ "STYLE-001" ]
  in
  check "Class D VPD boost capped at Low"
    (d_vpd_rule.confidence = Latex_parse_lib.Evidence_scoring.Low);

  (* Test 4: weight values *)
  check "High weight = 1.0" (typo.evidence_weight = 1.0);
  check "Low weight = 0.4" (style.evidence_weight = 0.4);
  check "Medium weight = 0.7" (math.evidence_weight = 0.7);

  (* Test 5: filter_by_config removes low-confidence results *)
  let high_cfg =
    {
      Latex_parse_lib.Evidence_scoring.min_confidence =
        Latex_parse_lib.Evidence_scoring.High;
      min_weight = 0.0;
      boost_vpd_rules = false;
    }
  in
  let results = [ typo; style; math ] in
  let filtered =
    Latex_parse_lib.Evidence_scoring.filter_by_config high_cfg results
  in
  check "High filter: only TYPO passes" (List.length filtered = 1);
  check "filtered is TYPO" ((List.hd filtered).id = "TYPO-001");

  (* Test 6: filter by min_weight *)
  let weight_cfg =
    {
      Latex_parse_lib.Evidence_scoring.min_confidence =
        Latex_parse_lib.Evidence_scoring.Low;
      min_weight = 0.5;
      boost_vpd_rules = false;
    }
  in
  let filtered2 =
    Latex_parse_lib.Evidence_scoring.filter_by_config weight_cfg results
  in
  check "weight filter removes Low" (List.length filtered2 = 2);

  (* Test 7: config_from_file with non-existent file returns default *)
  let cfg2 =
    Latex_parse_lib.Evidence_scoring.config_from_file "/nonexistent/path.json"
  in
  check "missing file → default" (cfg2.min_weight = 0.0);

  (* Test 8: load_config without env var returns default *)
  let cfg3 = Latex_parse_lib.Evidence_scoring.load_config () in
  check "load_config → default" (cfg3.boost_vpd_rules = true);

  Printf.printf "[test_evidence_scoring] done\n%!";
  if !fails > 0 then (
    Printf.eprintf "[test_evidence_scoring] %d failures\n%!" !fails;
    exit 1)
