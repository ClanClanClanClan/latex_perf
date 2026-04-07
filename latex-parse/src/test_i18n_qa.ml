(** Language QA gate test (spec W102-104).

    Verifies that: 1. Language detection correctly identifies each document's
    language 2. run_all_for_language executes without crashes 3. Per-language
    validators produce non-empty results on comprehensive files 4. Parser
    succeeds on all files

    Exit criteria: "language QA pass" *)

let fails = ref 0
let total = ref 0

let check name cond =
  incr total;
  if not cond then (
    Printf.eprintf "FAIL: %s\n%!" name;
    incr fails)
  else Printf.printf "  ok  %s\n%!" name

let read_file path =
  try
    let ic = open_in path in
    let n = in_channel_length ic in
    let s = Bytes.create n in
    really_input ic s 0 n;
    close_in ic;
    Some (Bytes.to_string s)
  with _ -> None

let () =
  Printf.printf "[test_i18n_qa] Language QA Gate\n%!";

  (* Resolve base directory (same logic as test_golden_corpus.ml) *)
  let exe_dir = Filename.dirname Sys.argv.(0) in
  let candidates =
    [ Filename.concat exe_dir "../.."; "."; Filename.concat exe_dir "../../.." ]
  in
  let base_dir =
    try
      List.find
        (fun d -> Sys.file_exists (Filename.concat d "corpora"))
        candidates
    with Not_found ->
      Printf.eprintf
        "[test_i18n_qa] WARNING: cannot find corpora/ directory\n%!";
      "."
  in
  Printf.printf "[test_i18n_qa] base_dir = %s\n%!" base_dir;

  (* All i18n_qa corpus files with expected languages *)
  let test_cases =
    [
      (* Live language packs — original *)
      ("corpora/lint/i18n_qa/i18n_qa_en.tex", "en", true);
      ("corpora/lint/i18n_qa/i18n_qa_fr.tex", "fr", true);
      ("corpora/lint/i18n_qa/i18n_qa_de.tex", "de", true);
      ("corpora/lint/i18n_qa/i18n_qa_es.tex", "es", true);
      ("corpora/lint/i18n_qa/i18n_qa_ja.tex", "ja", true);
      ("corpora/lint/i18n_qa/i18n_qa_zh.tex", "zh", true);
      ("corpora/lint/i18n_qa/i18n_qa_ar.tex", "ar", true);
      (* Live language packs — comprehensive *)
      ("corpora/lint/i18n_qa/i18n_qa_en_comprehensive.tex", "en", true);
      ("corpora/lint/i18n_qa/i18n_qa_fr_comprehensive.tex", "fr", true);
      ("corpora/lint/i18n_qa/i18n_qa_de_comprehensive.tex", "de", true);
      ("corpora/lint/i18n_qa/i18n_qa_es_comprehensive.tex", "es", true);
      ("corpora/lint/i18n_qa/i18n_qa_ja_comprehensive.tex", "ja", true);
      ("corpora/lint/i18n_qa/i18n_qa_zh_comprehensive.tex", "zh", true);
      ("corpora/lint/i18n_qa/i18n_qa_ar_comprehensive.tex", "ar", true);
      (* Stubbed language packs — short files *)
      ("corpora/lint/i18n_qa/i18n_qa_pt.tex", "pt", false);
      ("corpora/lint/i18n_qa/i18n_qa_ru.tex", "ru", false);
      ("corpora/lint/i18n_qa/i18n_qa_pl.tex", "pl", false);
      ("corpora/lint/i18n_qa/i18n_qa_ko.tex", "ko", false);
      ("corpora/lint/i18n_qa/i18n_qa_it.tex", "it", false);
      ("corpora/lint/i18n_qa/i18n_qa_nl.tex", "nl", false);
      ("corpora/lint/i18n_qa/i18n_qa_tr.tex", "tr", false);
      ("corpora/lint/i18n_qa/i18n_qa_el.tex", "el", false);
      (* Stubbed language packs — full synthetic papers *)
      ("corpora/lint/i18n_qa/i18n_qa_cs_paper.tex", "cs", false);
      ("corpora/lint/i18n_qa/i18n_qa_ro_paper.tex", "ro", false);
      ("corpora/lint/i18n_qa/i18n_qa_he_paper.tex", "he", false);
      ("corpora/lint/i18n_qa/i18n_qa_hi_paper.tex", "hi", false);
      ("corpora/lint/i18n_qa/i18n_qa_sv_paper.tex", "sv", false);
      ("corpora/lint/i18n_qa/i18n_qa_cy_paper.tex", "cy", false);
      (* Mixed-language papers *)
      ("corpora/lint/i18n_qa/i18n_qa_mixed_fr_en_paper.tex", "fr", true);
      ("corpora/lint/i18n_qa/i18n_qa_mixed_zh_en_paper.tex", "zh", true);
      ("corpora/lint/i18n_qa/i18n_qa_mixed_ja_zh_paper.tex", "ja", true);
      (* Edge cases *)
      ("corpora/lint/i18n_qa/i18n_qa_no_babel_paper.tex", "en", false);
      ("corpora/lint/i18n_qa/i18n_qa_conflicting_paper.tex", "en", false);
    ]
  in

  let tested = ref 0 in
  let skipped = ref 0 in

  List.iter
    (fun (path, expected_lang, is_live) ->
      let full_path = Filename.concat base_dir path in
      match read_file full_path with
      | None ->
          incr skipped;
          Printf.printf "  SKIP %s (file not found)\n%!" full_path
      | Some content ->
          incr tested;
          let basename = Filename.basename path in

          (* Test 1: Language detection *)
          let detected =
            Latex_parse_lib.Language_detect.detect_language content
          in
          check
            (Printf.sprintf "[%s] detect=%s (expect %s)" basename detected
               expected_lang)
            (detected = expected_lang);

          (* Test 2: run_all_for_language doesn't crash *)
          let crashed = ref false in
          let results =
            try
              Latex_parse_lib.Validators.run_all_for_language content
                (Some expected_lang)
            with exn ->
              Printf.eprintf "  CRASH: %s on %s\n%!" (Printexc.to_string exn)
                path;
              crashed := true;
              []
          in
          check
            (Printf.sprintf "[%s] run_all_for_language no crash" basename)
            (not !crashed);

          (* Test 3: Live language comprehensive files should produce results *)
          if is_live && String.length content > 200 then
            check
              (Printf.sprintf "[%s] validators fired (>0)" basename)
              (List.length results > 0);

          (* Test 4: Parser doesn't fail *)
          let parse_ok = Latex_parse_lib.Parser_l2.parse_success content in
          check (Printf.sprintf "[%s] parse success" basename) parse_ok;

          Printf.printf "    %s: %d validators fired\n%!" basename
            (List.length results))
    test_cases;

  Printf.printf "\n[test_i18n_qa] Summary: %d tested, %d skipped\n%!" !tested
    !skipped;
  Printf.printf "[test_i18n_qa] Checks: %d/%d passed\n%!" (!total - !fails)
    !total;

  (* Enforce minimum coverage *)
  check "minimum 20 files tested" (!tested >= 20);

  (* ── Per-language coverage report ──────────────────────────────── *)
  Printf.printf "\n[i18n-coverage] Per-language gated rule coverage:\n%!";
  let lang_rule_map =
    [
      ("en", [ "CE-001"; "CE-002"; "LANG-014"; "LANG-015"; "LANG-016" ]);
      ("fr", [ "FR-007"; "FR-008"; "LANG-003"; "LANG-011" ]);
      ("de", [ "DE-006" ]);
      ("ja", [ "JA-001"; "JA-002" ]);
      ("zh", [ "ZH-001"; "ZH-002" ]);
      ("ar", [ "AR-002" ]);
      ("hi", [ "HI-001" ]);
      ("ko", [ "KO-001" ]);
      ("he", [ "HE-001" ]);
      ("el", [ "EL-001" ]);
    ]
  in
  List.iter
    (fun (lang, expected_rules) ->
      (* Find a comprehensive file for this language *)
      let candidates =
        List.filter
          (fun (p, l, _) ->
            l = lang && String.length p > 30 (* skip tiny stubs *))
          test_cases
      in
      match candidates with
      | [] -> Printf.printf "  %s: no comprehensive file — skipped\n%!" lang
      | (path, _, _) :: _ -> (
          let full_path = Filename.concat base_dir path in
          match read_file full_path with
          | None -> Printf.printf "  %s: file not found — skipped\n%!" lang
          | Some content ->
              let results =
                Latex_parse_lib.Validators.run_all_for_language content
                  (Some lang)
              in
              let fired_ids =
                List.map
                  (fun (r : Latex_parse_lib.Validators.result) -> r.id)
                  results
              in
              let fired_count =
                List.length
                  (List.filter
                     (fun rid -> List.mem rid fired_ids)
                     expected_rules)
              in
              let total_expected = List.length expected_rules in
              Printf.printf
                "  %s: %d/%d language-specific rules fired (%d%%)\n%!" lang
                fired_count total_expected
                (if total_expected > 0 then fired_count * 100 / total_expected
                 else 100)))
    lang_rule_map;

  if !fails > 0 then (
    Printf.eprintf "[test_i18n_qa] FAIL: %d failures\n%!" !fails;
    exit 1)
  else Printf.printf "\n[test_i18n_qa] PASS: language QA gate\n%!"
