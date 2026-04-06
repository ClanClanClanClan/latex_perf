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
      (* Stubbed language packs *)
      ("corpora/lint/i18n_qa/i18n_qa_pt.tex", "pt", false);
      ("corpora/lint/i18n_qa/i18n_qa_ru.tex", "ru", false);
      ("corpora/lint/i18n_qa/i18n_qa_pl.tex", "pl", false);
      ("corpora/lint/i18n_qa/i18n_qa_ko.tex", "ko", false);
      ("corpora/lint/i18n_qa/i18n_qa_it.tex", "it", false);
      ("corpora/lint/i18n_qa/i18n_qa_nl.tex", "nl", false);
      ("corpora/lint/i18n_qa/i18n_qa_tr.tex", "tr", false);
      ("corpora/lint/i18n_qa/i18n_qa_el.tex", "el", false);
    ]
  in

  let tested = ref 0 in
  let skipped = ref 0 in

  List.iter
    (fun (path, expected_lang, is_live) ->
      match read_file path with
      | None ->
          incr skipped;
          Printf.printf "  SKIP %s (file not found)\n%!" path
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
  check "minimum 15 languages tested" (!tested >= 15);

  if !fails > 0 then (
    Printf.eprintf "[test_i18n_qa] FAIL: %d failures\n%!" !fails;
    exit 1)
  else Printf.printf "[test_i18n_qa] PASS: language QA gate\n%!"
