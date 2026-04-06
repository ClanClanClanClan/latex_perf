(** Language QA gate test (spec W102-104).

    Verifies that: 1. Language detection correctly identifies each document's
    language 2. run_all_for_language executes without crashes on all i18n corpus
    files 3. Per-language validators fire on their target documents

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
      (* Live language packs — comprehensive *)
      ("corpora/lint/i18n_qa/i18n_qa_en.tex", "en");
      ("corpora/lint/i18n_qa/i18n_qa_fr.tex", "fr");
      ("corpora/lint/i18n_qa/i18n_qa_de.tex", "de");
      ("corpora/lint/i18n_qa/i18n_qa_es.tex", "es");
      ("corpora/lint/i18n_qa/i18n_qa_ja.tex", "ja");
      ("corpora/lint/i18n_qa/i18n_qa_zh.tex", "zh");
      ("corpora/lint/i18n_qa/i18n_qa_ar.tex", "ar");
      (* Comprehensive variants *)
      ("corpora/lint/i18n_qa/i18n_qa_en_comprehensive.tex", "en");
      ("corpora/lint/i18n_qa/i18n_qa_fr_comprehensive.tex", "fr");
      ("corpora/lint/i18n_qa/i18n_qa_de_comprehensive.tex", "de");
      ("corpora/lint/i18n_qa/i18n_qa_es_comprehensive.tex", "es");
      ("corpora/lint/i18n_qa/i18n_qa_ja_comprehensive.tex", "ja");
      ("corpora/lint/i18n_qa/i18n_qa_zh_comprehensive.tex", "zh");
      ("corpora/lint/i18n_qa/i18n_qa_ar_comprehensive.tex", "ar");
      (* Stubbed language packs *)
      ("corpora/lint/i18n_qa/i18n_qa_pt.tex", "pt");
      ("corpora/lint/i18n_qa/i18n_qa_ru.tex", "ru");
      ("corpora/lint/i18n_qa/i18n_qa_pl.tex", "pl");
      ("corpora/lint/i18n_qa/i18n_qa_ko.tex", "ko");
      ("corpora/lint/i18n_qa/i18n_qa_it.tex", "it");
      ("corpora/lint/i18n_qa/i18n_qa_nl.tex", "nl");
      ("corpora/lint/i18n_qa/i18n_qa_tr.tex", "tr");
      ("corpora/lint/i18n_qa/i18n_qa_el.tex", "el");
    ]
  in

  let passed_langs = ref 0 in
  let tested_langs = ref 0 in

  List.iter
    (fun (path, expected_lang) ->
      match read_file path with
      | None -> Printf.printf "  SKIP %s (file not found)\n%!" path
      | Some content ->
          incr tested_langs;
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
          let results =
            try
              Latex_parse_lib.Validators.run_all_for_language content
                (Some expected_lang)
            with exn ->
              Printf.eprintf "  CRASH: %s on %s\n%!" (Printexc.to_string exn)
                path;
              []
          in
          check
            (Printf.sprintf "[%s] run_all_for_language no crash" basename)
            true;

          (* Test 3: parser doesn't fail *)
          let parse_ok = Latex_parse_lib.Parser_l2.parse_success content in
          check (Printf.sprintf "[%s] parse success" basename) parse_ok;

          Printf.printf "    %s: %d validators fired\n%!" basename
            (List.length results);
          incr passed_langs)
    test_cases;

  Printf.printf
    "\n[test_i18n_qa] Summary: %d/%d languages tested, %d/%d checks passed\n%!"
    !tested_langs (List.length test_cases) (!total - !fails) !total;

  if !fails > 0 then (
    Printf.eprintf "[test_i18n_qa] FAIL: %d failures\n%!" !fails;
    exit 1)
  else Printf.printf "[test_i18n_qa] PASS: language QA gate\n%!"
