(** Multi-engine `.aux` parser regression test (v26.3 §3 items F + G).

    Verifies [Aux_state.of_string] handles pdflatex, xelatex, and lualatex
    `.aux` files without spurious warnings. Each fixture contains the same core
    content (1 label, 1 bibcite, bibstyle, bibdata) plus engine-specific macros
    — the test asserts the core is recovered cleanly and [parse_warnings] is
    empty. *)

open Test_helpers

let repo_root = Sys.getcwd ()

let fixture_path name =
  let candidates =
    [
      Filename.concat repo_root ("corpora/aux/" ^ name);
      Filename.concat repo_root ("../../corpora/aux/" ^ name);
      Filename.concat repo_root ("../../../corpora/aux/" ^ name);
    ]
  in
  match List.find_opt Sys.file_exists candidates with
  | Some p -> p
  | None ->
      Printf.eprintf "[aux-engines] FATAL: fixture %s not found (cwd=%s)\n" name
        repo_root;
      exit 1

let read_all path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let check_engine ~engine_name ~fixture_name =
  let path = fixture_path fixture_name in
  let content = read_all path in
  let state = Latex_parse_lib.Aux_state.of_string ~source_path:path content in
  let n_labels = List.length state.labels in
  let n_cites = List.length state.bibcites in
  let n_warnings = List.length state.parse_warnings in
  let bibstyle_ok = state.bibstyle = Some "plain" in
  let bibdata_ok = state.bibdata = [ "refs" ] in
  let label_ok =
    match Latex_parse_lib.Aux_state.find_label state "sec:intro" with
    | Some _ -> true
    | None -> false
  in
  let cite_ok =
    match Latex_parse_lib.Aux_state.find_bibcite state "Knuth1984" with
    | Some _ -> true
    | None -> false
  in
  let labels_unique = Latex_parse_lib.Aux_state.labels_unique state in
  expect
    (n_labels = 1
    && n_cites = 1
    && n_warnings = 0
    && bibstyle_ok
    && bibdata_ok
    && label_ok
    && cite_ok
    && labels_unique)
    (Printf.sprintf
       "%s: labels=%d cites=%d warnings=%d bibstyle_ok=%b bibdata_ok=%b \
        label_ok=%b cite_ok=%b unique=%b"
       engine_name n_labels n_cites n_warnings bibstyle_ok bibdata_ok label_ok
       cite_ok labels_unique)

let () =
  run "pdflatex .aux parses cleanly" (fun _tag ->
      check_engine ~engine_name:"pdflatex" ~fixture_name:"pdflatex_minimal.aux");
  run "xelatex .aux parses cleanly (v26.3 item F)" (fun _tag ->
      check_engine ~engine_name:"xelatex" ~fixture_name:"xelatex_minimal.aux");
  run "lualatex .aux parses cleanly (v26.3 item G)" (fun _tag ->
      check_engine ~engine_name:"lualatex" ~fixture_name:"lualatex_minimal.aux");
  finalise "aux-engines"
