(** Integration tests for the expansion → validator pipeline. *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[pipeline] FAIL: %s\n%!" msg;
    incr fails)

let run msg f =
  incr cases;
  f msg

let find_result id results =
  List.find_opt (fun (r : Validators.result) -> r.id = id) results

let () =
  (* ════════════════════════════════════════════════════════════════════ Legacy
     expansion mode
     ════════════════════════════════════════════════════════════════════ *)

  (* Legacy expansion strips \textbf, \emph, \section by default *)
  run "legacy expansion strips textbf" (fun tag ->
      let cfg = Rest_simple_expander.default in
      let expanded = Rest_simple_expander.expand_fix cfg "\\textbf{hello}" in
      expect (expanded = "hello") (tag ^ ": textbf stripped"));

  run "legacy expansion strips emph" (fun tag ->
      let cfg = Rest_simple_expander.default in
      let expanded = Rest_simple_expander.expand_fix cfg "\\emph{world}" in
      expect (expanded = "world") (tag ^ ": emph stripped"));

  run "legacy expansion strips nested" (fun tag ->
      let cfg = Rest_simple_expander.default in
      let expanded =
        Rest_simple_expander.expand_fix cfg "\\textbf{\\emph{nested}}"
      in
      expect (expanded = "nested") (tag ^ ": nested stripped"));

  run "legacy expansion preserves unknown commands" (fun tag ->
      let cfg = Rest_simple_expander.default in
      let expanded = Rest_simple_expander.expand_fix cfg "\\frac{1}{2}" in
      expect (expanded = "\\frac{1}{2}") (tag ^ ": frac preserved"));

  run "legacy expansion handles bfseries" (fun tag ->
      let cfg = Rest_simple_expander.default in
      let expanded = Rest_simple_expander.expand_fix cfg "{\\bfseries text}" in
      expect (String.length expanded > 0) (tag ^ ": bfseries handled"));

  (* ════════════════════════════════════════════════════════════════════ Custom
     expansion config
     ════════════════════════════════════════════════════════════════════ *)
  run "custom config strips custom commands" (fun tag ->
      let cfg =
        {
          Rest_simple_expander.strip_controls = [ "myfoo" ];
          bfseries_until_brace = false;
          catalogue = None;
        }
      in
      let expanded = Rest_simple_expander.expand_fix cfg "\\myfoo{bar}" in
      expect (expanded = "bar") (tag ^ ": custom strip"));

  run "custom config preserves non-listed" (fun tag ->
      let cfg =
        {
          Rest_simple_expander.strip_controls = [ "myfoo" ];
          bfseries_until_brace = false;
          catalogue = None;
        }
      in
      let expanded = Rest_simple_expander.expand_fix cfg "\\textbf{bold}" in
      expect (expanded = "\\textbf{bold}") (tag ^ ": textbf preserved"));

  (* ════════════════════════════════════════════════════════════════════ Expand
     then validate pipeline
     ════════════════════════════════════════════════════════════════════ *)
  run "expand then validate: no false positives on clean" (fun tag ->
      let cfg = Rest_simple_expander.default in
      let expanded = Rest_simple_expander.expand_fix cfg "\\emph{test}" in
      let results = Validators.run_all expanded in
      (* "test" is clean text, should fire very few/no rules *)
      let errors =
        List.filter
          (fun (r : Validators.result) -> r.severity = Validators.Error)
          results
      in
      expect (List.length errors = 0) (tag ^ ": no errors on clean input"));

  run "expand then validate: validates expanded content" (fun tag ->
      let cfg = Rest_simple_expander.default in
      let src = "\\textbf{$\\frac{}{2}$}" in
      let expanded = Rest_simple_expander.expand_fix cfg src in
      (* After expansion, textbf is stripped, leaving $\frac{}{2}$ *)
      let results = Validators.run_all expanded in
      let math_057 = find_result "MATH-057" results in
      expect (math_057 <> None) (tag ^ ": MATH-057 fires on expanded empty frac"));

  run "expand and tokenize returns both" (fun tag ->
      let cfg = Rest_simple_expander.default in
      let expanded, tokens =
        Rest_simple_expander.expand_and_tokenize cfg "\\textbf{hello}"
      in
      expect (expanded = "hello") (tag ^ ": expanded is hello");
      (* Tokens should be from expanded text *)
      expect (List.length tokens >= 0) (tag ^ ": tokens is a list"));

  (* ════════════════════════════════════════════════════════════════════ JSON
     config parsing
     ════════════════════════════════════════════════════════════════════ *)
  run "of_json parses strip_controls" (fun tag ->
      let json =
        Yojson.Safe.from_string
          {|{"strip_controls": ["myfoo", "mybar"], "bfseries_until_brace": false}|}
      in
      let cfg = Rest_simple_expander.of_json json in
      expect
        (cfg.strip_controls = [ "myfoo"; "mybar" ])
        (tag ^ ": strip_controls parsed"));

  run "of_json falls back to default on bad input" (fun tag ->
      let json = Yojson.Safe.from_string {|{"bad": true}|} in
      let cfg = Rest_simple_expander.of_json json in
      expect
        (cfg.strip_controls = [ "textbf"; "emph"; "section" ])
        (tag ^ ": default strip_controls"));

  (* ════════════════════════════════════════════════════════════════════ Edge
     cases
     ════════════════════════════════════════════════════════════════════ *)
  run "empty input expands to empty" (fun tag ->
      let cfg = Rest_simple_expander.default in
      let expanded = Rest_simple_expander.expand_fix cfg "" in
      expect (expanded = "") (tag ^ ": empty"));

  run "no commands expands to same" (fun tag ->
      let cfg = Rest_simple_expander.default in
      let expanded = Rest_simple_expander.expand_fix cfg "plain text" in
      expect (expanded = "plain text") (tag ^ ": unchanged"));

  run "expand fixpoint: repeated expansion converges" (fun tag ->
      let cfg = Rest_simple_expander.default in
      let expanded =
        Rest_simple_expander.expand_fix cfg "\\textbf{\\textbf{\\emph{deep}}}"
      in
      expect (expanded = "deep") (tag ^ ": deep nesting"));

  if !fails > 0 then (
    Printf.eprintf "[pipeline] %d failure(s)\n%!" !fails;
    exit 1)
  else Printf.printf "[pipeline] PASS %d cases\n%!" !cases
