(** Unit tests for L1 straggler validators: CMD-007, CMD-010, FONT-001,
    FONT-004, RTL-003, RTL-004, CJK-008, CJK-015, TYPO-059, PT-002. *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  incr cases;
  if not cond then (
    Printf.eprintf "FAIL: %s\n%!" msg;
    incr fails)

let run msg f =
  let tag = Printf.sprintf "case %d: %s" (!cases + 1) msg in
  f tag

let find_result id results =
  List.find_opt (fun (r : Validators.result) -> r.id = id) results

let fires id src =
  let results = Validators.run_all src in
  match find_result id results with Some _ -> true | None -> false

let does_not_fire id src =
  let results = Validators.run_all src in
  match find_result id results with Some _ -> false | None -> true

let fires_with_count id src expected_count =
  let results = Validators.run_all src in
  match find_result id results with
  | Some r -> r.count = expected_count
  | None -> false

let () =
  (* ══════════════════════════════════════════════════════════════════════
     CMD-007: Optional argument declared but not used in definition body
     ══════════════════════════════════════════════════════════════════════ *)
  run "CMD-007 fires: #1 declared but not in body" (fun tag ->
      expect
        (fires "CMD-007" {|\newcommand{\foo}[1]{bar}|})
        (tag ^ ": unused #1"));
  run "CMD-007 fires: #2 unused in 2-arg command" (fun tag ->
      expect
        (fires "CMD-007" {|\newcommand{\foo}[2]{#1 only}|})
        (tag ^ ": #2 unused"));
  run "CMD-007 clean: all args used" (fun tag ->
      expect
        (does_not_fire "CMD-007" {|\newcommand{\foo}[2]{#1 and #2}|})
        (tag ^ ": both used"));
  run "CMD-007 clean: single arg used" (fun tag ->
      expect
        (does_not_fire "CMD-007" {|\newcommand{\foo}[1]{hello #1}|})
        (tag ^ ": #1 used"));
  run "CMD-007 clean: no optional args" (fun tag ->
      expect
        (does_not_fire "CMD-007" {|\newcommand{\foo}{bar}|})
        (tag ^ ": no args"));
  run "CMD-007 fires: renewcommand with unused arg" (fun tag ->
      expect
        (fires "CMD-007" {|\renewcommand{\foo}[1]{fixed}|})
        (tag ^ ": renewcommand"));
  run "CMD-007 fires: providecommand with unused arg" (fun tag ->
      expect
        (fires "CMD-007" {|\providecommand{\bar}[1]{baz}|})
        (tag ^ ": providecommand"));
  run "CMD-007 count: two violations" (fun tag ->
      expect
        (fires_with_count "CMD-007"
           {|\newcommand{\a}[1]{x}
\newcommand{\b}[2]{#1}|} 2)
        (tag ^ ": count 2"));

  (* ══════════════════════════════════════════════════════════════════════
     CMD-010: More than three successive macro renewals
     ══════════════════════════════════════════════════════════════════════ *)
  run "CMD-010 fires: 4 successive renewcommands" (fun tag ->
      expect
        (fires "CMD-010"
           {|\renewcommand{\a}{x}
\renewcommand{\b}{y}
\renewcommand{\c}{z}
\renewcommand{\d}{w}|})
        (tag ^ ": 4 consecutive"));
  run "CMD-010 fires: 5 successive renewcommands" (fun tag ->
      expect
        (fires_with_count "CMD-010"
           {|\renewcommand{\a}{x}
\renewcommand{\b}{y}
\renewcommand{\c}{z}
\renewcommand{\d}{w}
\renewcommand{\e}{v}|}
           2)
        (tag ^ ": 5 lines = count 2"));
  run "CMD-010 clean: 3 successive (threshold not exceeded)" (fun tag ->
      expect
        (does_not_fire "CMD-010"
           {|\renewcommand{\a}{x}
\renewcommand{\b}{y}
\renewcommand{\c}{z}|})
        (tag ^ ": exactly 3"));
  run "CMD-010 clean: broken by non-renew line" (fun tag ->
      expect
        (does_not_fire "CMD-010"
           {|\renewcommand{\a}{x}
\renewcommand{\b}{y}
% a comment
\renewcommand{\c}{z}
\renewcommand{\d}{w}|})
        (tag ^ ": interrupted by comment"));
  run "CMD-010 clean: single renewcommand" (fun tag ->
      expect
        (does_not_fire "CMD-010" {|\renewcommand{\a}{x}|})
        (tag ^ ": just one"));
  run "CMD-010 clean: no renewcommand" (fun tag ->
      expect (does_not_fire "CMD-010" {|Hello world.|}) (tag ^ ": no renews"));

  (* ══════════════════════════════════════════════════════════════════════
     FONT-001: Small-caps applied to all-caps word (ineffective)
     ══════════════════════════════════════════════════════════════════════ *)
  run "FONT-001 fires: \\textsc{ABC}" (fun tag ->
      expect (fires "FONT-001" {|\textsc{ABC}|}) (tag ^ ": all caps"));
  run "FONT-001 fires: \\textsc{HELLO WORLD}" (fun tag ->
      expect
        (fires "FONT-001" {|\textsc{HELLO WORLD}|})
        (tag ^ ": multi-word caps"));
  run "FONT-001 clean: \\textsc{Hello}" (fun tag ->
      expect (does_not_fire "FONT-001" {|\textsc{Hello}|}) (tag ^ ": mixed case"));
  run "FONT-001 clean: \\textsc{abc}" (fun tag ->
      expect (does_not_fire "FONT-001" {|\textsc{abc}|}) (tag ^ ": lowercase"));
  run "FONT-001 clean: no textsc" (fun tag ->
      expect (does_not_fire "FONT-001" {|ABC is all caps|}) (tag ^ ": no textsc"));
  run "FONT-001 count: two violations" (fun tag ->
      expect
        (fires_with_count "FONT-001" {|\textsc{ABC} and \textsc{XYZ}|} 2)
        (tag ^ ": count 2"));

  (* ══════════════════════════════════════════════════════════════════════
     FONT-004: Font change inside math via \textit not \mathit
     ══════════════════════════════════════════════════════════════════════ *)
  run "FONT-004 fires: \\textit inside math" (fun tag ->
      expect (fires "FONT-004" {|$\textit{x}$|}) (tag ^ ": textit in $"));
  run "FONT-004 fires: \\textbf inside math" (fun tag ->
      expect (fires "FONT-004" {|$\textbf{v}$|}) (tag ^ ": textbf in $"));
  run "FONT-004 fires: \\textrm inside math" (fun tag ->
      expect (fires "FONT-004" {|$\textrm{const}$|}) (tag ^ ": textrm in $"));
  run "FONT-004 fires: \\textsf inside math" (fun tag ->
      expect (fires "FONT-004" {|$\textsf{A}$|}) (tag ^ ": textsf in $"));
  run "FONT-004 fires: \\texttt inside math" (fun tag ->
      expect (fires "FONT-004" {|$\texttt{code}$|}) (tag ^ ": texttt in $"));
  run "FONT-004 clean: \\mathit inside math" (fun tag ->
      expect (does_not_fire "FONT-004" {|$\mathit{x}$|}) (tag ^ ": mathit ok"));
  run "FONT-004 clean: \\textit outside math" (fun tag ->
      expect
        (does_not_fire "FONT-004" {|\textit{hello}|})
        (tag ^ ": text mode ok"));
  run "FONT-004 count: two violations" (fun tag ->
      expect
        (fires_with_count "FONT-004" {|$\textit{a} + \textbf{b}$|} 2)
        (tag ^ ": count 2"));

  (* ══════════════════════════════════════════════════════════════════════
     RTL-003: Unbalanced \beginR / \endR primitives
     ══════════════════════════════════════════════════════════════════════ *)
  run "RTL-003 fires: one \\beginR, no \\endR" (fun tag ->
      expect (fires "RTL-003" {|\beginR hello|}) (tag ^ ": missing endR"));
  run "RTL-003 fires: two \\beginR, one \\endR" (fun tag ->
      expect
        (fires_with_count "RTL-003" {|\beginR foo \endR \beginR bar|} 1)
        (tag ^ ": 2 opens 1 close"));
  run "RTL-003 clean: balanced" (fun tag ->
      expect
        (does_not_fire "RTL-003" {|\beginR hello \endR|})
        (tag ^ ": balanced"));
  run "RTL-003 clean: no RTL primitives" (fun tag ->
      expect (does_not_fire "RTL-003" {|Hello world.|}) (tag ^ ": no RTL"));
  run "RTL-003 fires: extra \\endR" (fun tag ->
      expect (fires "RTL-003" {|\endR extra|}) (tag ^ ": orphan endR"));
  run "RTL-003 severity is Error" (fun tag ->
      let results = Validators.run_all {|\beginR no end|} in
      match find_result "RTL-003" results with
      | Some r -> expect (r.severity = Error) (tag ^ ": severity Error")
      | None -> expect false (tag ^ ": should fire"));

  (* ══════════════════════════════════════════════════════════════════════
     RTL-004: RTL punctuation not mirrored in math
     ══════════════════════════════════════════════════════════════════════ *)
  run "RTL-004 fires: Hebrew maqaf U+05BE in math" (fun tag ->
      expect (fires "RTL-004" "$x\xd6\xbey$") (tag ^ ": maqaf in math"));
  run "RTL-004 fires: Arabic comma U+060C in math" (fun tag ->
      expect (fires "RTL-004" "$a\xd8\x8cb$") (tag ^ ": arabic comma in math"));
  run "RTL-004 fires: Hebrew geresh U+05F3 in math" (fun tag ->
      expect (fires "RTL-004" "$n\xd7\x83$") (tag ^ ": geresh in math"));
  run "RTL-004 clean: RTL punct outside math" (fun tag ->
      expect (does_not_fire "RTL-004" "hello\xd6\xbeworld") (tag ^ ": text mode"));
  run "RTL-004 clean: no RTL punct" (fun tag ->
      expect (does_not_fire "RTL-004" "$x + y$") (tag ^ ": ASCII math"));

  (* ══════════════════════════════════════════════════════════════════════
     CJK-008: Full-width space U+3000 inside math mode
     ══════════════════════════════════════════════════════════════════════ *)
  run "CJK-008 fires: U+3000 in math" (fun tag ->
      expect
        (fires "CJK-008" "$x\xe3\x80\x80y$")
        (tag ^ ": fullwidth space in math"));
  run "CJK-008 clean: U+3000 outside math" (fun tag ->
      expect
        (does_not_fire "CJK-008" "hello\xe3\x80\x80world")
        (tag ^ ": text mode"));
  run "CJK-008 clean: normal space in math" (fun tag ->
      expect (does_not_fire "CJK-008" "$x + y$") (tag ^ ": ASCII space"));
  run "CJK-008 fires: display math" (fun tag ->
      expect (fires "CJK-008" "\\[x\xe3\x80\x80y\\]") (tag ^ ": display math"));
  run "CJK-008 count: two occurrences" (fun tag ->
      expect
        (fires_with_count "CJK-008" "$a\xe3\x80\x80b\xe3\x80\x80c$" 2)
        (tag ^ ": count 2"));

  (* ══════════════════════════════════════════════════════════════════════
     CJK-015: Chinese comma U+3001 inside math mode
     ══════════════════════════════════════════════════════════════════════ *)
  run "CJK-015 fires: U+3001 in math" (fun tag ->
      expect
        (fires "CJK-015" "$a\xe3\x80\x81b$")
        (tag ^ ": ideographic comma in math"));
  run "CJK-015 clean: U+3001 outside math" (fun tag ->
      expect
        (does_not_fire "CJK-015" "item1\xe3\x80\x81item2")
        (tag ^ ": text mode"));
  run "CJK-015 clean: ASCII comma in math" (fun tag ->
      expect (does_not_fire "CJK-015" "$a, b, c$") (tag ^ ": ASCII comma"));
  run "CJK-015 fires: \\( \\) math" (fun tag ->
      expect (fires "CJK-015" "\\(x\xe3\x80\x81y\\)") (tag ^ ": inline \\(\\)"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-059: Punctuation inside math adjacent to operator
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-059 fires: comma before equals" (fun tag ->
      expect (fires "TYPO-059" "$a,=b$") (tag ^ ": ,="));
  run "TYPO-059 fires: semicolon before plus" (fun tag ->
      expect (fires "TYPO-059" "$x;+y$") (tag ^ ": ;+"));
  run "TYPO-059 fires: period before less-than" (fun tag ->
      expect (fires "TYPO-059" "$a.<b$") (tag ^ ": .<"));
  run "TYPO-059 fires: comma space equals" (fun tag ->
      expect (fires "TYPO-059" "$a, =b$") (tag ^ ": , ="));
  run "TYPO-059 clean: comma then space then letter" (fun tag ->
      expect (does_not_fire "TYPO-059" "$a, b, c$") (tag ^ ": normal list"));
  run "TYPO-059 clean: no math" (fun tag ->
      expect (does_not_fire "TYPO-059" "hello, =world") (tag ^ ": not in math"));
  run "TYPO-059 clean: no offending pattern" (fun tag ->
      expect (does_not_fire "TYPO-059" "$x + y = z$") (tag ^ ": clean math"));

  (* ══════════════════════════════════════════════════════════════════════
     PT-002: pt-BR decimal comma and thousand dot enforcement
     ══════════════════════════════════════════════════════════════════════ *)
  run "PT-002 fires: dot decimal in pt-BR document" (fun tag ->
      expect
        (fires "PT-002" {|\usepackage[brazilian]{babel}
$3.14$|})
        (tag ^ ": 3.14 in pt-BR"));
  run "PT-002 fires: thousand separator in pt-BR" (fun tag ->
      expect
        (fires "PT-002" {|\usepackage[brazil]{babel}
$1.000$|})
        (tag ^ ": 1.000 in pt-BR"));
  run "PT-002 fires: portuges variant" (fun tag ->
      expect
        (fires "PT-002" {|\usepackage[portuges]{babel}
$2.5$|})
        (tag ^ ": portuges"));
  run "PT-002 clean: no pt-BR indicator" (fun tag ->
      expect (does_not_fire "PT-002" {|$3.14$|}) (tag ^ ": no babel pt-BR"));
  run "PT-002 clean: pt-BR but no math numbers" (fun tag ->
      expect
        (does_not_fire "PT-002" {|\usepackage[brazilian]{babel}
$x + y$|})
        (tag ^ ": no numbers"));
  run "PT-002 clean: dot outside math in pt-BR" (fun tag ->
      expect
        (does_not_fire "PT-002"
           {|\usepackage[brazilian]{babel}
The value is 3.14.|})
        (tag ^ ": text mode"));
  run "PT-002 count: two math numbers" (fun tag ->
      expect
        (fires_with_count "PT-002"
           {|\usepackage[brazilian]{babel}
$3.14$ and $2.71$|} 2)
        (tag ^ ": count 2"));

  (* ══════════════════════════════════════════════════════════════════════
     Registration and severity checks
     ══════════════════════════════════════════════════════════════════════ *)
  run "All 10 straggler rules are reachable via run_all" (fun tag ->
      (* Verify each rule fires on its canonical trigger input *)
      let triggers =
        [
          ("CMD-007", {|\newcommand{\foo}[1]{bar}|});
          ( "CMD-010",
            {|\renewcommand{\a}{x}
\renewcommand{\b}{y}
\renewcommand{\c}{z}
\renewcommand{\d}{w}|}
          );
          ("FONT-001", {|\textsc{ABC}|});
          ("FONT-004", {|$\textit{x}$|});
          ("RTL-003", {|\beginR hello|});
          ("RTL-004", "$\xd6\xbe$");
          ("CJK-008", "$\xe3\x80\x80$");
          ("CJK-015", "$\xe3\x80\x81$");
          ("TYPO-059", "$a,=b$");
          ("PT-002", {|\usepackage[brazilian]{babel}
$3.14$|});
        ]
      in
      List.iter
        (fun (eid, src) ->
          expect (fires eid src) (tag ^ ": " ^ eid ^ " reachable"))
        triggers);

  run "Preconditions: all straggler rules map to L1" (fun tag ->
      let expected =
        [
          "CMD-007";
          "CMD-010";
          "FONT-001";
          "FONT-004";
          "RTL-003";
          "RTL-004";
          "CJK-008";
          "CJK-015";
          "TYPO-059";
          "PT-002";
        ]
      in
      List.iter
        (fun eid ->
          expect
            (Validators.precondition_of_rule_id eid = L1)
            (tag ^ ": " ^ eid ^ " -> L1"))
        expected);

  run "RTL-003 severity is Error" (fun tag ->
      let results = Validators.run_all {|\beginR missing|} in
      match find_result "RTL-003" results with
      | Some r -> expect (r.severity = Validators.Error) (tag ^ ": Error")
      | None -> expect false (tag ^ ": should fire"));

  run "RTL-004 severity is Warning" (fun tag ->
      let results = Validators.run_all "$\xd6\xbe$" in
      match find_result "RTL-004" results with
      | Some r -> expect (r.severity = Validators.Warning) (tag ^ ": Warning")
      | None -> expect false (tag ^ ": should fire"));

  run "CJK-008 severity is Warning" (fun tag ->
      let results = Validators.run_all "$\xe3\x80\x80$" in
      match find_result "CJK-008" results with
      | Some r -> expect (r.severity = Validators.Warning) (tag ^ ": Warning")
      | None -> expect false (tag ^ ": should fire"));

  run "CJK-015 severity is Warning" (fun tag ->
      let results = Validators.run_all "$\xe3\x80\x81$" in
      match find_result "CJK-015" results with
      | Some r -> expect (r.severity = Validators.Warning) (tag ^ ": Warning")
      | None -> expect false (tag ^ ": should fire"));

  (* ══════════════════════════════════════════════════════════════════════
     Cross-cutting: combined document test
     ══════════════════════════════════════════════════════════════════════ *)
  run "Combined: multiple rules fire on complex document" (fun tag ->
      let doc =
        {|\usepackage[brazilian]{babel}
\newcommand{\myop}[1]{constant}
\renewcommand{\a}{x}
\renewcommand{\b}{y}
\renewcommand{\c}{z}
\renewcommand{\d}{w}
\textsc{HELLO}
$\textit{italic} + |}
        ^ "\xe3\x80\x80"
        ^ {| + 3.14$
\beginR unclosed|}
      in
      let results = Validators.run_all doc in
      expect (find_result "CMD-007" results <> None) (tag ^ ": CMD-007 fires");
      expect (find_result "CMD-010" results <> None) (tag ^ ": CMD-010 fires");
      expect (find_result "FONT-001" results <> None) (tag ^ ": FONT-001 fires");
      expect (find_result "FONT-004" results <> None) (tag ^ ": FONT-004 fires");
      expect (find_result "CJK-008" results <> None) (tag ^ ": CJK-008 fires");
      expect (find_result "PT-002" results <> None) (tag ^ ": PT-002 fires");
      expect (find_result "RTL-003" results <> None) (tag ^ ": RTL-003 fires"));

  (* ══════════════════════════════════════════════════════════════════════ Edge
     cases
     ══════════════════════════════════════════════════════════════════════ *)
  run "Empty string: no straggler rules fire" (fun tag ->
      let results = Validators.run_all "" in
      let straggler_ids =
        [
          "CMD-007";
          "CMD-010";
          "FONT-001";
          "FONT-004";
          "RTL-003";
          "RTL-004";
          "CJK-008";
          "CJK-015";
          "TYPO-059";
          "PT-002";
        ]
      in
      List.iter
        (fun eid ->
          expect
            (find_result eid results = None)
            (tag ^ ": " ^ eid ^ " silent on empty"))
        straggler_ids);

  run "Plain text: no straggler rules fire" (fun tag ->
      let results = Validators.run_all "Hello, this is plain text." in
      let straggler_ids =
        [
          "CMD-007";
          "CMD-010";
          "FONT-001";
          "FONT-004";
          "RTL-003";
          "RTL-004";
          "CJK-008";
          "CJK-015";
          "TYPO-059";
          "PT-002";
        ]
      in
      List.iter
        (fun eid ->
          expect
            (find_result eid results = None)
            (tag ^ ": " ^ eid ^ " silent on plain"))
        straggler_ids);

  (* ═══════════════════════════════════════════════════════════ *)
  Printf.printf "test_validators_stragglers: %d cases, %d failures\n%!" !cases
    !fails;
  if !fails > 0 then exit 1
