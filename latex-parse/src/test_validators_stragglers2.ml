(** Unit tests for straggler batch 2 rules (CY, DE, NL, PL, PT, RU, TR, ZH,
    VERB, MATH, L3, REF, TYPO). *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[stragglers2] FAIL: %s\n%!" msg;
    incr fails)

let run msg f =
  incr cases;
  f msg

let find_result id src =
  let results = Validators.run_all src in
  List.find_opt (fun (r : Validators.result) -> r.id = id) results

let fires id src = find_result id src <> None

let fires_with_count id src expected_count =
  match find_result id src with
  | Some r -> r.count = expected_count
  | None -> false

let does_not_fire id src = find_result id src = None

let () =
  Unix.putenv "L0_VALIDATORS" "pilot";

  (* ══════════════════════════════════════════════════════════════════════
     CY-001: Cyrillic initials require NB-space
     ══════════════════════════════════════════════════════════════════════ *)
  run "CY-001 fires on Cyrillic initial + space" (fun tag ->
      expect
        (fires "CY-001" "\xd0\x98. \xd0\x90.")
        (tag ^ ": Cyrillic initial+space"));
  run "CY-001 clean no space" (fun tag ->
      expect
        (does_not_fire "CY-001" "\xd0\x98.\xc2\xa0\xd0\x90.")
        (tag ^ ": NBSP ok"));
  run "CY-001 clean ASCII" (fun tag ->
      expect (does_not_fire "CY-001" "A. B.") (tag ^ ": ASCII initials ok"));

  (* ══════════════════════════════════════════════════════════════════════
     DE-006: Swiss DE glyph eszett prohibited
     ══════════════════════════════════════════════════════════════════════ *)
  run "DE-006 fires on eszett" (fun tag ->
      expect (fires "DE-006" "Stra\xc3\x9fe") (tag ^ ": has eszett"));
  run "DE-006 fires on capital eszett" (fun tag ->
      expect (fires "DE-006" "\xe1\xba\x9e") (tag ^ ": capital eszett"));
  run "DE-006 clean no eszett" (fun tag ->
      expect (does_not_fire "DE-006" "Strasse") (tag ^ ": ss form ok"));
  run "DE-006 count=2" (fun tag ->
      expect
        (fires_with_count "DE-006" "Stra\xc3\x9fe und Gro\xc3\x9f" 2)
        (tag ^ ": count=2"));

  (* ══════════════════════════════════════════════════════════════════════
     NL-001: NL digraph IJ/ij capitalisation
     ══════════════════════════════════════════════════════════════════════ *)
  run "NL-001 fires on Ij at start" (fun tag ->
      expect (fires "NL-001" "Ij is wrong") (tag ^ ": Ij at start"));
  run "NL-001 fires on Ij after period" (fun tag ->
      expect (fires "NL-001" "End. Ij should be IJ") (tag ^ ": Ij after period"));
  run "NL-001 clean IJ" (fun tag ->
      expect (does_not_fire "NL-001" "IJ is correct") (tag ^ ": IJ ok"));
  run "NL-001 clean lowercase ij" (fun tag ->
      expect
        (does_not_fire "NL-001" "the ij digraph")
        (tag ^ ": lowercase ij ok"));

  (* ══════════════════════════════════════════════════════════════════════
     NL-002: NL quotes must be uniform
     ══════════════════════════════════════════════════════════════════════ *)
  run "NL-002 fires on mixed quotes" (fun tag ->
      expect
        (fires "NL-002"
           "\xe2\x80\x98hello\xe2\x80\x99 and \xe2\x80\x9eworld\xe2\x80\x9f")
        (tag ^ ": mixed single+german"));
  run "NL-002 clean single only" (fun tag ->
      expect
        (does_not_fire "NL-002" "\xe2\x80\x98hello\xe2\x80\x99")
        (tag ^ ": single only ok"));
  run "NL-002 clean ASCII" (fun tag ->
      expect (does_not_fire "NL-002" "plain text") (tag ^ ": ASCII ok"));

  (* ══════════════════════════════════════════════════════════════════════
     PL-002: PL primary quotes, nested guillemets only
     ══════════════════════════════════════════════════════════════════════ *)
  run "PL-002 fires on guillemets without German" (fun tag ->
      expect
        (fires "PL-002" "\xc2\xab hello \xc2\xbb")
        (tag ^ ": guillemets without german"));
  run "PL-002 clean with German quotes" (fun tag ->
      expect
        (does_not_fire "PL-002"
           "\xe2\x80\x9ehello\xe2\x80\x9d \xc2\xabnested\xc2\xbb")
        (tag ^ ": german+guillemets ok"));
  run "PL-002 clean ASCII" (fun tag ->
      expect (does_not_fire "PL-002" "plain text") (tag ^ ": ASCII ok"));

  (* ══════════════════════════════════════════════════════════════════════
     PT-001: pt-BR pre-2009 spellings forbidden
     ══════════════════════════════════════════════════════════════════════ *)
  run "PT-001 fires on pre-2009 spelling" (fun tag ->
      expect (fires "PT-001" "ac\xc3\xa7\xc3\xa3o") (tag ^ ": pre-2009 accao"));
  run "PT-001 fires on optimo" (fun tag ->
      expect (fires "PT-001" "\xc3\xb3ptimo") (tag ^ ": pre-2009 optimo"));
  run "PT-001 clean post-2009" (fun tag ->
      expect (does_not_fire "PT-001" "acao otimo") (tag ^ ": modern ok"));

  (* ══════════════════════════════════════════════════════════════════════
     RU-002: RU letter yo must be preserved
     ══════════════════════════════════════════════════════════════════════ *)
  run "RU-002 fires on mixed yo and missing yo" (fun tag ->
      expect
        (fires "RU-002" "\xd1\x91\xd1\x82\xd0\xbe \xd0\xb5\xd1\x89\xd0\xb5")
        (tag ^ ": has yo but missing in esche"));
  run "RU-002 clean no yo present" (fun tag ->
      expect
        (does_not_fire "RU-002" "\xd0\xb5\xd1\x89\xd0\xb5")
        (tag ^ ": no yo at all, no fire"));
  run "RU-002 clean ASCII" (fun tag ->
      expect (does_not_fire "RU-002" "hello world") (tag ^ ": ASCII ok"));

  (* ══════════════════════════════════════════════════════════════════════
     TR-001: TR dotless/dotted I mapping error
     ══════════════════════════════════════════════════════════════════════ *)
  run "TR-001 fires on ASCII I next to Turkish I" (fun tag ->
      expect (fires "TR-001" "I\xc4\xb0") (tag ^ ": ASCII I + Turkish I"));
  run "TR-001 clean no Turkish chars" (fun tag ->
      expect (does_not_fire "TR-001" "Istanbul") (tag ^ ": no Turkish ok"));

  (* ══════════════════════════════════════════════════════════════════════
     ZH-002: ZH-Hant quotes consistency
     ══════════════════════════════════════════════════════════════════════ *)
  run "ZH-002 fires on mixed CJK+western quotes" (fun tag ->
      expect
        (fires "ZH-002"
           "\xe3\x80\x8c\xe4\xb8\xad\xe3\x80\x8d \xe2\x80\x9cen\xe2\x80\x9d")
        (tag ^ ": CJK corner + western"));
  run "ZH-002 clean CJK only" (fun tag ->
      expect
        (does_not_fire "ZH-002" "\xe3\x80\x8c\xe4\xb8\xad\xe3\x80\x8d")
        (tag ^ ": CJK only ok"));
  run "ZH-002 clean ASCII" (fun tag ->
      expect (does_not_fire "ZH-002" "plain text") (tag ^ ": ASCII ok"));

  (* ══════════════════════════════════════════════════════════════════════
     VERB-014: Code block inside caption
     ══════════════════════════════════════════════════════════════════════ *)
  run "VERB-014 fires on lstlisting in caption" (fun tag ->
      expect
        (fires "VERB-014"
           "\\caption{Some \\begin{lstlisting}code\\end{lstlisting}}")
        (tag ^ ": lstlisting in caption"));
  run "VERB-014 fires on verb in caption" (fun tag ->
      expect
        (fires "VERB-014" "\\caption{Use \\verb|x|}")
        (tag ^ ": verb in caption"));
  run "VERB-014 clean caption" (fun tag ->
      expect
        (does_not_fire "VERB-014" "\\caption{Normal text}")
        (tag ^ ": normal caption ok"));
  run "VERB-014 clean no caption" (fun tag ->
      expect
        (does_not_fire "VERB-014" "\\begin{lstlisting}code\\end{lstlisting}")
        (tag ^ ": code outside caption ok"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-064: Use of eqalign obsolete
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-064 fires on eqalign" (fun tag ->
      expect (fires "MATH-064" "\\eqalign{x &= y}") (tag ^ ": has eqalign"));
  run "MATH-064 count=2" (fun tag ->
      expect
        (fires_with_count "MATH-064" "\\eqalign{a} \\eqalign{b}" 2)
        (tag ^ ": count=2"));
  run "MATH-064 clean" (fun tag ->
      expect
        (does_not_fire "MATH-064" "\\begin{align}x\\end{align}")
        (tag ^ ": align ok"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-102: Legacy eqnarray environment
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-102 fires on eqnarray" (fun tag ->
      expect
        (fires "MATH-102" "\\begin{eqnarray}x\\end{eqnarray}")
        (tag ^ ": has eqnarray"));
  run "MATH-102 clean eqnarray*" (fun tag ->
      expect
        (does_not_fire "MATH-102" "\\begin{eqnarray*}x\\end{eqnarray*}")
        (tag ^ ": starred ok"));
  run "MATH-102 clean align" (fun tag ->
      expect
        (does_not_fire "MATH-102" "\\begin{align}x\\end{align}")
        (tag ^ ": align ok"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-107: Mix of le and leqslant
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-107 fires on mixed" (fun tag ->
      expect
        (fires "MATH-107" "$a \\le b$ and $c \\leqslant d$")
        (tag ^ ": mixed le+leqslant"));
  run "MATH-107 clean le only" (fun tag ->
      expect (does_not_fire "MATH-107" "$a \\le b$") (tag ^ ": le only ok"));
  run "MATH-107 clean leqslant only" (fun tag ->
      expect
        (does_not_fire "MATH-107" "$a \\leqslant b$")
        (tag ^ ": leqslant only ok"));

  (* ══════════════════════════════════════════════════════════════════════
     L3-008: Expl3 module lacks ProvidesExplPackage
     ══════════════════════════════════════════════════════════════════════ *)
  run "L3-008 fires when ExplSyntaxOn without Provides" (fun tag ->
      expect
        (fires "L3-008" "\\ExplSyntaxOn\n\\cs_new:Npn \\foo {}")
        (tag ^ ": no provides"));
  run "L3-008 clean with Provides" (fun tag ->
      expect
        (does_not_fire "L3-008" "\\ProvidesExplPackage{foo}\n\\ExplSyntaxOn")
        (tag ^ ": has provides"));
  run "L3-008 clean no expl3" (fun tag ->
      expect
        (does_not_fire "L3-008" "\\documentclass{article}")
        (tag ^ ": no expl3 ok"));

  (* ══════════════════════════════════════════════════════════════════════
     L3-010: ExplSyntaxOff missing at end of file
     ══════════════════════════════════════════════════════════════════════ *)
  run "L3-010 fires when On without Off" (fun tag ->
      expect
        (fires "L3-010" "\\ExplSyntaxOn\n\\cs_new:Npn \\foo {}")
        (tag ^ ": on without off"));
  run "L3-010 clean with Off" (fun tag ->
      expect
        (does_not_fire "L3-010"
           "\\ExplSyntaxOn\n\\cs_new:Npn \\foo {}\n\\ExplSyntaxOff")
        (tag ^ ": has off"));
  run "L3-010 clean no expl3" (fun tag ->
      expect
        (does_not_fire "L3-010" "\\documentclass{article}")
        (tag ^ ": no expl3 ok"));

  (* ══════════════════════════════════════════════════════════════════════
     REF-011: autoref used without hyperref/cleveref
     ══════════════════════════════════════════════════════════════════════ *)
  run "REF-011 fires on autoref without hyperref" (fun tag ->
      expect
        (fires "REF-011" "See \\autoref{fig:x}")
        (tag ^ ": autoref no hyperref"));
  run "REF-011 clean with hyperref" (fun tag ->
      expect
        (does_not_fire "REF-011" "\\usepackage{hyperref}\nSee \\autoref{fig:x}")
        (tag ^ ": has hyperref"));
  run "REF-011 clean no autoref" (fun tag ->
      expect
        (does_not_fire "REF-011" "See \\ref{fig:x}")
        (tag ^ ": no autoref ok"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-050: Inconsistent title-case capitalisation
     ══════════════════════════════════════════════════════════════════════ *)
  run "TYPO-050 fires on mixed case sections" (fun tag ->
      expect
        (fires "TYPO-050"
           "\\section{The Quick Brown Fox}\n\\section{A lowercase title}")
        (tag ^ ": mixed title/sentence case"));
  run "TYPO-050 clean uniform title case" (fun tag ->
      expect
        (does_not_fire "TYPO-050"
           "\\section{The Quick Brown Fox}\n\\section{Another Title Here}")
        (tag ^ ": uniform title case"));
  run "TYPO-050 clean single section" (fun tag ->
      expect
        (does_not_fire "TYPO-050" "\\section{Only One}")
        (tag ^ ": single section ok"));

  (* ─── summary ─────────────────────────────────────────────────────── *)
  Printf.printf "[stragglers2] PASS %d cases\n%!" !cases;
  if !fails > 0 then (
    Printf.eprintf "[stragglers2] %d FAILURES\n%!" !fails;
    exit 1)
