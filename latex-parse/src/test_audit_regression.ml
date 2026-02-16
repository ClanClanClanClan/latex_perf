(** Regression tests for audit-remediation fixes:
    - MATH-063: double-backslash splitting
    - CMD-005: \def\x pattern detection
    - PKG-007/PKG-023/TIKZ-007: first-occurrence position logic
    - FIG-010: subfigure* starred variant
    - DOC-001/DOC-002/DOC-003: article-like class guard *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[audit-regr] FAIL: %s\n%!" msg;
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
     MATH-063: Equation array with > 1 alignment point BUG FIX: was splitting on
     individual '\' instead of '\\' (line break)
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-063 regression: commands with backslash don't cause false positive"
    (fun tag ->
      (* \frac contains backslash but has only 2 & per line — should NOT fire *)
      expect
        (does_not_fire "MATH-063"
           "\\begin{eqnarray}\n\
            \\frac{a}{b} & = & c \\\\\n\
            \\alpha & = & \\beta\n\
            \\end{eqnarray}")
        (tag ^ ": commands with \\ in eqnarray, <=2 & per line"));
  run "MATH-063 regression: genuine >2 & still fires" (fun tag ->
      expect
        (fires "MATH-063"
           "\\begin{eqnarray}\na & b & c & d \\\\\n\\end{eqnarray}")
        (tag ^ ": 3 ampersands on one line"));
  run "MATH-063 regression: exactly 2 & is clean" (fun tag ->
      expect
        (does_not_fire "MATH-063"
           "\\begin{eqnarray}\na & = & b \\\\\nc & = & d\n\\end{eqnarray}")
        (tag ^ ": exactly 2 & per line is fine"));
  run "MATH-063 regression: \\frac with nested braces is clean" (fun tag ->
      expect
        (does_not_fire "MATH-063"
           "\\begin{eqnarray}\n\
            \\frac{\\alpha + \\beta}{\\gamma} & = & \\delta \\\\\n\
            \\sum_{i=1}^{n} x_i & = & S\n\
            \\end{eqnarray}")
        (tag ^ ": many commands, still <=2 & per line"));
  run "MATH-063 regression: count=2 with two bad lines" (fun tag ->
      expect
        (fires_with_count "MATH-063"
           "\\begin{eqnarray}\n\
            a & b & c & d \\\\\n\
            e & f & g & h\n\
            \\end{eqnarray}"
           2)
        (tag ^ ": two lines with 3 &"));
  run "MATH-063 regression: eqnarray* also checked" (fun tag ->
      expect
        (fires "MATH-063" "\\begin{eqnarray*}\na & b & c & d\n\\end{eqnarray*}")
        (tag ^ ": starred variant"));

  (* ══════════════════════════════════════════════════════════════════════
     CMD-005: Single-letter macro created BUG FIX: \def\x{body} was not properly
     detected
     ══════════════════════════════════════════════════════════════════════ *)
  run "CMD-005 fires on \\def\\x{body}" (fun tag ->
      expect
        (fires "CMD-005" "\\def\\x{hello}")
        (tag ^ ": def single-letter macro"));
  run "CMD-005 fires on \\def\\x #1{body}" (fun tag ->
      expect
        (fires "CMD-005" "\\def\\x #1{#1 world}")
        (tag ^ ": def with parameter"));
  run "CMD-005 fires on \\newcommand{\\x}" (fun tag ->
      expect
        (fires "CMD-005" "\\newcommand{\\a}{stuff}")
        (tag ^ ": newcommand single letter"));
  run "CMD-005 fires on \\renewcommand{\\y}" (fun tag ->
      expect
        (fires "CMD-005" "\\renewcommand{\\y}{stuff}")
        (tag ^ ": renewcommand single letter"));
  run "CMD-005 clean: \\def\\xy (two letters)" (fun tag ->
      expect
        (does_not_fire "CMD-005" "\\def\\xy{hello}")
        (tag ^ ": two-letter def is fine"));
  run "CMD-005 clean: \\newcommand{\\foo} (multi letter)" (fun tag ->
      expect
        (does_not_fire "CMD-005" "\\newcommand{\\foo}{bar}")
        (tag ^ ": multi-letter newcommand is fine"));
  run "CMD-005 count=2 with mixed patterns" (fun tag ->
      expect
        (fires_with_count "CMD-005" "\\def\\a{one}\n\\newcommand{\\b}{two}" 2)
        (tag ^ ": one def + one newcommand"));

  (* ══════════════════════════════════════════════════════════════════════
     PKG-007: hyperref loaded before geometry — first-occurrence logic BUG FIX:
     was using last-occurrence, now uses first-occurrence
     ══════════════════════════════════════════════════════════════════════ *)
  run "PKG-007 fires when hyperref before geometry" (fun tag ->
      expect
        (fires "PKG-007"
           "\\usepackage{hyperref}\n\
            \\usepackage{geometry}\n\
            \\begin{document}\n\
            \\end{document}")
        (tag ^ ": hyperref first"));
  run "PKG-007 clean when geometry before hyperref" (fun tag ->
      expect
        (does_not_fire "PKG-007"
           "\\usepackage{geometry}\n\
            \\usepackage{hyperref}\n\
            \\begin{document}\n\
            \\end{document}")
        (tag ^ ": geometry first"));
  run "PKG-007 regression: duplicate hyperref, first occurrence matters"
    (fun tag ->
      (* First hyperref is before geometry, second is after — first wins *)
      expect
        (fires "PKG-007"
           "\\usepackage{hyperref}\n\
            \\usepackage{geometry}\n\
            \\usepackage{hyperref}\n\
            \\begin{document}\n\
            \\end{document}")
        (tag ^ ": first hyperref before geometry fires"));
  run "PKG-007 regression: duplicate geometry, first occurrence matters"
    (fun tag ->
      (* First geometry is before hyperref — clean *)
      expect
        (does_not_fire "PKG-007"
           "\\usepackage{geometry}\n\
            \\usepackage{hyperref}\n\
            \\usepackage{geometry}\n\
            \\begin{document}\n\
            \\end{document}")
        (tag ^ ": first geometry before hyperref is clean"));

  (* ══════════════════════════════════════════════════════════════════════
     PKG-023: unicode-math must load before microtype — first-occurrence
     ══════════════════════════════════════════════════════════════════════ *)
  run "PKG-023 fires when unicode-math after microtype" (fun tag ->
      expect
        (fires "PKG-023"
           "\\usepackage{microtype}\n\
            \\usepackage{unicode-math}\n\
            \\begin{document}\n\
            \\end{document}")
        (tag ^ ": unicode-math after microtype"));
  run "PKG-023 clean when unicode-math before microtype" (fun tag ->
      expect
        (does_not_fire "PKG-023"
           "\\usepackage{unicode-math}\n\
            \\usepackage{microtype}\n\
            \\begin{document}\n\
            \\end{document}")
        (tag ^ ": correct order"));
  run "PKG-023 regression: duplicate unicode-math, first occurrence matters"
    (fun tag ->
      expect
        (does_not_fire "PKG-023"
           "\\usepackage{unicode-math}\n\
            \\usepackage{microtype}\n\
            \\usepackage{unicode-math}\n\
            \\begin{document}\n\
            \\end{document}")
        (tag ^ ": first unicode-math before microtype is clean"));

  (* ══════════════════════════════════════════════════════════════════════
     TIKZ-007: TikZ loaded after hyperref — first-occurrence
     ══════════════════════════════════════════════════════════════════════ *)
  run "TIKZ-007 fires when tikz after hyperref" (fun tag ->
      expect
        (fires "TIKZ-007"
           "\\usepackage{hyperref}\n\
            \\usepackage{tikz}\n\
            \\begin{document}\n\
            \\end{document}")
        (tag ^ ": tikz after hyperref"));
  run "TIKZ-007 clean when tikz before hyperref" (fun tag ->
      expect
        (does_not_fire "TIKZ-007"
           "\\usepackage{tikz}\n\
            \\usepackage{hyperref}\n\
            \\begin{document}\n\
            \\end{document}")
        (tag ^ ": tikz before hyperref"));
  run "TIKZ-007 regression: duplicate tikz, first occurrence matters"
    (fun tag ->
      expect
        (does_not_fire "TIKZ-007"
           "\\usepackage{tikz}\n\
            \\usepackage{hyperref}\n\
            \\usepackage{tikz}\n\
            \\begin{document}\n\
            \\end{document}")
        (tag ^ ": first tikz before hyperref is clean"));

  (* ══════════════════════════════════════════════════════════════════════
     FIG-010: Subfigure without \subcaption — starred variant BUG FIX: was not
     checking subfigure* environments
     ══════════════════════════════════════════════════════════════════════ *)
  run "FIG-010 fires on subfigure without subcaption" (fun tag ->
      expect
        (fires "FIG-010"
           "\\begin{figure}\n\
            \\begin{subfigure}{0.5\\textwidth}\n\
            \\includegraphics{a.png}\n\
            \\end{subfigure}\n\
            \\end{figure}")
        (tag ^ ": plain subfigure"));
  run "FIG-010 regression: fires on subfigure* without subcaption" (fun tag ->
      expect
        (fires "FIG-010"
           "\\begin{figure}\n\
            \\begin{subfigure*}{0.5\\textwidth}\n\
            \\includegraphics{a.png}\n\
            \\end{subfigure*}\n\
            \\end{figure}")
        (tag ^ ": starred subfigure"));
  run "FIG-010 clean: subfigure with \\subcaption" (fun tag ->
      expect
        (does_not_fire "FIG-010"
           "\\begin{figure}\n\
            \\begin{subfigure}{0.5\\textwidth}\n\
            \\includegraphics{a.png}\n\
            \\subcaption{A}\n\
            \\end{subfigure}\n\
            \\end{figure}")
        (tag ^ ": has subcaption"));
  run "FIG-010 clean: subfigure* with \\caption" (fun tag ->
      expect
        (does_not_fire "FIG-010"
           "\\begin{figure}\n\
            \\begin{subfigure*}{0.5\\textwidth}\n\
            \\includegraphics{a.png}\n\
            \\caption{A}\n\
            \\end{subfigure*}\n\
            \\end{figure}")
        (tag ^ ": starred with caption"));
  run "FIG-010 count=2 mixed starred and plain" (fun tag ->
      expect
        (fires_with_count "FIG-010"
           "\\begin{figure}\n\
            \\begin{subfigure}{0.5\\textwidth}\n\
            \\includegraphics{a.png}\n\
            \\end{subfigure}\n\
            \\begin{subfigure*}{0.5\\textwidth}\n\
            \\includegraphics{b.png}\n\
            \\end{subfigure*}\n\
            \\end{figure}"
           2)
        (tag ^ ": two missing subcaptions"));

  (* ══════════════════════════════════════════════════════════════════════
     DOC-001: Title missing \maketitle — article-like class guard BUG FIX: was
     firing on all documents, now requires article-like class
     ══════════════════════════════════════════════════════════════════════ *)
  run "DOC-001 fires on article without \\maketitle" (fun tag ->
      expect
        (fires "DOC-001"
           "\\documentclass{article}\n\\begin{document}\nHello\n\\end{document}")
        (tag ^ ": article missing maketitle"));
  run "DOC-001 fires on report without \\maketitle" (fun tag ->
      expect
        (fires "DOC-001"
           "\\documentclass{report}\n\\begin{document}\nHello\n\\end{document}")
        (tag ^ ": report missing maketitle"));
  run "DOC-001 fires on scrartcl without \\maketitle" (fun tag ->
      expect
        (fires "DOC-001"
           "\\documentclass{scrartcl}\n\
            \\begin{document}\n\
            Hello\n\
            \\end{document}")
        (tag ^ ": scrartcl missing maketitle"));
  run "DOC-001 clean: article with \\maketitle" (fun tag ->
      expect
        (does_not_fire "DOC-001"
           "\\documentclass{article}\n\
            \\begin{document}\n\
            \\maketitle\n\
            \\end{document}")
        (tag ^ ": has maketitle"));
  run "DOC-001 regression: beamer without maketitle is clean" (fun tag ->
      expect
        (does_not_fire "DOC-001"
           "\\documentclass{beamer}\n\\begin{document}\nHello\n\\end{document}")
        (tag ^ ": beamer doesn't need maketitle"));
  run "DOC-001 regression: letter without maketitle is clean" (fun tag ->
      expect
        (does_not_fire "DOC-001"
           "\\documentclass{letter}\n\\begin{document}\nHello\n\\end{document}")
        (tag ^ ": letter doesn't need maketitle"));
  run "DOC-001 regression: standalone without maketitle is clean" (fun tag ->
      expect
        (does_not_fire "DOC-001"
           "\\documentclass{standalone}\n\
            \\begin{document}\n\
            Hello\n\
            \\end{document}")
        (tag ^ ": standalone doesn't need maketitle"));
  run "DOC-001 regression: no documentclass at all is clean" (fun tag ->
      expect
        (does_not_fire "DOC-001" "\\begin{document}\nHello\n\\end{document}")
        (tag ^ ": no documentclass is clean"));

  (* ══════════════════════════════════════════════════════════════════════
     DOC-002: Abstract environment missing — article-like class guard
     ══════════════════════════════════════════════════════════════════════ *)
  run "DOC-002 fires on article without abstract" (fun tag ->
      expect
        (fires "DOC-002"
           "\\documentclass{article}\n\
            \\begin{document}\n\
            \\maketitle\n\
            \\end{document}")
        (tag ^ ": article missing abstract"));
  run "DOC-002 clean: article with abstract" (fun tag ->
      expect
        (does_not_fire "DOC-002"
           "\\documentclass{article}\n\
            \\begin{document}\n\
            \\begin{abstract}Text\\end{abstract}\n\
            \\end{document}")
        (tag ^ ": has abstract"));
  run "DOC-002 regression: beamer without abstract is clean" (fun tag ->
      expect
        (does_not_fire "DOC-002"
           "\\documentclass{beamer}\n\
            \\begin{document}\n\
            \\maketitle\n\
            \\end{document}")
        (tag ^ ": beamer doesn't need abstract"));
  run "DOC-002 regression: standalone without abstract is clean" (fun tag ->
      expect
        (does_not_fire "DOC-002"
           "\\documentclass{standalone}\n\\begin{document}\n\\end{document}")
        (tag ^ ": standalone doesn't need abstract"));

  (* ══════════════════════════════════════════════════════════════════════
     DOC-003: Keywords missing — article-like class guard
     ══════════════════════════════════════════════════════════════════════ *)
  run "DOC-003 fires on article without keywords" (fun tag ->
      expect
        (fires "DOC-003"
           "\\documentclass{article}\n\
            \\begin{document}\n\
            \\maketitle\n\
            \\end{document}")
        (tag ^ ": article missing keywords"));
  run "DOC-003 clean: article with keywords" (fun tag ->
      expect
        (does_not_fire "DOC-003"
           "\\documentclass{article}\n\
            \\begin{document}\n\
            \\keywords{test}\n\
            \\end{document}")
        (tag ^ ": has keywords"));
  run "DOC-003 regression: beamer without keywords is clean" (fun tag ->
      expect
        (does_not_fire "DOC-003"
           "\\documentclass{beamer}\n\\begin{document}\n\\end{document}")
        (tag ^ ": beamer doesn't need keywords"));

  (* ─── summary ─────────────────────────────────────────────────────── *)
  Printf.printf "[audit-regr] PASS %d cases\n%!" !cases;
  if !fails > 0 then (
    Printf.eprintf "[audit-regr] %d FAILURES\n%!" !fails;
    exit 1)
