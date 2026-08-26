(** Unit tests for [Compile_gate_checks] — the precise structural-fatal
    compile-gate detectors.

    For EACH detector we assert:
    - it FIRES on the genuinely-fatal trigger(s) (pdflatex → no PDF), and
    - it does NOT fire on EACH compiling counter-example (nested/grouped
      scripts, escaped &, & inside legal alignment envs, commented-out,
      verbatim, \verb).

    Every boundary here was pinned empirically against
    /Library/TeX/texbin/pdflatex (see the STEP prompt's transcript). *)

open Latex_parse_lib
open Test_helpers

let fires f src = f src <> None
let not_fires f src = f src = None

let doc body =
  "\\documentclass{article}\n\\begin{document}\n" ^ body ^ "\n\\end{document}\n"

(* ── Detector (1): double super/subscript ───────────────────────────────── *)
let () =
  let f = Compile_gate_checks.double_script_fatal in
  (* FATAL triggers *)
  run "dbl-sup x^a^b fires" (fun t -> expect (fires f (doc "$x^a^b$")) t);
  run "dbl-sub x_a_b fires" (fun t -> expect (fires f (doc "$x_a_b$")) t);
  run "sup-then-prime x^a' fires" (fun t -> expect (fires f (doc "$x^a'$")) t);
  run "sup-then-prime-grp x^{a}' fires" (fun t ->
      expect (fires f (doc "$x^{a}'$")) t);
  run "three sup x^a^b^c fires" (fun t -> expect (fires f (doc "$x^a^b^c$")) t);
  run "space between x^a ^b fires" (fun t ->
      expect (fires f (doc "$x^a ^b$")) t);
  run "grp sup x^{a}^{b} fires" (fun t ->
      expect (fires f (doc "$x^{a}^{b}$")) t);
  run "sup sub sup x^a_b^c fires" (fun t ->
      expect (fires f (doc "$x^a_b^c$")) t);
  run "sub sup sub x_{a}^{b}_{c} fires" (fun t ->
      expect (fires f (doc "$x_{a}^{b}_{c}$")) t);
  run "cmd then sup x^\\alpha^b fires" (fun t ->
      expect (fires f (doc "$x^\\alpha^b$")) t);
  run "display math dbl sup fires" (fun t ->
      expect (fires f (doc "\\[x^a^b\\]")) t);
  run "align env dbl sup fires" (fun t ->
      expect (fires f (doc "\\begin{align}x^a^b\\end{align}")) t);
  (* COMPILING counter-examples — must NOT fire *)
  run "nested x^{a^b} ok" (fun t -> expect (not_fires f (doc "$x^{a^b}$")) t);
  run "grouped {x^a}^b ok" (fun t -> expect (not_fires f (doc "${x^a}^b$")) t);
  run "mixed x^a_b ok" (fun t -> expect (not_fires f (doc "$x^a_b$")) t);
  run "mixed x_a^b ok" (fun t -> expect (not_fires f (doc "$x_a^b$")) t);
  run "braced x^{a}_{b} ok" (fun t ->
      expect (not_fires f (doc "$x^{a}_{b}$")) t);
  run "prime then caret x''^b ok" (fun t ->
      expect (not_fires f (doc "$x''^b$")) t);
  run "prime then sup x'^b ok" (fun t -> expect (not_fires f (doc "$x'^b$")) t);
  run "primes only x''' ok" (fun t -> expect (not_fires f (doc "$x'''$")) t);
  run "sub then prime x_a' ok" (fun t -> expect (not_fires f (doc "$x_a'$")) t);
  run "adjacent bases x^a y^b ok" (fun t ->
      expect (not_fires f (doc "$x^a y^b$")) t);
  run "reset by group x^a{}^b ok" (fun t ->
      expect (not_fires f (doc "$x^a{}^b$")) t);
  run "deep nest x^{y^{z^w}} ok" (fun t ->
      expect (not_fires f (doc "$x^{y^{z^w}}$")) t);
  run "int limits x_a^b ok" (fun t ->
      expect (not_fires f (doc "$\\int_a^b x$")) t);
  run "frac two bases ok" (fun t ->
      expect (not_fires f (doc "$\\frac{x^a}{y^b}$")) t);
  run "two braced bases a^{b}c^{d} ok" (fun t ->
      expect (not_fires f (doc "$a^{b}c^{d}$")) t);
  run "nested sub x_{a_{b}} ok" (fun t ->
      expect (not_fires f (doc "$x_{a_{b}}$")) t);
  run "sum sub then sup ok" (fun t ->
      expect (not_fires f (doc "$\\sum_{i}^{n} a_i$")) t);
  (* fatal: A^i_j^k inside align (two supers on A) *)
  run "align A^i_j^k fires" (fun t ->
      expect (fires f (doc "\\begin{align}A^i_j^k\\end{align}")) t);
  (* NOT in math: ^ outside math is not a superscript here (no fire) *)
  run "caret outside math not flagged" (fun t ->
      expect (not_fires f (doc "text a^b^c not math")) t);
  (* comment-aware: dbl sup inside a comment must NOT fire *)
  run "dbl sup in comment ok" (fun t ->
      expect (not_fires f (doc "% $x^a^b$ commented\ntext")) t);
  (* verbatim-aware: dbl sup inside verbatim must NOT fire *)
  run "dbl sup in verbatim ok" (fun t ->
      expect (not_fires f (doc "\\begin{verbatim}$x^a^b$\\end{verbatim}")) t);
  (* SOUNDNESS: extreme brace nesting past the OLD fixed 4096-frame cap. A real
     x^a^b at the bottom of a 5000-deep group MUST still fire (growable frame
     stack, no silent bail⇒false-READY). *)
  let deep = 5000 in
  let deep_fatal =
    doc ("$" ^ String.make deep '{' ^ "x^a^b" ^ String.make deep '}' ^ "$")
  in
  run "deep-nested (>4096) real dbl sup fires" (fun t ->
      expect (fires f deep_fatal) t);
  (* and a deep-nested COMPILING form (nested single scripts) must NOT fire —
     zero over-rejection past the old cap. *)
  let deep_ok =
    doc ("$" ^ String.make deep '{' ^ "x^a" ^ String.make deep '}' ^ "$")
  in
  run "deep-nested (>4096) single sup ok" (fun t ->
      expect (not_fires f deep_ok) t);
  ()

(* Detector (2) — misplaced alignment tab `&` — was DROPPED from the gate (it
   cannot be made over-rejection-free without macro expansion; see
   compile_gate_checks.mli). We assert here that the GATE does NOT fire on the
   real-paper `&` patterns that motivated dropping it, so any future re-addition
   that regresses over-rejection is caught. *)
let () =
  let g = Compile_gate_checks.structural_fatal_reasons in
  let no_amp_reason src =
    not
      (List.exists
         (fun r ->
           let needle = "alignment tab" in
           let ls = String.length r and ln = String.length needle in
           let rec scan i =
             if i + ln > ls then false
             else if String.sub r i ln = needle then true
             else scan (i + 1)
           in
           scan 0)
         (g src))
  in
  run "gate ignores & in tabular" (fun t ->
      expect (no_amp_reason (doc "\\begin{tabular}{ll}a & b\\end{tabular}")) t);
  run "gate ignores & in label (compiles)" (fun t ->
      expect (no_amp_reason (doc "$x$ \\label{eq:spaces&diag}")) t);
  run "gate ignores custom-env & (\\bea shortcut, compiles)" (fun t ->
      expect (no_amp_reason (doc "\\bea a & b \\eea")) t);
  run "gate ignores bare & in text (dropped detector)" (fun t ->
      expect (no_amp_reason (doc "a & b")) t);
  (* moving-argument range coverage: label with _ inside math env must be immune
     (this was the real double-subscript over-rejection). *)
  run "label with underscores in align not a double subscript" (fun t ->
      expect
        (not_fires Compile_gate_checks.double_script_fatal
           (doc "\\begin{align}\\label{eq:BSDE_P_W} x&=y\\end{align}"))
        t);
  run "ref with underscores in inline math immune" (fun t ->
      expect
        (not_fires Compile_gate_checks.double_script_fatal
           (doc "$a$ see \\eqref{eq:def_A_gamma}"))
        t);
  (* REGRESSION (corpus scan, Article 015): a commented-out line carrying an
     UNBALANCED `$$`/`$` desynchronises find_math_ranges' display-math pairing
     and spills a fake math range over the following prose; a custom \ref-alias
     in that prose (\reff{def_S_tilde}) then reads as a double subscript. The
     comment-blanked math computation must prevent this — pdflatex compiles the
     real file. *)
  run "commented unbalanced $$ does not spill math onto \\reff key" (fun t ->
      expect
        (not_fires Compile_gate_checks.double_script_fatal
           (doc
              "\\def\\reff#1{{\\ref{#1}}}\n\
               %$$a_b_c$$\n\
               $$x=y$$\n\
               Then \\reff{def_S_tilde} holds."))
        t);
  (* REGRESSION (corpus scan, 2507.09077 main_arXiv): a user-defined \ref-alias
     (\newcommand{\Eqn}[1]{{(\ref{eq:#1})}}) used INSIDE real math — its
     label-key underscores are not script operators; pdflatex compiles. *)
  run "custom \\newcommand ref-alias inside math immune" (fun t ->
      expect
        (not_fires Compile_gate_checks.double_script_fatal
           (doc
              "\\newcommand{\\Eqn}[1]{{(\\ref{eq:#1})}}\n\
               $x \\gets \\Eqn{ssnl_v_update}$"))
        t);
  run "custom \\def ref-alias inside math immune" (fun t ->
      expect
        (not_fires Compile_gate_checks.double_script_fatal
           (doc "\\def\\myref#1{\\eqref{#1}}\n$z = \\myref{a_b_c}$"))
        t);
  (* SOUNDNESS GUARD: a genuine math-typesetting macro (\mathrm) is NOT a
     ref-alias, so a real double superscript inside it must STILL fire. *)
  run "double superscript inside \\mathrm still fires" (fun t ->
      expect
        (fires Compile_gate_checks.double_script_fatal (doc "$\\mathrm{x^a^b}$"))
        t);
  ()

(* ── Detector (3): no \documentclass ────────────────────────────────────── *)
let () =
  let f = Compile_gate_checks.no_documentclass_fatal in
  run "no documentclass fires" (fun t ->
      expect (fires f "\\begin{document}hello\\end{document}") t);
  run "documentclass only in comment fires" (fun t ->
      expect
        (fires f "%\\documentclass{article}\n\\begin{document}hi\\end{document}")
        t);
  run "documentclass present ok" (fun t -> expect (not_fires f (doc "hello")) t);
  run "documentstyle present ok" (fun t ->
      expect
        (not_fires f
           "\\documentstyle{article}\\begin{document}hi\\end{document}")
        t);
  ()

(* ── Detector (4): \usepackage after \begin{document} ───────────────────── *)
let () =
  let f = Compile_gate_checks.usepackage_after_begin_fatal in
  run "usepackage after begin fires" (fun t ->
      expect (fires f (doc "\\usepackage{amsmath}x")) t);
  run "usepackage in preamble ok" (fun t ->
      expect
        (not_fires f
           "\\documentclass{article}\\usepackage{amsmath}\\begin{document}x\\end{document}")
        t);
  run "usepackage after begin but commented ok" (fun t ->
      expect (not_fires f (doc "% \\usepackage{amsmath}\nx")) t);
  run "usepackage after begin in verbatim ok" (fun t ->
      expect
        (not_fires f (doc "\\begin{verbatim}\\usepackage{x}\\end{verbatim}"))
        t);
  ()

(* ── Detector (8): duplicate \begin{document} (R7-2) ────────────────────── *)
let () =
  let f = Compile_gate_checks.duplicate_begin_document_fatal in
  (* [doc] already wraps ONE \begin{document}; a second in the body ⇒ 2 ⇒ fires
     ("! LaTeX Error: Can be used only in preamble", pdflatex exit 1). *)
  run "duplicate begin{document} fires" (fun t ->
      expect (fires f (doc "Hi.\\begin{document}Again.")) t);
  run "single begin{document} ok" (fun t ->
      expect (not_fires f (doc "just one body")) t);
  run "second begin{document} commented ok" (fun t ->
      expect (not_fires f (doc "Hi.\n% \\begin{document}\nx")) t);
  run "second begin{document} in verbatim ok" (fun t ->
      expect
        (not_fires f (doc "\\begin{verbatim}\\begin{document}\\end{verbatim}"))
        t);
  ()

(* ── Detector (9): \verb broken across a line (R7-2) ─────────────────────── *)
let () =
  let f = Compile_gate_checks.verb_broken_eol_fatal in
  run "verb broken across line fires" (fun t ->
      expect (fires f (doc "Some \\verb|code\nmore| text.")) t);
  run "verb* broken across line fires" (fun t ->
      expect (fires f (doc "\\verb*+a\nb+")) t);
  run "verb closed on same line ok" (fun t ->
      expect (not_fires f (doc "inline \\verb|code| here")) t);
  run "verb in math closed same line ok" (fun t ->
      expect (not_fires f (doc "$\\verb|x|$ then")) t);
  run "broken verb inside verbatim env ok" (fun t ->
      expect
        (not_fires f (doc "\\begin{verbatim}\\verb|a\nb|\\end{verbatim}"))
        t);
  run "broken verb inside comment ok" (fun t ->
      expect (not_fires f (doc "% \\verb|a\nreal line")) t);
  run "verbatiminput prefix not treated as verb" (fun t ->
      expect (not_fires f (doc "\\verbatiminput{f}\nmore")) t);
  ()

(* ── \hyperref link-text is TYPESET, not a moving-arg key (R7-7) ──────────
   \hyperref[l]{link text} re-typesets its brace group, so a genuine
   double-superscript inside it is fatal and MUST fire; the [l] reference key is
   an optional arg (never a math range) so it stays immune. *)
let () =
  let f = Compile_gate_checks.double_script_fatal in
  run "double superscript in \\hyperref link text fires" (fun t ->
      expect (fires f (doc "\\hyperref[x]{$a^b^c$}")) t);
  run "single superscript in \\hyperref link text ok" (fun t ->
      expect (not_fires f (doc "\\hyperref[x]{text $y^2$ here}")) t);
  run "underscore in \\hyperref [label] key immune" (fun t ->
      expect (not_fires f (doc "\\hyperref[eq:a_b_c]{see it}")) t);
  ()

(* ── Combined entry: structural_fatal_reasons ───────────────────────────── *)
let () =
  run "combined: clean doc yields no reasons" (fun t ->
      expect
        (Compile_gate_checks.structural_fatal_reasons (doc "$x^a_b$") = [])
        t);
  run "combined: fatal doc yields >=1 reason" (fun t ->
      expect
        (List.length
           (Compile_gate_checks.structural_fatal_reasons (doc "$x^a^b$"))
        >= 1)
        t);
  ()

(* ── DWR-3a: \iffalse dead spans in no_live_end_document_fatal ─────────────
   fr_end_in_iffalse was a false-READY: the only \end{document} sits inside
   \iffalse...\fi, so TeX never executes it and emergency-stops, while the
   detector found the string and reported READY. Tested through the exported
   structural_fatal_reasons because the detector itself is internal.

   The counter-examples matter more than the positive case: this arm can only
   make the detector fire MORE, so every risk here is over-rejection, and a real
   paper that uses \iffalse to comment out a block must stay READY. *)
let () =
  let fatal src =
    List.length (Compile_gate_checks.structural_fatal_reasons src) >= 1
  in
  run "end{document} only inside \\iffalse..\\fi is FATAL" (fun t ->
      expect
        (fatal
           "\\documentclass{article}\n\
            \\begin{document}\n\
            Hi.\n\
            \\iffalse\n\
            \\end{document}\n\
            \\fi\n")
        t);
  run "a LIVE end{document} after an \\iffalse block is fine" (fun t ->
      expect
        (not
           (fatal
              "\\documentclass{article}\n\
               \\begin{document}\n\
               \\iffalse\n\
               dead\n\
               \\fi\n\
               Hi.\n\
               \\end{document}\n"))
        t);
  run "\\iffalse block BEFORE the end is fine (the common comment-out shape)"
    (fun t ->
      expect
        (not
           (fatal
              "\\documentclass{article}\n\
               \\begin{document}\n\
               \\iffalse\n\
               \\section{old}\n\
               \\fi\n\
               text\n\
               \\end{document}\n"))
        t);
  run "\\else terminates the dead span, so the else-branch is live" (fun t ->
      expect
        (not
           (fatal
              "\\documentclass{article}\n\
               \\begin{document}\n\
               \\iffalse\n\
               dead\n\
               \\else\n\
               \\end{document}\n\
               \\fi\n"))
        t);
  run "\\iffalse inside a brace group is a definition body, not a conditional"
    (fun t ->
      (* \newcommand{\hidden}{\iffalse} must NOT start a dead span, or a live
         \end{document} after it would be wrongly called dead. *)
      expect
        (not
           (fatal
              "\\documentclass{article}\n\
               \\newcommand{\\hidden}{\\iffalse}\n\
               \\begin{document}\n\
               Hi.\n\
               \\end{document}\n"))
        t);
  run "\\fill must not be read as \\fi (control-word boundary)" (fun t ->
      expect
        (not
           (fatal
              "\\documentclass{article}\n\
               \\begin{document}\n\
               \\hspace{\\fill}\n\
               Hi.\n\
               \\end{document}\n"))
        t);
  ()

(* ── thmtools shared-counter collision (OPEN-002) ───────────────────────── The
   largest real-paper false-READY class: 8 of the 8 recorded flip on this
   detector. Every case below mirrors a pdflatex-verified vector (16/16 agree
   with the rule under the pin; the FATAL ones die with "! LaTeX Error: Command
   \c@lemma already defined", the NOT-FATAL ones are rc 0).

   Tested directly rather than through [structural_fatal_reasons]: the detector
   deliberately lives OUTSIDE that list so the caller can hand it the
   CLOSURE-RESOLVED source (the load and the declarations routinely live in
   different files); these unit cases exercise the pure string function, and the
   closure path is pinned by the fr_thmtools_child_load tree fixture.

   The NEGATIVES matter more than the positives: the held-out validation was FP
   0/30, and every case here that must stay silent is an over-rejection if it
   ever fires. *)
let () =
  let fires body =
    Compile_gate_checks.thmtools_counter_collision_fatal
      ("\\documentclass{article}\n"
      ^ body
      ^ "\n\\begin{document}\nBody.\n\\end{document}\n")
    <> None
  in
  let shared =
    "\\newtheorem{theorem}{Theorem}\n\\newtheorem{lemma}[theorem]{Lemma}"
  in
  run "thmtools + shared counter is FATAL" (fun t ->
      expect (fires ("\\usepackage{thmtools}\n" ^ shared)) t);
  run "thm-restate variant is FATAL" (fun t ->
      expect (fires ("\\usepackage{thm-restate}\n" ^ shared)) t);
  run "comma-list load position counts" (fun t ->
      expect (fires ("\\usepackage{amsmath,thmtools,graphicx}\n" ^ shared)) t);
  run "\\declaretheorem sibling= is FATAL" (fun t ->
      expect
        (fires
           "\\usepackage{thmtools}\n\
            \\declaretheorem{theorem}\n\
            \\declaretheorem[sibling=theorem]{lemma}")
        t);
  run "\\declaretheorem numberlike= is FATAL" (fun t ->
      expect
        (fires
           "\\usepackage{thmtools}\n\
            \\declaretheorem{theorem}\n\
            \\declaretheorem[numberlike=theorem]{lemma}")
        t);
  run "amsthm BEFORE thmtools does not rescue" (fun t ->
      expect
        (fires ("\\usepackage{amsthm}\n\\usepackage{thmtools}\n" ^ shared))
        t);
  run "\\RequirePackage spelling is FATAL" (fun t ->
      expect (fires ("\\RequirePackage{thmtools}\n" ^ shared)) t);
  run "[section] suffix on the PARENT still fires on the shared child" (fun t ->
      expect
        (fires
           "\\usepackage{thmtools}\n\
            \\newtheorem{theorem}{Theorem}[section]\n\
            \\newtheorem{lemma}[theorem]{Lemma}")
        t);
  (* ── the rescues and non-cases: every one is an over-rejection if it fires *)
  run "amsthm AFTER thmtools RESCUES" (fun t ->
      expect
        (not
           (fires ("\\usepackage{thmtools}\n\\usepackage{amsthm}\n" ^ shared)))
        t);
  run "own counters are fine" (fun t ->
      expect
        (not (fires "\\usepackage{thmtools}\n\\newtheorem{lemma}{Lemma}"))
        t);
  run "commented-out load must NOT fire" (fun t ->
      expect (not (fires ("% \\usepackage{thmtools}\n" ^ shared))) t);
  run "declarations BEFORE the load are fine" (fun t ->
      expect (not (fires (shared ^ "\n\\usepackage{thmtools}"))) t);
  run "numberwithin= is the PARENT form, not shared" (fun t ->
      expect
        (not
           (fires
              "\\usepackage{thmtools}\n\
               \\declaretheorem[numberwithin=section]{theorem}"))
        t);
  run "parent-form suffix alone is fine" (fun t ->
      expect
        (not
           (fires
              "\\usepackage{thmtools}\n\\newtheorem{theorem}{Theorem}[section]"))
        t);
  run "no thmtools at all: plain shared counters are fine" (fun t ->
      expect (not (fires shared)) t);
  run "load inside verbatim must NOT fire" (fun t ->
      expect
        (not
           (fires
              ("\\begin{verbatim}\\usepackage{thmtools}\\end{verbatim}\n"
              ^ shared)))
        t);
  run "\\declaretheoremstyle is not \\declaretheorem" (fun t ->
      expect
        (not
           (fires
              "\\usepackage{thmtools}\n\
               \\declaretheoremstyle[bodyfont=\\itshape]{mystyle}"))
        t);
  run "the pattern AFTER \\begin{document} does not fire (preamble-only)"
    (fun t ->
      expect
        (Compile_gate_checks.thmtools_counter_collision_fatal
           ("\\documentclass{article}\n\
             \\begin{document}\n\
             \\usepackage{thmtools}\n"
           ^ shared
           ^ "\n\\end{document}\n")
        = None)
        t);
  run "the message is version-conditioned prose with no scrapeable token"
    (fun t ->
      match
        Compile_gate_checks.thmtools_counter_collision_fatal
          ("\\documentclass{article}\n\\usepackage{thmtools}\n"
          ^ shared
          ^ "\n\\begin{document}\nB.\n\\end{document}\n")
      with
      | None -> expect false (t ^ ": detector must fire here")
      | Some m ->
          let contains sub =
            let n = String.length m and k = String.length sub in
            let rec go i =
              i + k <= n && (String.sub m i k = sub || go (i + 1))
            in
            go 0
          in
          (* diff_real_roots.py scrapes reasons with \b([A-Z]{2,8}-\d{3})\b — a
             fabricated token here would pollute cli_reasons attribution. The
             hyphen-digit shape only arises from ALLCAPS-### ids, so checking
             for an uppercase letter directly before "-0/-1/-2" is a sufficient
             tripwire for this message. *)
          let has_id_token =
            let n = String.length m in
            let rec go i =
              if i + 2 >= n then false
              else if
                m.[i] >= 'A'
                && m.[i] <= 'Z'
                && m.[i + 1] = '-'
                && m.[i + 2] >= '0'
                && m.[i + 2] <= '9'
              then true
              else go (i + 1)
            in
            go 0
          in
          expect
            ((not has_id_token)
            && contains "TeX Live"
            && contains "amsthm AFTER thmtools")
            (t ^ ": version condition + fix line, no RULE-123 tokens"))

let () =
  run "a document-derived name cannot leak a scrapeable token" (fun t ->
      (* diff_real_roots scrapes stdout for T<digit> / ALLCAPS-### tokens. A
         theorem the author called FIG-001 must not inject a phantom rule-id
         into cli_reasons — the message lowercases the interpolated name.
         Measured end-to-end before the guard existed: ['FIG-001'] leaked. *)
      let src =
        String.concat "\n"
          [
            "\\documentclass{article}";
            "\\usepackage{thmtools}";
            "\\newtheorem{thm}{Theorem}";
            "\\newtheorem{FIG-001}[thm]{Bad}";
            "\\begin{document}";
            "B.";
            "\\end{document}";
          ]
      in
      match Compile_gate_checks.thmtools_counter_collision_fatal src with
      | None -> expect false (t ^ ": detector must fire on FIG-001[thm]")
      | Some m ->
          let has_id_token =
            let n = String.length m in
            let rec go i =
              if i + 2 >= n then false
              else if
                m.[i] >= 'A'
                && m.[i] <= 'Z'
                && m.[i + 1] = '-'
                && m.[i + 2] >= '0'
                && m.[i + 2] <= '9'
              then true
              else go (i + 1)
            in
            go 0
          in
          expect (not has_id_token)
            (t ^ ": interpolated name must be scrape-inert"))

(* ── Self-collision family (SC-A duplicate theorem, SC-B theH-star) ──────
   Every fatal/compiling boundary below was pinned against the pin (and the
   family is engine-independent — the anchors fail under TL2024 identically).
   The scanner is exercised through the same composition the caller uses: scan
   segments (with carried per-file state where relevant), then verdict.

   The NEGATIVES carry the weight: 165 of 165 real-world same-name duplicates
   are guard-managed and COMPILE, so a guard the scanner misses is an
   over-rejection on a real paper. *)
let () =
  let verdict segs =
    let open Compile_gate_checks in
    let _, evs =
      List.fold_left
        (fun (st, acc) seg ->
          let st', e = sc_scan_segment st seg in
          (st', acc @ e))
        (sc_initial, []) segs
    in
    self_collision_verdict evs
  in
  let fires segs = verdict segs <> None in
  run "SC-A: plain kernel \\newtheorem twice is FATAL" (fun t ->
      expect
        (fires [ "\\newtheorem{lem}{Lemma}\n\\newtheorem{lem}{Lemma}\n" ])
        t);
  run "SC-A: \\declaretheorem then \\newtheorem same name is FATAL" (fun t ->
      expect (fires [ "\\declaretheorem{lem}\n\\newtheorem{lem}{Lemma}\n" ]) t);
  run "SC-A: \\if-guarded duplicate must NOT fire" (fun t ->
      expect
        (not
           (fires
              [
                "\\newtheorem{lem}{Lemma}\n\
                 \\ifdefined\\undefzz\\newtheorem{lem}{Lemma}\\fi\n";
              ]))
        t);
  run "SC-A: brace-guarded duplicate must NOT fire" (fun t ->
      expect
        (not
           (fires
              [
                "\\newtheorem{lem}{Lemma}\n\
                 \\@ifundefined{c@lem}{\\newtheorem{lem}{Lemma}}{}\n";
              ]))
        t);
  run "SC-A: two different names are fine" (fun t ->
      expect
        (not (fires [ "\\newtheorem{lem}{Lemma}\n\\newtheorem{thm}{Thm}\n" ]))
        t);
  run "SC-A: \\newtheorem* duplicate also fires" (fun t ->
      expect
        (fires [ "\\newtheorem{lem}{Lemma}\n\\newtheorem*{lem}{Lemma}\n" ])
        t);
  run "SC-B: \\newcommand{\\theH<x>} AFTER the counter is FATAL" (fun t ->
      expect
        (fires
           [
             "\\usepackage{algorithm}\n\
              \\newcommand{\\theHalgorithm}{\\arabic{algorithm}}\n";
           ])
        t);
  run "SC-B: \\newcounter creator counts" (fun t ->
      expect (fires [ "\\newcounter{myctr}\n\\newcommand{\\theHmyctr}{x}\n" ]) t);
  run "SC-B: \\renewcommand NEVER fires (documented spelling)" (fun t ->
      expect
        (not
           (fires
              [
                "\\usepackage{algorithm}\n\\renewcommand{\\theHalgorithm}{x}\n";
              ]))
        t);
  run "SC-B: \\providecommand never fires" (fun t ->
      expect
        (not
           (fires
              [
                "\\usepackage{algorithm}\n\
                 \\providecommand{\\theHalgorithm}{x}\n";
              ]))
        t);
  run "SC-B: definition BEFORE the counter compiles — order is the rule"
    (fun t ->
      expect
        (not
           (fires
              [ "\\newcommand{\\theHalgorithm}{x}\n\\usepackage{algorithm}\n" ]))
        t);
  run "SC-B: comma-list creator load counts" (fun t ->
      expect
        (fires
           [
             "\\usepackage{amsmath,algorithm,graphicx}\n\
              \\newcommand{\\theHalgorithm}{x}\n";
           ])
        t);
  (* ── the segment/state contract the caller depends on ── *)
  run "SC: per-file state carries an OPEN guard across segments" (fun t ->
      (* A guard opened in segment 1 must still suppress in segment 2 of the
         SAME file — the caller feeds both through the same carried state. *)
      let open Compile_gate_checks in
      let st1, e1 =
        sc_scan_segment sc_initial "\\newtheorem{lem}{L}\n\\ifdefined\\x\n"
      in
      let _, e2 = sc_scan_segment st1 "\\newtheorem{lem}{L}\n\\fi\n" in
      expect (self_collision_verdict (e1 @ e2) = None) t);
  run "SC: splice order decides SC-B — creator in child, def after in root"
    (fun t ->
      (* root-part1 | child(creates) | root-part2(defines) — must FIRE. *)
      expect
        (fires
           [
             "\\usepackage{myconf}\n";
             "\\RequirePackage{algorithm}\n";
             "\\newcommand{\\theHalgorithm}{x}\n";
           ])
        t);
  run "SC: reverse splice order must NOT fire" (fun t ->
      (* def in root-part1 | child creates after — compiles (verified cell). *)
      expect
        (not
           (fires
              [
                "\\newcommand{\\theHalgorithm}{x}\n";
                "\\RequirePackage{algorithm}\n";
              ]))
        t);
  run "SC: stray \\fi and } clamp at zero, later events still emitted" (fun t ->
      expect
        (fires [ "\\fi }\n\\newtheorem{lem}{L}\n\\newtheorem{lem}{L}\n" ])
        t);
  run "SC messages carry no scrapeable token" (fun t ->
      let check = function
        | None -> false
        | Some m ->
            let n = String.length m in
            let rec go i =
              if i + 2 >= n then true
              else if
                m.[i] >= 'A'
                && m.[i] <= 'Z'
                && m.[i + 1] = '-'
                && m.[i + 2] >= '0'
                && m.[i + 2] <= '9'
              then false
              else go (i + 1)
            in
            go 0
      in
      expect
        (check
           (verdict [ "\\newtheorem{LEM-01x}{L}\n\\newtheorem{LEM-01x}{L}\n" ])
        && check
             (verdict
                [
                  "\\usepackage{algorithm}\n\\newcommand{\\theHalgorithm}{x}\n";
                ]))
        (t ^ ": document-derived names are lowercased"))

let () = finalise "compile_gate"
