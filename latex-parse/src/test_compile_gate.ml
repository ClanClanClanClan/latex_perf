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

let doc body = "\\documentclass{article}\n\\begin{document}\n" ^ body ^ "\n\\end{document}\n"

(* ── Detector (1): double super/subscript ───────────────────────────────── *)
let () =
  let f = Compile_gate_checks.double_script_fatal in
  (* FATAL triggers *)
  run "dbl-sup x^a^b fires" (fun t ->
      expect (fires f (doc "$x^a^b$")) t);
  run "dbl-sub x_a_b fires" (fun t -> expect (fires f (doc "$x_a_b$")) t);
  run "sup-then-prime x^a' fires" (fun t ->
      expect (fires f (doc "$x^a'$")) t);
  run "sup-then-prime-grp x^{a}' fires" (fun t ->
      expect (fires f (doc "$x^{a}'$")) t);
  run "three sup x^a^b^c fires" (fun t ->
      expect (fires f (doc "$x^a^b^c$")) t);
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
      expect
        (fires f (doc "\\begin{align}x^a^b\\end{align}"))
        t);
  (* COMPILING counter-examples — must NOT fire *)
  run "nested x^{a^b} ok" (fun t -> expect (not_fires f (doc "$x^{a^b}$")) t);
  run "grouped {x^a}^b ok" (fun t -> expect (not_fires f (doc "${x^a}^b$")) t);
  run "mixed x^a_b ok" (fun t -> expect (not_fires f (doc "$x^a_b$")) t);
  run "mixed x_a^b ok" (fun t -> expect (not_fires f (doc "$x_a^b$")) t);
  run "braced x^{a}_{b} ok" (fun t ->
      expect (not_fires f (doc "$x^{a}_{b}$")) t);
  run "prime then caret x''^b ok" (fun t ->
      expect (not_fires f (doc "$x''^b$")) t);
  run "prime then sup x'^b ok" (fun t ->
      expect (not_fires f (doc "$x'^b$")) t);
  run "primes only x''' ok" (fun t -> expect (not_fires f (doc "$x'''$")) t);
  run "sub then prime x_a' ok" (fun t ->
      expect (not_fires f (doc "$x_a'$")) t);
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
      expect
        (not_fires f (doc "\\begin{verbatim}$x^a^b$\\end{verbatim}"))
        t);
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
      expect
        (no_amp_reason (doc "$x$ \\label{eq:spaces&diag}"))
        t);
  run "gate ignores custom-env & (\\bea shortcut, compiles)" (fun t ->
      expect (no_amp_reason (doc "\\bea a & b \\eea")) t);
  run "gate ignores bare & in text (dropped detector)" (fun t ->
      expect (no_amp_reason (doc "a & b")) t);
  (* moving-argument range coverage: label with _ inside math env must be
     immune (this was the real double-subscript over-rejection). *)
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
              "\\def\\reff#1{{\\ref{#1}}}\n%$$a_b_c$$\n$$x=y$$\nThen \\reff{def_S_tilde} holds."))
        t);
  (* REGRESSION (corpus scan, 2507.09077 main_arXiv): a user-defined \ref-alias
     (\newcommand{\Eqn}[1]{{(\ref{eq:#1})}}) used INSIDE real math — its
     label-key underscores are not script operators; pdflatex compiles. *)
  run "custom \\newcommand ref-alias inside math immune" (fun t ->
      expect
        (not_fires Compile_gate_checks.double_script_fatal
           (doc
              "\\newcommand{\\Eqn}[1]{{(\\ref{eq:#1})}}\n$x \\gets \\Eqn{ssnl_v_update}$"))
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
        (fires Compile_gate_checks.double_script_fatal
           (doc "$\\mathrm{x^a^b}$"))
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
  run "documentclass present ok" (fun t ->
      expect (not_fires f (doc "hello")) t);
  run "documentstyle present ok" (fun t ->
      expect
        (not_fires f "\\documentstyle{article}\\begin{document}hi\\end{document}")
        t);
  ()

(* ── Detector (4): \usepackage after \begin{document} ───────────────────── *)
let () =
  let f = Compile_gate_checks.usepackage_after_begin_fatal in
  run "usepackage after begin fires" (fun t ->
      expect
        (fires f (doc "\\usepackage{amsmath}x"))
        t);
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

(* ── Combined entry: structural_fatal_reasons ───────────────────────────── *)
let () =
  run "combined: clean doc yields no reasons" (fun t ->
      expect (Compile_gate_checks.structural_fatal_reasons (doc "$x^a_b$") = []) t);
  run "combined: fatal doc yields >=1 reason" (fun t ->
      expect
        (List.length (Compile_gate_checks.structural_fatal_reasons (doc "$x^a^b$"))
        >= 1)
        t);
  ()

let () = finalise "compile_gate"
