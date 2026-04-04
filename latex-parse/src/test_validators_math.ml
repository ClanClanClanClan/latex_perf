(** Unit tests for all L1 MATH validator rules. Merged from: math_l1 (009-022),
    math_gap (025,028,029), math_l1b (030-053), math_c1/c2/c3 (055-108). 60 test
    files -> consolidated by domain. *)

open Latex_parse_lib
open Test_helpers

(* -- MATH-A: MATH-009..022 (core math-token validators) ---------- *)
let () =
  (* ══════════════════════════════════════════════════════════════════════
     MATH-009: Bare function name in math
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-009 fires on bare sin" (fun tag ->
      expect (fires "MATH-009" "$sin x$") (tag ^ ": bare sin"));
  run "MATH-009 fires on bare log" (fun tag ->
      expect (fires "MATH-009" "$log x$") (tag ^ ": bare log"));
  run "MATH-009 fires on bare exp" (fun tag ->
      expect (fires "MATH-009" "$exp(x)$") (tag ^ ": bare exp"));
  run "MATH-009 clean: \\sin" (fun tag ->
      expect (does_not_fire "MATH-009" "$\\sin x$") (tag ^ ": \\sin ok"));
  run "MATH-009 clean: \\log" (fun tag ->
      expect (does_not_fire "MATH-009" "$\\log x$") (tag ^ ": \\log ok"));
  run "MATH-009 clean: no functions" (fun tag ->
      expect (does_not_fire "MATH-009" "$x + y$") (tag ^ ": no funcs"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-010: Division symbol ÷ in math
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-010 fires on ÷" (fun tag ->
      expect (fires "MATH-010" "$a \xc3\xb7 b$") (tag ^ ": div symbol"));
  run "MATH-010 count=2" (fun tag ->
      expect
        (fires_with_count "MATH-010" "$a \xc3\xb7 b \xc3\xb7 c$" 2)
        (tag ^ ": count=2"));
  run "MATH-010 clean: \\frac" (fun tag ->
      expect (does_not_fire "MATH-010" "$\\frac{a}{b}$") (tag ^ ": frac ok"));
  run "MATH-010 clean: solidus" (fun tag ->
      expect (does_not_fire "MATH-010" "$a / b$") (tag ^ ": solidus ok"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-011: Vector notation inconsistent
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-011 fires on mixed vec+mathbf" (fun tag ->
      expect
        (fires "MATH-011" "$\\vec{a} + \\mathbf{b}$")
        (tag ^ ": mixed notation"));
  run "MATH-011 clean: only vec" (fun tag ->
      expect
        (does_not_fire "MATH-011" "$\\vec{a} + \\vec{b}$")
        (tag ^ ": consistent vec"));
  run "MATH-011 clean: only mathbf" (fun tag ->
      expect
        (does_not_fire "MATH-011" "$\\mathbf{a} + \\mathbf{b}$")
        (tag ^ ": consistent mathbf"));
  run "MATH-011 clean: no vectors" (fun tag ->
      expect (does_not_fire "MATH-011" "$x + y$") (tag ^ ": no vectors"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-012: Multi-letter function not in \operatorname{}
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-012 fires on bare diag" (fun tag ->
      expect (fires "MATH-012" "$diag(A)$") (tag ^ ": bare diag"));
  run "MATH-012 fires on bare trace" (fun tag ->
      expect (fires "MATH-012" "$trace(A)$") (tag ^ ": bare trace"));
  run "MATH-012 clean: \\operatorname{diag}" (fun tag ->
      expect
        (does_not_fire "MATH-012" "$\\operatorname{diag}(A)$")
        (tag ^ ": operatorname ok"));
  run "MATH-012 clean: \\sin (known)" (fun tag ->
      expect (does_not_fire "MATH-012" "$\\sin x$") (tag ^ ": known operator"));
  run "MATH-012 clean: short var xy" (fun tag ->
      expect (does_not_fire "MATH-012" "$xy + z$") (tag ^ ": 2-char var"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-013: Differential d not typeset roman
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-013 fires on \\int f(x) dx" (fun tag ->
      expect (fires "MATH-013" "$\\int f(x) dx$") (tag ^ ": bare dx in integral"));
  run "MATH-013 fires on \\oint F dy" (fun tag ->
      expect
        (fires "MATH-013" "$\\oint F dy$")
        (tag ^ ": bare dy in line integral"));
  run "MATH-013 clean: \\int f(x)\\,\\mathrm{d}x" (fun tag ->
      expect
        (does_not_fire "MATH-013" "$\\int f(x)\\,\\mathrm{d}x$")
        (tag ^ ": mathrm d ok"));
  run "MATH-013 clean: no integral" (fun tag ->
      expect
        (does_not_fire "MATH-013" "$f(x) dx$")
        (tag ^ ": no integral context"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-014: Inline \frac in running text
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-014 fires on $\\frac{a}{b}$" (fun tag ->
      expect (fires "MATH-014" "$\\frac{a}{b}$") (tag ^ ": frac in inline"));
  run "MATH-014 clean: \\[\\frac{a}{b}\\]" (fun tag ->
      expect
        (does_not_fire "MATH-014" "\\[\\frac{a}{b}\\]")
        (tag ^ ": frac in display ok"));
  run "MATH-014 clean: $\\tfrac{a}{b}$" (fun tag ->
      expect (does_not_fire "MATH-014" "$\\tfrac{a}{b}$") (tag ^ ": tfrac ok"));
  run "MATH-014 clean: no frac" (fun tag ->
      expect (does_not_fire "MATH-014" "$x + y$") (tag ^ ": no frac"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-015: \stackrel used — prefer \overset
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-015 fires on \\stackrel" (fun tag ->
      expect (fires "MATH-015" "$\\stackrel{\\rm def}{=}$") (tag ^ ": stackrel"));
  run "MATH-015 count=2" (fun tag ->
      expect
        (fires_with_count "MATH-015" "$\\stackrel{a}{b} + \\stackrel{c}{d}$" 2)
        (tag ^ ": count=2"));
  run "MATH-015 clean: \\overset" (fun tag ->
      expect
        (does_not_fire "MATH-015" "$\\overset{\\rm def}{=}$")
        (tag ^ ": overset ok"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-016: Nested subscripts without braces
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-016 fires on x_i_j" (fun tag ->
      expect (fires "MATH-016" "$x_i_j$") (tag ^ ": x_i_j"));
  run "MATH-016 clean: x_{i_j}" (fun tag ->
      expect (does_not_fire "MATH-016" "$x_{i_j}$") (tag ^ ": braced"));
  run "MATH-016 clean: x_i" (fun tag ->
      expect (does_not_fire "MATH-016" "$x_i$") (tag ^ ": single sub"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-017: Mismatched \left/\right delimiter types
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-017 fires on \\left\\{ ... \\right]" (fun tag ->
      expect
        (fires "MATH-017" "$\\left\\{ x \\right]$")
        (tag ^ ": brace vs bracket"));
  run "MATH-017 fires on \\left( ... \\right]" (fun tag ->
      expect
        (fires "MATH-017" "$\\left( x \\right]$")
        (tag ^ ": paren vs bracket"));
  run "MATH-017 clean: \\left( ... \\right)" (fun tag ->
      expect
        (does_not_fire "MATH-017" "$\\left( x \\right)$")
        (tag ^ ": matched parens"));
  run "MATH-017 clean: \\left. ... \\right)" (fun tag ->
      expect
        (does_not_fire "MATH-017" "$\\left. x \\right)$")
        (tag ^ ": invisible left ok"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-018: π written numerically as 3.14
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-018 fires on 3.14" (fun tag ->
      expect (fires "MATH-018" "$3.14$") (tag ^ ": 3.14"));
  run "MATH-018 fires on 3.14159" (fun tag ->
      expect (fires "MATH-018" "$3.14159$") (tag ^ ": 3.14159"));
  run "MATH-018 clean: \\pi" (fun tag ->
      expect (does_not_fire "MATH-018" "$\\pi$") (tag ^ ": \\pi ok"));
  run "MATH-018 clean: 3.15" (fun tag ->
      expect (does_not_fire "MATH-018" "$3.15$") (tag ^ ": not pi"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-019: Inline stacked ^_ order wrong
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-019 fires on $\\sum^n_i$" (fun tag ->
      expect (fires "MATH-019" "$\\sum^n_i$") (tag ^ ": ^n_i in inline"));
  run "MATH-019 clean: $\\sum_{i}^{n}$" (fun tag ->
      expect
        (does_not_fire "MATH-019" "$\\sum_{i}^{n}$")
        (tag ^ ": sub before sup ok"));
  run "MATH-019 clean: display \\sum^n_i" (fun tag ->
      expect (does_not_fire "MATH-019" "\\[\\sum^n_i\\]") (tag ^ ": display ok"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-020: Missing \cdot between coefficient and vector
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-020 fires on 3\\vec{a}" (fun tag ->
      expect (fires "MATH-020" "$3\\vec{a}$") (tag ^ ": digit before vec"));
  run "MATH-020 fires on 2\\mathbf{v}" (fun tag ->
      expect (fires "MATH-020" "$2\\mathbf{v}$") (tag ^ ": digit before mathbf"));
  run "MATH-020 clean: 3\\cdot\\vec{a}" (fun tag ->
      expect
        (does_not_fire "MATH-020" "$3\\cdot\\vec{a}$")
        (tag ^ ": cdot present"));
  run "MATH-020 clean: \\vec{a}" (fun tag ->
      expect (does_not_fire "MATH-020" "$\\vec{a}$") (tag ^ ": no coefficient"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-021: Absolute value bars |x|
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-021 fires on |x|" (fun tag ->
      expect (fires "MATH-021" "$|x|$") (tag ^ ": bar abs value"));
  run "MATH-021 fires on |a+b|" (fun tag ->
      expect (fires "MATH-021" "$|a+b|$") (tag ^ ": expression abs"));
  run "MATH-021 clean: \\lvert x \\rvert" (fun tag ->
      expect
        (does_not_fire "MATH-021" "$\\lvert x \\rvert$")
        (tag ^ ": lvert/rvert ok"));
  run "MATH-021 clean: no bars" (fun tag ->
      expect (does_not_fire "MATH-021" "$x + y$") (tag ^ ": no bars"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-022: Bold math italic without \bm or \mathbf
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-022 fires on \\textbf in math" (fun tag ->
      expect (fires "MATH-022" "$\\textbf{x}$") (tag ^ ": textbf in math"));
  run "MATH-022 count=2" (fun tag ->
      expect
        (fires_with_count "MATH-022" "$\\textbf{a} + \\textbf{b}$" 2)
        (tag ^ ": count=2"));
  run "MATH-022 clean: \\mathbf" (fun tag ->
      expect (does_not_fire "MATH-022" "$\\mathbf{x}$") (tag ^ ": mathbf ok"));
  run "MATH-022 clean: \\bm" (fun tag ->
      expect (does_not_fire "MATH-022" "$\\bm{x}$") (tag ^ ": bm ok"));

  (* ══════════════════════════════════════════════════════════════════════
     Cross-cutting edge cases
     ══════════════════════════════════════════════════════════════════════ *)
  run "empty input: no L1 MATH rules fire" (fun tag ->
      let results = Validators.run_all "" in
      let math_l1_fires =
        List.filter
          (fun (r : Validators.result) ->
            String.length r.id >= 5
            && String.sub r.id 0 5 = "MATH-"
            && r.id <> "MATH-083")
          results
      in
      expect (math_l1_fires = []) (tag ^ ": no L1 MATH on empty"));

  run "clean math: no L1 MATH rules fire" (fun tag ->
      let results = Validators.run_all "$\\sin(x) + \\cos(y)$" in
      let math_l1_fires =
        List.filter
          (fun (r : Validators.result) ->
            String.length r.id >= 5
            && String.sub r.id 0 5 = "MATH-"
            && r.id <> "MATH-083")
          results
      in
      expect (math_l1_fires = []) (tag ^ ": no L1 MATH on clean"));

  (* Registration checks *)
  run "registration: MATH-009 registered" (fun tag ->
      expect (fires "MATH-009" "$sin x$") (tag ^ ": registered"));
  run "registration: MATH-015 registered" (fun tag ->
      expect (fires "MATH-015" "$\\stackrel{a}{b}$") (tag ^ ": registered"));
  run "registration: MATH-022 registered" (fun tag ->
      expect (fires "MATH-022" "$\\textbf{x}$") (tag ^ ": registered"));

  (* Precondition checks *)
  run "precondition: MATH-009 maps to L1" (fun tag ->
      let layer = Validators.precondition_of_rule_id "MATH-009" in
      expect (layer = L1) (tag ^ ": L1 layer"));
  run "precondition: MATH-083 maps to L0" (fun tag ->
      let layer = Validators.precondition_of_rule_id "MATH-083" in
      expect (layer = L0) (tag ^ ": L0 layer for 083"));

  (* Combined: multiple MATH L1 issues *)
  run "combined: multiple MATH rules fire" (fun tag ->
      let src = "$sin x + \\stackrel{a}{b} + |y| + \\textbf{z}$" in
      expect (fires "MATH-009" src) (tag ^ ": MATH-009 fires");
      expect (fires "MATH-015" src) (tag ^ ": MATH-015 fires");
      expect (fires "MATH-021" src) (tag ^ ": MATH-021 fires");
      expect (fires "MATH-022" src) (tag ^ ": MATH-022 fires"))

(* -- MATH gap-fill: MATH-025, MATH-028, MATH-029 ----------------- *)
let () =
  (* ════════════════════════════════════════════════════════════════════
     MATH-025: align with single column → suggest equation
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-025 align no ampersand" (fun tag ->
      expect
        (fires "MATH-025" "\\begin{align}\nx = 1\n\\end{align}")
        (tag ^ ": should fire"));
  run "MATH-025 align* no ampersand" (fun tag ->
      expect
        (fires "MATH-025" "\\begin{align*}\ny = 2\n\\end{align*}")
        (tag ^ ": should fire"));
  run "MATH-025 align with ampersand" (fun tag ->
      expect
        (does_not_fire "MATH-025"
           "\\begin{align}\nx &= 1 \\\\\ny &= 2\n\\end{align}")
        (tag ^ ": has ampersand"));
  run "MATH-025 align* with ampersand" (fun tag ->
      expect
        (does_not_fire "MATH-025"
           "\\begin{align*}\na &= b \\\\\nc &= d\n\\end{align*}")
        (tag ^ ": has ampersand"));
  run "MATH-025 two single-column aligns" (fun tag ->
      expect
        (fires_with_count "MATH-025"
           "\\begin{align}\n\
            x = 1\n\
            \\end{align}\n\
            \\begin{align}\n\
            y = 2\n\
            \\end{align}"
           2)
        (tag ^ ": count 2"));
  run "MATH-025 no align env" (fun tag ->
      expect
        (does_not_fire "MATH-025" "Just some text $x = 1$")
        (tag ^ ": no align env"));
  run "MATH-025 equation env" (fun tag ->
      expect
        (does_not_fire "MATH-025" "\\begin{equation}\nx = 1\n\\end{equation}")
        (tag ^ ": equation env"));
  run "MATH-025 empty align body" (fun tag ->
      expect
        (fires "MATH-025" "\\begin{align}\n\\end{align}")
        (tag ^ ": should fire"));
  run "MATH-025 severity is info" (fun tag ->
      match find_result "MATH-025" "\\begin{align}\nx = 1\n\\end{align}" with
      | Some r -> expect (r.severity = Validators.Info) (tag ^ ": severity info")
      | None -> expect false (tag ^ ": did not fire"));
  run "MATH-025 empty input" (fun tag ->
      expect (does_not_fire "MATH-025" "") (tag ^ ": empty input"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-028: array without column alignment spec
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-028 array no spec" (fun tag ->
      expect
        (fires "MATH-028" "$\\begin{array} 1 \\\\ 2 \\end{array}$")
        (tag ^ ": should fire"));
  run "MATH-028 array space after" (fun tag ->
      expect
        (fires "MATH-028" "$\\begin{array} x \\end{array}$")
        (tag ^ ": should fire"));
  run "MATH-028 array with {c}" (fun tag ->
      expect
        (does_not_fire "MATH-028" "$\\begin{array}{c} 1 \\\\ 2 \\end{array}$")
        (tag ^ ": has col spec"));
  run "MATH-028 array with {lcr}" (fun tag ->
      expect
        (does_not_fire "MATH-028" "$\\begin{array}{lcr} a & b & c \\end{array}$")
        (tag ^ ": has col spec"));
  run "MATH-028 array with {|c|}" (fun tag ->
      expect
        (does_not_fire "MATH-028" "$\\begin{array}{|c|} 1 \\end{array}$")
        (tag ^ ": has col spec"));
  run "MATH-028 two bare arrays" (fun tag ->
      expect
        (fires_with_count "MATH-028"
           "$\\begin{array} 1 \\end{array}$ $\\begin{array} 2 \\end{array}$" 2)
        (tag ^ ": count 2"));
  run "MATH-028 no array env" (fun tag ->
      expect (does_not_fire "MATH-028" "$x + y$") (tag ^ ": no array env"));
  run "MATH-028 severity is info" (fun tag ->
      match find_result "MATH-028" "$\\begin{array} x \\end{array}$" with
      | Some r -> expect (r.severity = Validators.Info) (tag ^ ": severity info")
      | None -> expect false (tag ^ ": did not fire"));
  run "MATH-028 empty input" (fun tag ->
      expect (does_not_fire "MATH-028" "") (tag ^ ": empty input"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-029: eqnarray usage
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-029 eqnarray" (fun tag ->
      expect
        (fires "MATH-029" "\\begin{eqnarray}\nx &=& 1\n\\end{eqnarray}")
        (tag ^ ": should fire"));
  run "MATH-029 eqnarray*" (fun tag ->
      expect
        (fires "MATH-029" "\\begin{eqnarray*}\nx &=& 1\n\\end{eqnarray*}")
        (tag ^ ": should fire"));
  run "MATH-029 align" (fun tag ->
      expect
        (does_not_fire "MATH-029" "\\begin{align}\nx &= 1\n\\end{align}")
        (tag ^ ": align ok"));
  run "MATH-029 align*" (fun tag ->
      expect
        (does_not_fire "MATH-029" "\\begin{align*}\nx &= 1\n\\end{align*}")
        (tag ^ ": align* ok"));
  run "MATH-029 equation" (fun tag ->
      expect
        (does_not_fire "MATH-029" "\\begin{equation}\nx = 1\n\\end{equation}")
        (tag ^ ": equation ok"));
  run "MATH-029 two eqnarrays" (fun tag ->
      expect
        (fires_with_count "MATH-029"
           "\\begin{eqnarray}\n\
            a\n\
            \\end{eqnarray}\n\
            \\begin{eqnarray*}\n\
            b\n\
            \\end{eqnarray*}"
           2)
        (tag ^ ": count 2"));
  run "MATH-029 no env" (fun tag ->
      expect
        (does_not_fire "MATH-029" "Just text $x = 1$")
        (tag ^ ": no eqnarray"));
  run "MATH-029 severity is warning" (fun tag ->
      match
        find_result "MATH-029" "\\begin{eqnarray}\nx &=& 1\n\\end{eqnarray}"
      with
      | Some r ->
          expect (r.severity = Validators.Warning) (tag ^ ": severity warning")
      | None -> expect false (tag ^ ": did not fire"));
  run "MATH-029 empty input" (fun tag ->
      expect (does_not_fire "MATH-029" "") (tag ^ ": empty input"));

  (* ════════════════════════════════════════════════════════════════════
     precondition_of_rule_id for L2/L3 future rules
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-023 maps to L2" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "MATH-023" = Validators.L2)
        (tag ^ ": MATH-023 = L2"));
  run "MATH-024 maps to L2" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "MATH-024" = Validators.L2)
        (tag ^ ": MATH-024 = L2"));
  run "MATH-026 maps to L2 (log-based approx)" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "MATH-026" = Validators.L2)
        (tag ^ ": MATH-026 = L2"));
  run "MATH-027 maps to L2 (log-based approx)" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "MATH-027" = Validators.L2)
        (tag ^ ": MATH-027 = L2"));
  run "MATH-025 maps to L1" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "MATH-025" = Validators.L1)
        (tag ^ ": MATH-025 = L1"));
  run "MATH-028 maps to L1" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "MATH-028" = Validators.L1)
        (tag ^ ": MATH-028 = L1"));
  run "MATH-029 maps to L1" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "MATH-029" = Validators.L1)
        (tag ^ ": MATH-029 = L1"));

  (* ════════════════════════════════════════════════════════════════════
     precondition_of_rule_id: CJK/CMD layer mappings (spec says L0)
     ════════════════════════════════════════════════════════════════════ *)
  run "CJK-001 maps to L0" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "CJK-001" = Validators.L0)
        (tag ^ ": CJK-001 = L0"));
  run "CJK-002 maps to L0" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "CJK-002" = Validators.L0)
        (tag ^ ": CJK-002 = L0"));
  run "CJK-008 maps to L1 (needs expansion)" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "CJK-008" = Validators.L1)
        (tag ^ ": CJK-008 = L1"));
  run "CJK-015 maps to L1 (needs expansion)" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "CJK-015" = Validators.L1)
        (tag ^ ": CJK-015 = L1"));
  run "CMD-002 maps to L0" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "CMD-002" = Validators.L0)
        (tag ^ ": CMD-002 = L0"));
  run "CMD-004 maps to L0" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "CMD-004" = Validators.L0)
        (tag ^ ": CMD-004 = L0"));
  run "CMD-001 maps to L1 (needs expansion)" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "CMD-001" = Validators.L1)
        (tag ^ ": CMD-001 = L1"));
  run "CMD-003 maps to L1 (needs expansion)" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "CMD-003" = Validators.L1)
        (tag ^ ": CMD-003 = L1"));
  run "CMD-007 maps to L1 (needs expansion)" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "CMD-007" = Validators.L1)
        (tag ^ ": CMD-007 = L1"));
  run "CMD-010 maps to L1 (needs expansion)" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "CMD-010" = Validators.L1)
        (tag ^ ": CMD-010 = L1"));
  run "VERB-001 maps to L0" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "VERB-001" = Validators.L0)
        (tag ^ ": VERB-001 = L0"));
  run "TYPO-059 maps to L1" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "TYPO-059" = Validators.L1)
        (tag ^ ": TYPO-059 = L1"))

(* -- MATH-B: MATH-030..053 --------------------------------------- *)
let () =
  (* ══════════════════════════════════════════════════════════════════════
     MATH-030: Overuse of \displaystyle in inline math
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-030 fires on $\\displaystyle\\sum$" (fun tag ->
      expect
        (fires "MATH-030" "$\\displaystyle\\sum_{i=1}^n a_i$")
        (tag ^ ": displaystyle in inline"));
  run "MATH-030 count=2" (fun tag ->
      expect
        (fires_with_count "MATH-030" "$\\displaystyle x$ and $\\displaystyle y$"
           2)
        (tag ^ ": count=2"));
  run "MATH-030 clean: display math \\[\\displaystyle\\]" (fun tag ->
      expect
        (does_not_fire "MATH-030" "\\[\\displaystyle\\sum_{i=1}^n a_i\\]")
        (tag ^ ": display mode ok"));
  run "MATH-030 clean: equation env" (fun tag ->
      expect
        (does_not_fire "MATH-030"
           "\\begin{equation}\\displaystyle\\sum\\end{equation}")
        (tag ^ ": equation env ok"));
  run "MATH-030 clean: no displaystyle" (fun tag ->
      expect (does_not_fire "MATH-030" "$x + y$") (tag ^ ": no displaystyle"));
  run "MATH-030 fires in \\( ... \\) inline" (fun tag ->
      expect (fires "MATH-030" "\\(\\displaystyle x\\)") (tag ^ ": \\( \\) form"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-031: Operator spacing: missing \; before \text in math
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-031 fires on x\\text{for}" (fun tag ->
      expect
        (fires "MATH-031" "$x\\text{for all}$")
        (tag ^ ": no space before \\text"));
  run "MATH-031 fires on }\\text{" (fun tag ->
      expect
        (fires "MATH-031" "$\\frac{a}{b}\\text{where}$")
        (tag ^ ": } before \\text"));
  run "MATH-031 count=2" (fun tag ->
      expect
        (fires_with_count "MATH-031" "$x\\text{for} y\\text{if}$" 2)
        (tag ^ ": count=2"));
  run "MATH-031 clean: x\\;\\text{}" (fun tag ->
      expect
        (does_not_fire "MATH-031" "$x\\;\\text{for all}$")
        (tag ^ ": \\; before \\text ok"));
  run "MATH-031 clean: x\\,\\text{}" (fun tag ->
      expect
        (does_not_fire "MATH-031" "$x\\,\\text{if}$")
        (tag ^ ": \\, before \\text ok"));
  run "MATH-031 clean: x \\text{}" (fun tag ->
      expect
        (does_not_fire "MATH-031" "$x \\text{for all}$")
        (tag ^ ": space before \\text ok"));
  run "MATH-031 clean: no \\text" (fun tag ->
      expect (does_not_fire "MATH-031" "$x + y$") (tag ^ ": no \\text"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-033: \pm used outside math mode
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-033 fires on \\pm in text" (fun tag ->
      expect
        (fires "MATH-033" "The result is \\pm 5.")
        (tag ^ ": \\pm outside math"));
  run "MATH-033 count=2" (fun tag ->
      expect
        (fires_with_count "MATH-033" "Values are \\pm 3 and \\pm 7." 2)
        (tag ^ ": count=2"));
  run "MATH-033 clean: \\pm in math" (fun tag ->
      expect (does_not_fire "MATH-033" "$x \\pm y$") (tag ^ ": \\pm in math ok"));
  run "MATH-033 clean: \\pm in display math" (fun tag ->
      expect
        (does_not_fire "MATH-033" "\\[x \\pm y\\]")
        (tag ^ ": display math ok"));
  run "MATH-033 clean: no \\pm" (fun tag ->
      expect (does_not_fire "MATH-033" "The result is 5.") (tag ^ ": no \\pm"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-034: Spacing before differential in integral missing \,
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-034 fires on \\int f(x)dx" (fun tag ->
      expect (fires "MATH-034" "$\\int f(x)dx$") (tag ^ ": no \\, before dx"));
  run "MATH-034 fires on \\int g dy" (fun tag ->
      expect (fires "MATH-034" "$\\int g dy$") (tag ^ ": no \\, before dy"));
  run "MATH-034 clean: \\int f(x)\\,dx" (fun tag ->
      expect
        (does_not_fire "MATH-034" "$\\int f(x)\\,dx$")
        (tag ^ ": \\, before dx ok"));
  run "MATH-034 clean: no integral" (fun tag ->
      expect
        (does_not_fire "MATH-034" "$f(x) dx$")
        (tag ^ ": no integral context"));
  run "MATH-034 clean: \\int only, no diff" (fun tag ->
      expect
        (does_not_fire "MATH-034" "$\\int f(x)$")
        (tag ^ ": integral without differential"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-035: Multiple subscripts stacked without braces
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-035 fires on a_i_j" (fun tag ->
      expect (fires "MATH-035" "$a_i_j$") (tag ^ ": a_i_j"));
  run "MATH-035 fires on x_{ab}_c" (fun tag ->
      expect (fires "MATH-035" "$x_{ab}_c$") (tag ^ ": braced then bare"));
  run "MATH-035 clean: x_{i,j}" (fun tag ->
      expect (does_not_fire "MATH-035" "$x_{i,j}$") (tag ^ ": comma form"));
  run "MATH-035 clean: single subscript" (fun tag ->
      expect (does_not_fire "MATH-035" "$x_i$") (tag ^ ": single sub"));
  run "MATH-035 clean: x_{i_j}" (fun tag ->
      expect (does_not_fire "MATH-035" "$x_{i_j}$") (tag ^ ": nested braced"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-036: Superfluous \mathrm{} around single letter
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-036 fires on \\mathrm{x}" (fun tag ->
      expect (fires "MATH-036" "$\\mathrm{x}$") (tag ^ ": single letter"));
  run "MATH-036 fires on \\mathrm{A}" (fun tag ->
      expect (fires "MATH-036" "$\\mathrm{A}$") (tag ^ ": single capital"));
  run "MATH-036 count=2" (fun tag ->
      expect
        (fires_with_count "MATH-036" "$\\mathrm{a} + \\mathrm{b}$" 2)
        (tag ^ ": count=2"));
  run "MATH-036 clean: \\mathrm{max}" (fun tag ->
      expect
        (does_not_fire "MATH-036" "$\\mathrm{max}$")
        (tag ^ ": multi-letter ok"));
  run "MATH-036 clean: no \\mathrm" (fun tag ->
      expect (does_not_fire "MATH-036" "$x + y$") (tag ^ ": no mathrm"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-037: \sfrac used in math mode
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-037 fires on $\\sfrac{1}{2}$" (fun tag ->
      expect (fires "MATH-037" "$\\sfrac{1}{2}$") (tag ^ ": sfrac in math"));
  run "MATH-037 count=2" (fun tag ->
      expect
        (fires_with_count "MATH-037" "$\\sfrac{1}{2} + \\sfrac{3}{4}$" 2)
        (tag ^ ": count=2"));
  run "MATH-037 clean: \\sfrac in text" (fun tag ->
      expect
        (does_not_fire "MATH-037" "Use \\sfrac{1}{2} cup of flour.")
        (tag ^ ": text mode ok"));
  run "MATH-037 clean: $\\frac{1}{2}$" (fun tag ->
      expect (does_not_fire "MATH-037" "$\\frac{1}{2}$") (tag ^ ": frac ok"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-038: Nested \frac three levels deep
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-038 fires on triple-nested frac" (fun tag ->
      expect
        (fires "MATH-038" "$\\frac{\\frac{\\frac{a}{b}}{c}}{d}$")
        (tag ^ ": 3 levels"));
  run "MATH-038 clean: two-level frac" (fun tag ->
      expect
        (does_not_fire "MATH-038" "$\\frac{\\frac{a}{b}}{c}$")
        (tag ^ ": 2 levels ok"));
  run "MATH-038 clean: single frac" (fun tag ->
      expect (does_not_fire "MATH-038" "$\\frac{a}{b}$") (tag ^ ": 1 level ok"));
  run "MATH-038 clean: no frac" (fun tag ->
      expect (does_not_fire "MATH-038" "$x + y$") (tag ^ ": no frac"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-039: Stacked relational operators without \substack
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-039 fires on \\underset{x}{\\overset{y}{" (fun tag ->
      expect
        (fires "MATH-039" "$\\underset{a}{\\overset{b}{=}}$")
        (tag ^ ": underset+overset"));
  run "MATH-039 fires on \\overset{x}{\\underset{y}{" (fun tag ->
      expect
        (fires "MATH-039" "$\\overset{a}{\\underset{b}{=}}$")
        (tag ^ ": overset+underset"));
  run "MATH-039 clean: single \\overset" (fun tag ->
      expect
        (does_not_fire "MATH-039" "$\\overset{a}{=}$")
        (tag ^ ": single overset ok"));
  run "MATH-039 clean: single \\underset" (fun tag ->
      expect
        (does_not_fire "MATH-039" "$\\underset{a}{=}$")
        (tag ^ ": single underset ok"));
  run "MATH-039 clean: no stacked ops" (fun tag ->
      expect (does_not_fire "MATH-039" "$x = y$") (tag ^ ": no stacked ops"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-040: Ellipsis \ldots between center-axis operators
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-040 fires on + \\ldots +" (fun tag ->
      expect (fires "MATH-040" "$a_1 + \\ldots + a_n$") (tag ^ ": + \\ldots +"));
  run "MATH-040 fires on = \\ldots =" (fun tag ->
      expect (fires "MATH-040" "$x = \\ldots = y$") (tag ^ ": = \\ldots ="));
  run "MATH-040 fires on < \\ldots <" (fun tag ->
      expect (fires "MATH-040" "$a < \\ldots < b$") (tag ^ ": < \\ldots <"));
  run "MATH-040 clean: + \\cdots +" (fun tag ->
      expect
        (does_not_fire "MATH-040" "$a_1 + \\cdots + a_n$")
        (tag ^ ": cdots ok"));
  run "MATH-040 clean: standalone \\ldots" (fun tag ->
      expect
        (does_not_fire "MATH-040" "$a_1, a_2, \\ldots$")
        (tag ^ ": trailing \\ldots ok"));
  run "MATH-040 clean: no ellipsis" (fun tag ->
      expect (does_not_fire "MATH-040" "$a + b$") (tag ^ ": no ellipsis"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-041: Integral limits written inline in inline math
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-041 fires on $\\int_0^1 f$" (fun tag ->
      expect
        (fires "MATH-041" "$\\int_0^1 f(x) dx$")
        (tag ^ ": inline int with limits"));
  run "MATH-041 fires on $\\int_{a}^{b}$" (fun tag ->
      expect
        (fires "MATH-041" "$\\int_{a}^{b} f(x) dx$")
        (tag ^ ": braced limits inline"));
  run "MATH-041 clean: display integral" (fun tag ->
      expect
        (does_not_fire "MATH-041" "\\[\\int_0^1 f(x) dx\\]")
        (tag ^ ": display ok"));
  run "MATH-041 clean: \\int without limits" (fun tag ->
      expect
        (does_not_fire "MATH-041" "$\\int f(x) dx$")
        (tag ^ ": no limits ok"));
  run "MATH-041 clean: no integral" (fun tag ->
      expect (does_not_fire "MATH-041" "$x + y$") (tag ^ ": no integral"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-042: Missing \, between number and unit in math
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-042 fires on 5\\mathrm{kg}" (fun tag ->
      expect
        (fires "MATH-042" "$5\\mathrm{kg}$")
        (tag ^ ": digit before \\mathrm{"));
  run "MATH-042 fires on 10\\text{m}" (fun tag ->
      expect (fires "MATH-042" "$10\\text{m}$") (tag ^ ": digit before \\text{"));
  run "MATH-042 fires on 3\\textrm{s}" (fun tag ->
      expect
        (fires "MATH-042" "$3\\textrm{s}$")
        (tag ^ ": digit before \\textrm{"));
  run "MATH-042 clean: 5\\,\\mathrm{kg}" (fun tag ->
      expect
        (does_not_fire "MATH-042" "$5\\,\\mathrm{kg}$")
        (tag ^ ": \\, present ok"));
  run "MATH-042 clean: no number before unit" (fun tag ->
      expect
        (does_not_fire "MATH-042" "$x\\mathrm{kg}$")
        (tag ^ ": letter before mathrm ok"));
  run "MATH-042 clean: no units" (fun tag ->
      expect (does_not_fire "MATH-042" "$5 + 3$") (tag ^ ": no units"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-043: \text{Xxx} in math used as function name
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-043 fires on \\text{Var}" (fun tag ->
      expect (fires "MATH-043" "$\\text{Var}(X)$") (tag ^ ": Var as function"));
  run "MATH-043 fires on \\text{Cov}" (fun tag ->
      expect (fires "MATH-043" "$\\text{Cov}(X, Y)$") (tag ^ ": Cov as function"));
  run "MATH-043 fires on \\text{Tr}" (fun tag ->
      expect (fires "MATH-043" "$\\text{Tr}(A)$") (tag ^ ": Tr as function"));
  run "MATH-043 count=2" (fun tag ->
      expect
        (fires_with_count "MATH-043" "$\\text{Var}(X) + \\text{Cov}(X,Y)$" 2)
        (tag ^ ": count=2"));
  run "MATH-043 clean: \\operatorname{Var}" (fun tag ->
      expect
        (does_not_fire "MATH-043" "$\\operatorname{Var}(X)$")
        (tag ^ ": operatorname ok"));
  run "MATH-043 clean: \\text{for all}" (fun tag ->
      expect
        (does_not_fire "MATH-043" "$x \\text{for all}$")
        (tag ^ ": lowercase text ok"));
  run "MATH-043 clean: \\text{IF}" (fun tag ->
      expect
        (does_not_fire "MATH-043" "$\\text{IF}$")
        (tag ^ ": all caps doesn't match"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-044: Compound relation <=/>= instead of \le/\ge
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-044 fires on <=" (fun tag ->
      expect (fires "MATH-044" "$x <= y$") (tag ^ ": <= in math"));
  run "MATH-044 fires on >=" (fun tag ->
      expect (fires "MATH-044" "$x >= y$") (tag ^ ": >= in math"));
  run "MATH-044 count=2" (fun tag ->
      expect (fires_with_count "MATH-044" "$a <= b >= c$" 2) (tag ^ ": count=2"));
  run "MATH-044 clean: \\le" (fun tag ->
      expect (does_not_fire "MATH-044" "$x \\le y$") (tag ^ ": \\le ok"));
  run "MATH-044 clean: \\geq" (fun tag ->
      expect (does_not_fire "MATH-044" "$x \\geq y$") (tag ^ ": \\geq ok"));
  run "MATH-044 clean: \\le=" (fun tag ->
      expect (does_not_fire "MATH-044" "$x \\le y$") (tag ^ ": proper notation"));
  run "MATH-044 clean: no relations" (fun tag ->
      expect (does_not_fire "MATH-044" "$x + y$") (tag ^ ": no relations"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-045: Mixed italic/upright capital Greek
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-045 fires on mixed Gamma style" (fun tag ->
      expect
        (fires "MATH-045" "$\\Gamma + \\mathrm{\\Delta}$")
        (tag ^ ": mixed italic/upright"));
  run "MATH-045 clean: all italic Greek" (fun tag ->
      expect
        (does_not_fire "MATH-045" "$\\Gamma + \\Delta$")
        (tag ^ ": all italic ok"));
  run "MATH-045 clean: no Greek capitals" (fun tag ->
      expect (does_not_fire "MATH-045" "$x + y$") (tag ^ ": no Greek"));
  run "MATH-045 clean: all upright" (fun tag ->
      expect
        (does_not_fire "MATH-045" "$\\mathrm{\\Gamma} + \\mathrm{\\Delta}$")
        (tag ^ ": all upright ok"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-046: \ldots between commas — prefer \cdots
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-046 fires on , \\ldots ," (fun tag ->
      expect
        (fires "MATH-046" "$a_1, \\ldots, a_n$")
        (tag ^ ": comma ldots comma"));
  run "MATH-046 count=2" (fun tag ->
      expect
        (fires_with_count "MATH-046" "$a, \\ldots, b, \\ldots, c$" 2)
        (tag ^ ": count=2"));
  run "MATH-046 clean: , \\cdots ," (fun tag ->
      expect
        (does_not_fire "MATH-046" "$a_1, \\cdots, a_n$")
        (tag ^ ": cdots ok"));
  run "MATH-046 clean: \\ldots without commas" (fun tag ->
      expect
        (does_not_fire "MATH-046" "$a_1 \\ldots a_n$")
        (tag ^ ": no surrounding commas"));
  run "MATH-046 clean: no ellipsis" (fun tag ->
      expect (does_not_fire "MATH-046" "$a, b, c$") (tag ^ ": no ellipsis"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-047: Double superscript a^b^c
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-047 fires on x^a^b" (fun tag ->
      expect (fires "MATH-047" "$x^a^b$") (tag ^ ": x^a^b"));
  run "MATH-047 fires on x^{ab}^c" (fun tag ->
      expect (fires "MATH-047" "$x^{ab}^c$") (tag ^ ": braced then bare"));
  run "MATH-047 clean: x^{a^b}" (fun tag ->
      expect (does_not_fire "MATH-047" "$x^{a^b}$") (tag ^ ": nested braced"));
  run "MATH-047 clean: single sup" (fun tag ->
      expect (does_not_fire "MATH-047" "$x^a$") (tag ^ ": single sup"));
  run "MATH-047 clean: x^a_b" (fun tag ->
      expect (does_not_fire "MATH-047" "$x^a_b$") (tag ^ ": sup then sub ok"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-048: \mathbf applied to digits
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-048 fires on \\mathbf{1}" (fun tag ->
      expect (fires "MATH-048" "$\\mathbf{1}$") (tag ^ ": bold digit"));
  run "MATH-048 fires on \\mathbf{42}" (fun tag ->
      expect (fires "MATH-048" "$\\mathbf{42}$") (tag ^ ": bold number"));
  run "MATH-048 count=2" (fun tag ->
      expect
        (fires_with_count "MATH-048" "$\\mathbf{1} + \\mathbf{0}$" 2)
        (tag ^ ": count=2"));
  run "MATH-048 clean: \\mathbf{x}" (fun tag ->
      expect (does_not_fire "MATH-048" "$\\mathbf{x}$") (tag ^ ": letter ok"));
  run "MATH-048 clean: \\mathbf{abc}" (fun tag ->
      expect (does_not_fire "MATH-048" "$\\mathbf{abc}$") (tag ^ ": letters ok"));
  run "MATH-048 clean: no \\mathbf" (fun tag ->
      expect (does_not_fire "MATH-048" "$x + 1$") (tag ^ ": no mathbf"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-049: Missing spacing around \times
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-049 fires on a\\times b (no space before)" (fun tag ->
      expect (fires "MATH-049" "$a\\times b$") (tag ^ ": no space before"));
  run "MATH-049 fires on a \\times{b} (no space after)" (fun tag ->
      expect
        (fires "MATH-049" "$a \\times{b}$")
        (tag ^ ": no space after (brace)"));
  run "MATH-049 clean: a \\times b" (fun tag ->
      expect
        (does_not_fire "MATH-049" "$a \\times b$")
        (tag ^ ": proper spacing"));
  run "MATH-049 clean: no \\times" (fun tag ->
      expect (does_not_fire "MATH-049" "$a \\cdot b$") (tag ^ ": no times"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-050: \hat on multi-letter argument
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-050 fires on \\hat{xy}" (fun tag ->
      expect (fires "MATH-050" "$\\hat{xy}$") (tag ^ ": multi-letter hat"));
  run "MATH-050 fires on \\hat{abc}" (fun tag ->
      expect (fires "MATH-050" "$\\hat{abc}$") (tag ^ ": 3-letter hat"));
  run "MATH-050 count=2" (fun tag ->
      expect
        (fires_with_count "MATH-050" "$\\hat{ab} + \\hat{cd}$" 2)
        (tag ^ ": count=2"));
  run "MATH-050 clean: \\hat{x}" (fun tag ->
      expect (does_not_fire "MATH-050" "$\\hat{x}$") (tag ^ ": single letter"));
  run "MATH-050 clean: \\widehat{xy}" (fun tag ->
      expect (does_not_fire "MATH-050" "$\\widehat{xy}$") (tag ^ ": widehat ok"));
  run "MATH-050 clean: no hat" (fun tag ->
      expect (does_not_fire "MATH-050" "$x + y$") (tag ^ ": no hat"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-051: Nested \sqrt
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-051 fires on \\sqrt{\\sqrt{x}}" (fun tag ->
      expect (fires "MATH-051" "$\\sqrt{\\sqrt{x}}$") (tag ^ ": nested sqrt"));
  run "MATH-051 fires on \\sqrt[3]{\\sqrt{x}}" (fun tag ->
      expect
        (fires "MATH-051" "$\\sqrt[3]{\\sqrt{x}}$")
        (tag ^ ": nested sqrt with optional arg"));
  run "MATH-051 clean: single \\sqrt" (fun tag ->
      expect (does_not_fire "MATH-051" "$\\sqrt{x}$") (tag ^ ": single sqrt"));
  run "MATH-051 clean: \\sqrt then separate \\sqrt" (fun tag ->
      expect
        (does_not_fire "MATH-051" "$\\sqrt{x} + \\sqrt{y}$")
        (tag ^ ": adjacent but not nested"));
  run "MATH-051 clean: no sqrt" (fun tag ->
      expect (does_not_fire "MATH-051" "$x + y$") (tag ^ ": no sqrt"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-052: \over primitive used
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-052 fires on {a \\over b}" (fun tag ->
      expect (fires "MATH-052" "${a \\over b}$") (tag ^ ": \\over primitive"));
  run "MATH-052 fires on \\over at end" (fun tag ->
      expect (fires "MATH-052" "$a \\over$") (tag ^ ": \\over at end"));
  run "MATH-052 clean: \\frac{a}{b}" (fun tag ->
      expect (does_not_fire "MATH-052" "$\\frac{a}{b}$") (tag ^ ": frac ok"));
  run "MATH-052 clean: \\overbrace" (fun tag ->
      expect
        (does_not_fire "MATH-052" "$\\overbrace{abc}$")
        (tag ^ ": overbrace not flagged"));
  run "MATH-052 clean: \\overline" (fun tag ->
      expect
        (does_not_fire "MATH-052" "$\\overline{x}$")
        (tag ^ ": overline not flagged"));
  run "MATH-052 clean: \\overset" (fun tag ->
      expect
        (does_not_fire "MATH-052" "$\\overset{a}{=}$")
        (tag ^ ": overset not flagged"));
  run "MATH-052 clean: \\overrightarrow" (fun tag ->
      expect
        (does_not_fire "MATH-052" "$\\overrightarrow{AB}$")
        (tag ^ ": overrightarrow not flagged"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-053: Space after \left(
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-053 fires on \\left( x" (fun tag ->
      expect
        (fires "MATH-053" "$\\left( x \\right)$")
        (tag ^ ": space after \\left("));
  run "MATH-053 fires on \\left(  x (double space)" (fun tag ->
      expect (fires "MATH-053" "$\\left(  x\\right)$") (tag ^ ": double space"));
  run "MATH-053 clean: \\left(x (no space)" (fun tag ->
      expect
        (does_not_fire "MATH-053" "$\\left(x\\right)$")
        (tag ^ ": no space ok"));
  run "MATH-053 clean: no \\left(" (fun tag ->
      expect (does_not_fire "MATH-053" "$(x)$") (tag ^ ": no \\left("));
  run "MATH-053 clean: \\left\\{" (fun tag ->
      expect
        (does_not_fire "MATH-053" "$\\left\\{ x \\right\\}$")
        (tag ^ ": brace delim not affected"));

  (* ══════════════════════════════════════════════════════════════════════
     Cross-cutting edge cases
     ══════════════════════════════════════════════════════════════════════ *)
  run "empty input: no Batch B rules fire" (fun tag ->
      let results = Validators.run_all "" in
      let batch_b_fires =
        List.filter
          (fun (r : Validators.result) ->
            let id = r.id in
            let n = String.length id in
            n >= 5
            && String.sub id 0 5 = "MATH-"
            &&
            let num =
              try int_of_string (String.sub id 5 (n - 5)) with Failure _ -> 0
            in
            num >= 30 && num <= 53)
          results
      in
      expect (batch_b_fires = []) (tag ^ ": no Batch B on empty"));

  run "clean math: no Batch B rules fire" (fun tag ->
      let src = "$\\sin(x) + \\cos(y)$" in
      let results = Validators.run_all src in
      let batch_b_fires =
        List.filter
          (fun (r : Validators.result) ->
            let id = r.id in
            let n = String.length id in
            n >= 5
            && String.sub id 0 5 = "MATH-"
            &&
            let num =
              try int_of_string (String.sub id 5 (n - 5)) with Failure _ -> 0
            in
            num >= 30 && num <= 53)
          results
      in
      expect (batch_b_fires = []) (tag ^ ": no Batch B on clean"));

  run "text-only input: no Batch B fires" (fun tag ->
      let src = "This is plain text with no math at all." in
      let results = Validators.run_all src in
      let batch_b_fires =
        List.filter
          (fun (r : Validators.result) ->
            let id = r.id in
            let n = String.length id in
            n >= 5
            && String.sub id 0 5 = "MATH-"
            &&
            let num =
              try int_of_string (String.sub id 5 (n - 5)) with Failure _ -> 0
            in
            num >= 30 && num <= 53)
          results
      in
      expect (batch_b_fires = []) (tag ^ ": no Batch B on text-only"));

  (* Registration checks: verify all 23 rules are registered and fire *)
  run "registration: MATH-030 registered" (fun tag ->
      expect
        (fires "MATH-030" "$\\displaystyle x$")
        (tag ^ ": MATH-030 registered"));
  run "registration: MATH-038 registered" (fun tag ->
      expect
        (fires "MATH-038" "$\\frac{\\frac{\\frac{a}{b}}{c}}{d}$")
        (tag ^ ": MATH-038 registered"));
  run "registration: MATH-047 registered" (fun tag ->
      expect (fires "MATH-047" "$x^a^b$") (tag ^ ": MATH-047 registered"));
  run "registration: MATH-053 registered" (fun tag ->
      expect
        (fires "MATH-053" "$\\left( x\\right)$")
        (tag ^ ": MATH-053 registered"));

  (* Precondition checks *)
  run "precondition: MATH-030 maps to L1" (fun tag ->
      let layer = Validators.precondition_of_rule_id "MATH-030" in
      expect (layer = L1) (tag ^ ": L1 layer"));
  run "precondition: MATH-040 maps to L1" (fun tag ->
      let layer = Validators.precondition_of_rule_id "MATH-040" in
      expect (layer = L1) (tag ^ ": L1 layer"));
  run "precondition: MATH-053 maps to L1" (fun tag ->
      let layer = Validators.precondition_of_rule_id "MATH-053" in
      expect (layer = L1) (tag ^ ": L1 layer"));

  (* Combined: multiple Batch B issues in one source *)
  run "combined: multiple Batch B rules fire" (fun tag ->
      let src =
        "$\\displaystyle x + \\text{Var}(X) + \\hat{ab} + \\mathbf{42}$"
      in
      expect (fires "MATH-030" src) (tag ^ ": MATH-030 fires");
      expect (fires "MATH-043" src) (tag ^ ": MATH-043 fires");
      expect (fires "MATH-050" src) (tag ^ ": MATH-050 fires");
      expect (fires "MATH-048" src) (tag ^ ": MATH-048 fires"));

  (* Real-document style test: a paragraph with multiple math snippets *)
  run "real doc: mixed good and bad" (fun tag ->
      let src =
        "Let $f(x) = \\sin(x)$. Then $\\int f(x)dx$ is well-known. We note $x \
         <= y$ implies $\\text{Var}(X) \\ge 0$. Also $a, \\ldots, b$ is \
         shorthand."
      in
      (* MATH-034 should fire for \\int f(x)dx — need integral AND bare dx *)
      expect (fires "MATH-034" src) (tag ^ ": MATH-034 on bare dx in integral");
      (* MATH-044 should fire for <= *)
      expect (fires "MATH-044" src) (tag ^ ": MATH-044 on <=");
      (* MATH-043 should fire for \\text{Var} *)
      expect (fires "MATH-043" src) (tag ^ ": MATH-043 on \\text{Var}");
      (* MATH-046 should fire for , \\ldots , *)
      expect (fires "MATH-046" src) (tag ^ ": MATH-046 on comma ldots comma"));

  (* Math environment edge cases *)
  run "align env: MATH-030 does not fire for displaystyle" (fun tag ->
      expect
        (does_not_fire "MATH-030" "\\begin{align}\\displaystyle x\\end{align}")
        (tag ^ ": align env ok"));

  run "equation* env: MATH-047 fires inside" (fun tag ->
      expect
        (fires "MATH-047" "\\begin{equation*}x^a^b\\end{equation*}")
        (tag ^ ": equation* triggers"));

  (* Escaped dollar signs *)
  run "escaped dollar: not treated as math" (fun tag ->
      expect
        (does_not_fire "MATH-030" "Price is \\$\\displaystyle 5.")
        (tag ^ ": escaped $ ignored"))

(* -- MATH-C part 1: MATH-055..105 -------------------------------- *)
let () =
  (* ════════════════════════════════════════════════════════════════════
     MATH-055: \mathcal argument has multiple characters
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-055 fires on multi-char mathcal" (fun tag ->
      expect (fires "MATH-055" "$\\mathcal{AB}$") (tag ^ ": multi-char mathcal"));
  run "MATH-055 fires on three-char" (fun tag ->
      expect (fires "MATH-055" "$\\mathcal{XYZ}$") (tag ^ ": three chars"));
  run "MATH-055 count=2" (fun tag ->
      expect
        (fires_with_count "MATH-055" "$\\mathcal{AB} + \\mathcal{CD}$" 2)
        (tag ^ ": count=2"));
  run "MATH-055 severity=Info" (fun tag ->
      match find_result "MATH-055" "$\\mathcal{AB}$" with
      | Some r -> expect (r.severity = Validators.Info) (tag ^ ": Info")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-055 clean single char" (fun tag ->
      expect
        (does_not_fire "MATH-055" "$\\mathcal{A}$")
        (tag ^ ": single char ok"));
  run "MATH-055 clean no mathcal" (fun tag ->
      expect (does_not_fire "MATH-055" "$x + y$") (tag ^ ": no mathcal"));
  run "MATH-055 clean outside math" (fun tag ->
      expect (does_not_fire "MATH-055" "\\mathcal{AB}") (tag ^ ": outside math"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-057: Empty fraction numerator or denominator
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-057 fires on empty numerator" (fun tag ->
      expect (fires "MATH-057" "$\\frac{}{2}$") (tag ^ ": empty numerator"));
  run "MATH-057 fires on empty denominator" (fun tag ->
      expect (fires "MATH-057" "$\\frac{1}{}$") (tag ^ ": empty denom"));
  run "MATH-057 fires on frac with space in arg" (fun tag ->
      expect (fires "MATH-057" "$\\frac{ }{2}$") (tag ^ ": space in numerator"));
  run "MATH-057 severity=Error" (fun tag ->
      match find_result "MATH-057" "$\\frac{}{2}$" with
      | Some r -> expect (r.severity = Validators.Error) (tag ^ ": Error")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-057 count=2" (fun tag ->
      expect
        (fires_with_count "MATH-057" "$\\frac{}{x} + \\frac{}{y}$" 2)
        (tag ^ ": count=2"));
  run "MATH-057 clean normal frac" (fun tag ->
      expect (does_not_fire "MATH-057" "$\\frac{a}{b}$") (tag ^ ": normal frac"));
  run "MATH-057 clean no frac" (fun tag ->
      expect (does_not_fire "MATH-057" "$x + y$") (tag ^ ": no frac"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-058: Nested \text inside \text
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-058 fires on nested text" (fun tag ->
      expect
        (fires "MATH-058" "$\\text{foo \\text{bar}}$")
        (tag ^ ": nested text"));
  run "MATH-058 severity=Info" (fun tag ->
      match find_result "MATH-058" "$\\text{a \\text{b}}$" with
      | Some r -> expect (r.severity = Validators.Info) (tag ^ ": Info")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-058 count=2" (fun tag ->
      expect
        (fires_with_count "MATH-058"
           "$\\text{a \\text{b}} + \\text{c \\text{d}}$" 2)
        (tag ^ ": count=2"));
  run "MATH-058 clean single text" (fun tag ->
      expect
        (does_not_fire "MATH-058" "$\\text{hello world}$")
        (tag ^ ": single text"));
  run "MATH-058 clean no text" (fun tag ->
      expect (does_not_fire "MATH-058" "$x + y$") (tag ^ ": no text"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-065: Manual \hspace in math detected
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-065 fires on hspace in math" (fun tag ->
      expect (fires "MATH-065" "$a \\hspace{1cm} b$") (tag ^ ": hspace in math"));
  run "MATH-065 fires in display math" (fun tag ->
      expect
        (fires "MATH-065" "\\[a \\hspace{2cm} b\\]")
        (tag ^ ": hspace in display"));
  run "MATH-065 count=2" (fun tag ->
      expect
        (fires_with_count "MATH-065" "$\\hspace{1cm} + \\hspace{2cm}$" 2)
        (tag ^ ": count=2"));
  run "MATH-065 severity=Info" (fun tag ->
      match find_result "MATH-065" "$\\hspace{1cm}$" with
      | Some r -> expect (r.severity = Validators.Info) (tag ^ ": Info")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-065 clean no hspace" (fun tag ->
      expect (does_not_fire "MATH-065" "$a + b$") (tag ^ ": no hspace"));
  run "MATH-065 clean hspace outside math" (fun tag ->
      expect
        (does_not_fire "MATH-065" "\\hspace{1cm} text")
        (tag ^ ": outside math"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-066: \phantom used; suggest \hphantom or \vphantom
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-066 fires on phantom" (fun tag ->
      expect (fires "MATH-066" "$\\phantom{x}$") (tag ^ ": plain phantom"));
  run "MATH-066 severity=Info" (fun tag ->
      match find_result "MATH-066" "$\\phantom{x}$" with
      | Some r -> expect (r.severity = Validators.Info) (tag ^ ": Info")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-066 count=2" (fun tag ->
      expect
        (fires_with_count "MATH-066" "$\\phantom{a} + \\phantom{b}$" 2)
        (tag ^ ": count=2"));
  run "MATH-066 clean hphantom" (fun tag ->
      expect (does_not_fire "MATH-066" "$\\hphantom{x}$") (tag ^ ": hphantom ok"));
  run "MATH-066 clean vphantom" (fun tag ->
      expect (does_not_fire "MATH-066" "$\\vphantom{x}$") (tag ^ ": vphantom ok"));
  run "MATH-066 clean no phantom" (fun tag ->
      expect (does_not_fire "MATH-066" "$a + b$") (tag ^ ": no phantom"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-068: Spacing around \mid missing
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-068 fires on mid without leading space" (fun tag ->
      expect (fires "MATH-068" "$x\\mid y$") (tag ^ ": no leading space"));
  run "MATH-068 fires on mid without trailing space" (fun tag ->
      expect (fires "MATH-068" "$x \\midy$") (tag ^ ": no trailing space"));
  run "MATH-068 severity=Info" (fun tag ->
      match find_result "MATH-068" "$x\\mid y$" with
      | Some r -> expect (r.severity = Validators.Info) (tag ^ ": Info")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-068 clean with spaces" (fun tag ->
      expect (does_not_fire "MATH-068" "$x \\mid y$") (tag ^ ": spaces ok"));
  run "MATH-068 clean no mid" (fun tag ->
      expect (does_not_fire "MATH-068" "$x + y$") (tag ^ ": no mid"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-069: Bold sans-serif math font used
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-069 fires on mathbfsf" (fun tag ->
      expect (fires "MATH-069" "$\\mathbfsf{x}$") (tag ^ ": mathbfsf"));
  run "MATH-069 fires on bm+mathsf" (fun tag ->
      expect
        (fires "MATH-069" "$\\bm{\\mathsf{x}}$")
        (tag ^ ": bm wrapping mathsf"));
  run "MATH-069 severity=Info" (fun tag ->
      match find_result "MATH-069" "$\\mathbfsf{x}$" with
      | Some r -> expect (r.severity = Validators.Info) (tag ^ ": Info")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-069 clean mathsf alone" (fun tag ->
      expect
        (does_not_fire "MATH-069" "$\\mathsf{x}$")
        (tag ^ ": mathsf alone ok"));
  run "MATH-069 clean no font commands" (fun tag ->
      expect (does_not_fire "MATH-069" "$x + y$") (tag ^ ": no font cmds"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-071: Overuse of \cancel in equation (more than 3)
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-071 fires on 4+ cancels" (fun tag ->
      expect
        (fires "MATH-071"
           "$\\cancel{a} + \\cancel{b} + \\cancel{c} + \\cancel{d}$")
        (tag ^ ": 4 cancels"));
  run "MATH-071 severity=Info" (fun tag ->
      match
        find_result "MATH-071" "$\\cancel{a}\\cancel{b}\\cancel{c}\\cancel{d}$"
      with
      | Some r -> expect (r.severity = Validators.Info) (tag ^ ": Info")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-071 clean 3 cancels" (fun tag ->
      expect
        (does_not_fire "MATH-071" "$\\cancel{a} + \\cancel{b} + \\cancel{c}$")
        (tag ^ ": 3 cancels ok"));
  run "MATH-071 clean 1 cancel" (fun tag ->
      expect (does_not_fire "MATH-071" "$\\cancel{x}$") (tag ^ ": 1 cancel ok"));
  run "MATH-071 clean no cancel" (fun tag ->
      expect (does_not_fire "MATH-071" "$x + y$") (tag ^ ": no cancel"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-078: Long arrow typed as --> instead of \longrightarrow
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-078 fires on -->" (fun tag ->
      expect (fires "MATH-078" "$a --> b$") (tag ^ ": --> in math"));
  run "MATH-078 count=2" (fun tag ->
      expect
        (fires_with_count "MATH-078" "$a --> b --> c$" 2)
        (tag ^ ": count=2"));
  run "MATH-078 severity=Info" (fun tag ->
      match find_result "MATH-078" "$a --> b$" with
      | Some r -> expect (r.severity = Validators.Info) (tag ^ ": Info")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-078 clean longrightarrow" (fun tag ->
      expect
        (does_not_fire "MATH-078" "$a \\longrightarrow b$")
        (tag ^ ": proper command"));
  run "MATH-078 clean single dash" (fun tag ->
      expect (does_not_fire "MATH-078" "$a - b$") (tag ^ ": single dash"));
  run "MATH-078 clean outside math" (fun tag ->
      expect (does_not_fire "MATH-078" "a --> b") (tag ^ ": outside math"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-079: \displaystyle inside display math — redundant
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-079 fires in \\[...\\]" (fun tag ->
      expect
        (fires "MATH-079" "\\[\\displaystyle x + y\\]")
        (tag ^ ": displaystyle in \\[\\]"));
  run "MATH-079 fires in equation env" (fun tag ->
      expect
        (fires "MATH-079" "\\begin{equation}\n\\displaystyle x\n\\end{equation}")
        (tag ^ ": displaystyle in equation"));
  run "MATH-079 fires in align env" (fun tag ->
      expect
        (fires "MATH-079" "\\begin{align}\n\\displaystyle x &= y\n\\end{align}")
        (tag ^ ": displaystyle in align"));
  run "MATH-079 severity=Info" (fun tag ->
      match find_result "MATH-079" "\\[\\displaystyle x\\]" with
      | Some r -> expect (r.severity = Validators.Info) (tag ^ ": Info")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-079 clean in inline math" (fun tag ->
      expect
        (does_not_fire "MATH-079" "$\\displaystyle x + y$")
        (tag ^ ": inline ok"));
  run "MATH-079 clean no displaystyle" (fun tag ->
      expect (does_not_fire "MATH-079" "\\[x + y\\]") (tag ^ ": no cmd"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-082: Negative thin space \! used twice consecutively
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-082 fires on double negative thin space" (fun tag ->
      expect (fires "MATH-082" "$a\\!\\!b$") (tag ^ ": \\!\\!"));
  run "MATH-082 severity=Warning" (fun tag ->
      match find_result "MATH-082" "$a\\!\\!b$" with
      | Some r -> expect (r.severity = Validators.Warning) (tag ^ ": Warning")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-082 count=2" (fun tag ->
      expect
        (fires_with_count "MATH-082" "$\\!\\! + \\!\\!$" 2)
        (tag ^ ": count=2"));
  run "MATH-082 clean single thin space" (fun tag ->
      expect (does_not_fire "MATH-082" "$a\\!b$") (tag ^ ": single ok"));
  run "MATH-082 clean no thin space" (fun tag ->
      expect (does_not_fire "MATH-082" "$a + b$") (tag ^ ": no \\!"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-085: Use of \eqcirc — rarely acceptable
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-085 fires on eqcirc" (fun tag ->
      expect (fires "MATH-085" "$a \\eqcirc b$") (tag ^ ": eqcirc"));
  run "MATH-085 severity=Info" (fun tag ->
      match find_result "MATH-085" "$a \\eqcirc b$" with
      | Some r -> expect (r.severity = Validators.Info) (tag ^ ": Info")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-085 count=2" (fun tag ->
      expect
        (fires_with_count "MATH-085" "$\\eqcirc + \\eqcirc$" 2)
        (tag ^ ": count=2"));
  run "MATH-085 clean no eqcirc" (fun tag ->
      expect (does_not_fire "MATH-085" "$a \\approx b$") (tag ^ ": no eqcirc"));
  run "MATH-085 clean outside math" (fun tag ->
      expect (does_not_fire "MATH-085" "\\eqcirc text") (tag ^ ": outside math"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-094: Manual \kern in math detected
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-094 fires on kern in math" (fun tag ->
      expect (fires "MATH-094" "$a \\kern 2pt b$") (tag ^ ": kern in math"));
  run "MATH-094 fires in display math" (fun tag ->
      expect
        (fires "MATH-094" "\\[a \\kern 3mu b\\]")
        (tag ^ ": kern in display"));
  run "MATH-094 severity=Info" (fun tag ->
      match find_result "MATH-094" "$a \\kern 1pt b$" with
      | Some r -> expect (r.severity = Validators.Info) (tag ^ ": Info")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-094 count=2" (fun tag ->
      expect
        (fires_with_count "MATH-094" "$\\kern 1pt + \\kern 2pt$" 2)
        (tag ^ ": count=2"));
  run "MATH-094 clean no kern" (fun tag ->
      expect (does_not_fire "MATH-094" "$a + b$") (tag ^ ": no kern"));
  run "MATH-094 clean outside math" (fun tag ->
      expect
        (does_not_fire "MATH-094" "\\kern 1pt text")
        (tag ^ ": outside math"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-105: \textstyle inside display math — redundant
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-105 fires in \\[...\\]" (fun tag ->
      expect
        (fires "MATH-105" "\\[\\textstyle x + y\\]")
        (tag ^ ": textstyle in \\[\\]"));
  run "MATH-105 fires in equation env" (fun tag ->
      expect
        (fires "MATH-105" "\\begin{equation}\n\\textstyle x\n\\end{equation}")
        (tag ^ ": textstyle in equation"));
  run "MATH-105 fires in align env" (fun tag ->
      expect
        (fires "MATH-105" "\\begin{align}\n\\textstyle x &= y\n\\end{align}")
        (tag ^ ": textstyle in align"));
  run "MATH-105 severity=Info" (fun tag ->
      match find_result "MATH-105" "\\[\\textstyle x\\]" with
      | Some r -> expect (r.severity = Validators.Info) (tag ^ ": Info")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-105 clean in inline math" (fun tag ->
      expect
        (does_not_fire "MATH-105" "$\\textstyle x + y$")
        (tag ^ ": inline ok"));
  run "MATH-105 clean no textstyle" (fun tag ->
      expect (does_not_fire "MATH-105" "\\[x + y\\]") (tag ^ ": no cmd"));

  (* ════════════════════════════════════════════════════════════════════ Empty
     input
     ════════════════════════════════════════════════════════════════════ *)
  run "empty input fires nothing" (fun tag ->
      let results = Validators.run_all "" in
      let math_c =
        List.filter
          (fun (r : Validators.result) ->
            List.mem r.id
              [
                "MATH-055";
                "MATH-057";
                "MATH-058";
                "MATH-065";
                "MATH-066";
                "MATH-068";
                "MATH-069";
                "MATH-071";
                "MATH-078";
                "MATH-079";
                "MATH-082";
                "MATH-085";
                "MATH-094";
                "MATH-105";
              ])
          results
      in
      expect (math_c = []) (tag ^ ": no fires on empty"))

(* -- MATH-C part 2: MATH-056..098 -------------------------------- *)
let () =
  (* ════════════════════════════════════════════════════════════════════
     MATH-056: \operatorname duplicated for same function
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-056 fires on duplicated operatorname" (fun tag ->
      expect
        (fires "MATH-056" "$\\operatorname{Tr}(A) + \\operatorname{Tr}(B)$")
        (tag ^ ": duplicated Tr"));
  run "MATH-056 severity=Info" (fun tag ->
      match
        find_result "MATH-056" "$\\operatorname{Tr}(A) + \\operatorname{Tr}(B)$"
      with
      | Some r -> expect (r.severity = Validators.Info) (tag ^ ": Info")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-056 clean different operatornames" (fun tag ->
      expect
        (does_not_fire "MATH-056"
           "$\\operatorname{Tr}(A) + \\operatorname{rank}(B)$")
        (tag ^ ": different names ok"));
  run "MATH-056 clean single operatorname" (fun tag ->
      expect
        (does_not_fire "MATH-056" "$\\operatorname{Tr}(A)$")
        (tag ^ ": single ok"));
  run "MATH-056 clean no operatorname" (fun tag ->
      expect (does_not_fire "MATH-056" "$x + y$") (tag ^ ": none"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-059: \bar on group expression with operators/spaces
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-059 fires on bar with operator" (fun tag ->
      expect (fires "MATH-059" "$\\bar{a + b}$") (tag ^ ": bar with +"));
  run "MATH-059 fires on bar with space" (fun tag ->
      expect (fires "MATH-059" "$\\bar{x y}$") (tag ^ ": bar with space"));
  run "MATH-059 severity=Warning" (fun tag ->
      match find_result "MATH-059" "$\\bar{a + b}$" with
      | Some r -> expect (r.severity = Validators.Warning) (tag ^ ": Warning")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-059 clean single char" (fun tag ->
      expect (does_not_fire "MATH-059" "$\\bar{x}$") (tag ^ ": single char ok"));
  run "MATH-059 clean no bar" (fun tag ->
      expect (does_not_fire "MATH-059" "$x + y$") (tag ^ ": no bar"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-060: Differential d typeset italic
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-060 fires on italic d in integral" (fun tag ->
      expect (fires "MATH-060" "$\\int f(x) dx$") (tag ^ ": italic dx"));
  run "MATH-060 severity=Info" (fun tag ->
      match find_result "MATH-060" "$\\int f(x) dx$" with
      | Some r -> expect (r.severity = Validators.Info) (tag ^ ": Info")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-060 clean mathrm d" (fun tag ->
      expect
        (does_not_fire "MATH-060" "$\\int f(x) \\mathrm{d}x$")
        (tag ^ ": mathrm d ok"));
  run "MATH-060 clean no integral" (fun tag ->
      expect (does_not_fire "MATH-060" "$f(x) dx$") (tag ^ ": no integral"));
  run "MATH-060 clean no d" (fun tag ->
      expect (does_not_fire "MATH-060" "$\\int f(x)$") (tag ^ ": no d"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-061: Log base missing braces
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-061 fires on log_10x" (fun tag ->
      expect (fires "MATH-061" "$\\log_10 x$") (tag ^ ": log_10x"));
  run "MATH-061 fires on log_2n" (fun tag ->
      expect (fires "MATH-061" "$\\log_2n$") (tag ^ ": log_2n"));
  run "MATH-061 severity=Warning" (fun tag ->
      match find_result "MATH-061" "$\\log_10 x$" with
      | Some r -> expect (r.severity = Validators.Warning) (tag ^ ": Warning")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-061 clean braced base" (fun tag ->
      expect (does_not_fire "MATH-061" "$\\log_{10} x$") (tag ^ ": braced ok"));
  run "MATH-061 clean no log" (fun tag ->
      expect (does_not_fire "MATH-061" "$x + y$") (tag ^ ": no log"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-067: \limits on non-big-operator
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-067 fires on limits on non-operator" (fun tag ->
      expect (fires "MATH-067" "$A\\limits_{i}$") (tag ^ ": limits on A"));
  run "MATH-067 severity=Warning" (fun tag ->
      match find_result "MATH-067" "$A\\limits_{i}$" with
      | Some r -> expect (r.severity = Validators.Warning) (tag ^ ": Warning")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-067 clean on sum" (fun tag ->
      expect
        (does_not_fire "MATH-067" "$\\sum\\limits_{i=1}^{n}$")
        (tag ^ ": sum ok"));
  run "MATH-067 clean on int" (fun tag ->
      expect
        (does_not_fire "MATH-067" "$\\int\\limits_{0}^{1}$")
        (tag ^ ": int ok"));
  run "MATH-067 clean on prod" (fun tag ->
      expect
        (does_not_fire "MATH-067" "$\\prod\\limits_{i}$")
        (tag ^ ": prod ok"));
  run "MATH-067 clean on bigcup" (fun tag ->
      expect
        (does_not_fire "MATH-067" "$\\bigcup\\limits_{i}$")
        (tag ^ ": bigcup ok"));
  run "MATH-067 clean no limits" (fun tag ->
      expect (does_not_fire "MATH-067" "$x + y$") (tag ^ ": no limits"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-070: Multiline subscripts without \substack
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-070 fires on multiline subscript" (fun tag ->
      expect
        (fires "MATH-070" "$\\sum_{i=1\\\\j=2}$")
        (tag ^ ": \\\\ in subscript"));
  run "MATH-070 severity=Info" (fun tag ->
      match find_result "MATH-070" "$\\sum_{i=1\\\\j=2}$" with
      | Some r -> expect (r.severity = Validators.Info) (tag ^ ": Info")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-070 clean with substack" (fun tag ->
      expect
        (does_not_fire "MATH-070" "$\\sum_{\\substack{i=1\\\\j=2}}$")
        (tag ^ ": substack ok"));
  run "MATH-070 clean single-line subscript" (fun tag ->
      expect
        (does_not_fire "MATH-070" "$\\sum_{i=1}$")
        (tag ^ ": single line ok"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-073: \color used inside math
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-073 fires on color in math" (fun tag ->
      expect (fires "MATH-073" "$\\color{red} x + y$") (tag ^ ": color in math"));
  run "MATH-073 fires in display math" (fun tag ->
      expect
        (fires "MATH-073" "\\[\\color{blue} a\\]")
        (tag ^ ": color in display"));
  run "MATH-073 severity=Warning" (fun tag ->
      match find_result "MATH-073" "$\\color{red} x$" with
      | Some r -> expect (r.severity = Validators.Warning) (tag ^ ": Warning")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-073 count=2" (fun tag ->
      expect
        (fires_with_count "MATH-073" "$\\color{red} x + \\color{blue} y$" 2)
        (tag ^ ": count=2"));
  run "MATH-073 clean no color" (fun tag ->
      expect (does_not_fire "MATH-073" "$x + y$") (tag ^ ": no color"));
  run "MATH-073 clean color outside math" (fun tag ->
      expect
        (does_not_fire "MATH-073" "\\color{red} text")
        (tag ^ ": outside math"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-077: Alignment point & outside alignment environment
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-077 fires on & in equation" (fun tag ->
      expect
        (fires "MATH-077" "\\begin{equation}\nx & = y\n\\end{equation}")
        (tag ^ ": & in equation"));
  run "MATH-077 fires in gather" (fun tag ->
      expect
        (fires "MATH-077" "\\begin{gather}\nx & y\n\\end{gather}")
        (tag ^ ": & in gather"));
  run "MATH-077 severity=Error" (fun tag ->
      match
        find_result "MATH-077" "\\begin{equation}\nx & = y\n\\end{equation}"
      with
      | Some r -> expect (r.severity = Validators.Error) (tag ^ ": Error")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-077 clean & in align" (fun tag ->
      expect
        (does_not_fire "MATH-077" "\\begin{align}\nx &= y\n\\end{align}")
        (tag ^ ": align ok"));
  run "MATH-077 clean & in array" (fun tag ->
      expect
        (does_not_fire "MATH-077" "\\begin{array}{cc}\na & b\n\\end{array}")
        (tag ^ ": array ok"));
  run "MATH-077 clean no &" (fun tag ->
      expect
        (does_not_fire "MATH-077" "\\begin{equation}\nx = y\n\\end{equation}")
        (tag ^ ": no &"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-081: Function call f(x) without kern
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-081 fires on f(x)" (fun tag ->
      expect (fires "MATH-081" "$f(x)$") (tag ^ ": f(x)"));
  run "MATH-081 severity=Info" (fun tag ->
      match find_result "MATH-081" "$f(x)$" with
      | Some r -> expect (r.severity = Validators.Info) (tag ^ ": Info")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-081 clean with kern" (fun tag ->
      expect (does_not_fire "MATH-081" "$f\\!(x)$") (tag ^ ": kern ok"));
  run "MATH-081 clean with left" (fun tag ->
      expect
        (does_not_fire "MATH-081" "$f\\left(x\\right)$")
        (tag ^ ": left/right ok"));
  run "MATH-081 clean no parens" (fun tag ->
      expect (does_not_fire "MATH-081" "$f + g$") (tag ^ ": no parens"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-084: Displaystyle \sum in inline math
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-084 fires on displaystyle sum in inline" (fun tag ->
      expect
        (fires "MATH-084" "$\\displaystyle\\sum_{i=1}^{n} x_i$")
        (tag ^ ": displaystyle sum inline"));
  run "MATH-084 severity=Info" (fun tag ->
      match find_result "MATH-084" "$\\displaystyle\\sum_{i=1}^{n}$" with
      | Some r -> expect (r.severity = Validators.Info) (tag ^ ": Info")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-084 clean in display math" (fun tag ->
      expect
        (does_not_fire "MATH-084" "\\[\\displaystyle\\sum_{i=1}^{n}\\]")
        (tag ^ ": display ok"));
  run "MATH-084 clean no displaystyle" (fun tag ->
      expect
        (does_not_fire "MATH-084" "$\\sum_{i=1}^{n}$")
        (tag ^ ": no displaystyle"));
  run "MATH-084 clean no sum" (fun tag ->
      expect (does_not_fire "MATH-084" "$\\displaystyle x$") (tag ^ ": no sum"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-086: Nested \sqrt depth > 2
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-086 fires on nested sqrt" (fun tag ->
      expect (fires "MATH-086" "$\\sqrt{\\sqrt{x}}$") (tag ^ ": double nested"));
  run "MATH-086 severity=Warning" (fun tag ->
      match find_result "MATH-086" "$\\sqrt{\\sqrt{x}}$" with
      | Some r -> expect (r.severity = Validators.Warning) (tag ^ ": Warning")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-086 clean single sqrt" (fun tag ->
      expect (does_not_fire "MATH-086" "$\\sqrt{x}$") (tag ^ ": single ok"));
  run "MATH-086 clean no sqrt" (fun tag ->
      expect (does_not_fire "MATH-086" "$x + y$") (tag ^ ": no sqrt"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-090: Nested \frac depth > 3
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-090 fires on triple nested frac" (fun tag ->
      expect
        (fires "MATH-090" "$\\frac{\\frac{\\frac{a}{b}}{c}}{d}$")
        (tag ^ ": triple nested"));
  run "MATH-090 severity=Warning" (fun tag ->
      match find_result "MATH-090" "$\\frac{\\frac{\\frac{a}{b}}{c}}{d}$" with
      | Some r -> expect (r.severity = Validators.Warning) (tag ^ ": Warning")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-090 clean double nested" (fun tag ->
      expect
        (does_not_fire "MATH-090" "$\\frac{\\frac{a}{b}}{c}$")
        (tag ^ ": double ok"));
  run "MATH-090 clean single frac" (fun tag ->
      expect (does_not_fire "MATH-090" "$\\frac{a}{b}$") (tag ^ ": single ok"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-093: Multi-letter italic variable
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-093 fires on multi-letter var" (fun tag ->
      expect (fires "MATH-093" "$speed + velocity$") (tag ^ ": speed, velocity"));
  run "MATH-093 severity=Info" (fun tag ->
      match find_result "MATH-093" "$speed = 10$" with
      | Some r -> expect (r.severity = Validators.Info) (tag ^ ": Info")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-093 clean known function" (fun tag ->
      expect
        (does_not_fire "MATH-093" "$\\sin + \\cos$")
        (tag ^ ": known funcs ok"));
  run "MATH-093 clean single letter vars" (fun tag ->
      expect
        (does_not_fire "MATH-093" "$x + y + z$")
        (tag ^ ": single letter ok"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-098: Too many \qquad in single math line
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-098 fires on 3+ qquad" (fun tag ->
      expect
        (fires "MATH-098" "$a \\qquad b \\qquad c \\qquad d$")
        (tag ^ ": 3 qquad"));
  run "MATH-098 severity=Info" (fun tag ->
      match find_result "MATH-098" "$a \\qquad b \\qquad c \\qquad d$" with
      | Some r -> expect (r.severity = Validators.Info) (tag ^ ": Info")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-098 clean 2 qquad" (fun tag ->
      expect
        (does_not_fire "MATH-098" "$a \\qquad b \\qquad c$")
        (tag ^ ": 2 qquad ok"));
  run "MATH-098 clean no qquad" (fun tag ->
      expect (does_not_fire "MATH-098" "$a + b$") (tag ^ ": no qquad"));

  (* ════════════════════════════════════════════════════════════════════ Empty
     input
     ════════════════════════════════════════════════════════════════════ *)
  run "empty input fires nothing" (fun tag ->
      let results = Validators.run_all "" in
      let math_c2 =
        List.filter
          (fun (r : Validators.result) ->
            List.mem r.id
              [
                "MATH-056";
                "MATH-059";
                "MATH-060";
                "MATH-061";
                "MATH-067";
                "MATH-070";
                "MATH-073";
                "MATH-077";
                "MATH-081";
                "MATH-084";
                "MATH-086";
                "MATH-090";
                "MATH-093";
                "MATH-098";
              ])
          results
      in
      expect (math_c2 = []) (tag ^ ": no fires on empty"))

(* -- MATH-C part 3: MATH-072..108 -------------------------------- *)
let () =
  (* ════════════════════════════════════════════════════════════════════
     MATH-072: \operatorname for predefined function
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-072 fires on operatorname{det}" (fun tag ->
      expect (fires "MATH-072" "$\\operatorname{det}(A)$") (tag ^ ": det"));
  run "MATH-072 fires on operatorname{sin}" (fun tag ->
      expect (fires "MATH-072" "$\\operatorname{sin}(x)$") (tag ^ ": sin"));
  run "MATH-072 severity=Warning" (fun tag ->
      match find_result "MATH-072" "$\\operatorname{det}(A)$" with
      | Some r -> expect (r.severity = Validators.Warning) (tag ^ ": Warning")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-072 clean custom operator" (fun tag ->
      expect
        (does_not_fire "MATH-072" "$\\operatorname{Tr}(A)$")
        (tag ^ ": custom Tr ok"));
  run "MATH-072 clean no operatorname" (fun tag ->
      expect (does_not_fire "MATH-072" "$\\det(A)$") (tag ^ ": none"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-074: TikZ \node inside math without math mode key
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-074 fires on node in math" (fun tag ->
      expect (fires "MATH-074" "$\\node at (0,0) {x};$") (tag ^ ": node in math"));
  run "MATH-074 severity=Warning" (fun tag ->
      match find_result "MATH-074" "$\\node at (0,0) {x};$" with
      | Some r -> expect (r.severity = Validators.Warning) (tag ^ ": Warning")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-074 clean with math mode" (fun tag ->
      expect
        (does_not_fire "MATH-074" "$\\node[math mode] at (0,0) {x};$")
        (tag ^ ": math mode ok"));
  run "MATH-074 clean no node" (fun tag ->
      expect (does_not_fire "MATH-074" "$x + y$") (tag ^ ": no node"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-087: Fake bold digits via \mathbf
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-087 fires on mathbf digits" (fun tag ->
      expect (fires "MATH-087" "$\\mathbf{42}$") (tag ^ ": bold digits"));
  run "MATH-087 fires on single digit" (fun tag ->
      expect (fires "MATH-087" "$\\mathbf{0}$") (tag ^ ": single digit"));
  run "MATH-087 severity=Info" (fun tag ->
      match find_result "MATH-087" "$\\mathbf{42}$" with
      | Some r -> expect (r.severity = Validators.Info) (tag ^ ": Info")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-087 clean mathbf letters" (fun tag ->
      expect (does_not_fire "MATH-087" "$\\mathbf{ABC}$") (tag ^ ": letters ok"));
  run "MATH-087 clean no mathbf" (fun tag ->
      expect (does_not_fire "MATH-087" "$42$") (tag ^ ": no mathbf"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-088: Bare \partial lacks thin space
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-088 fires on partial without spacing" (fun tag ->
      expect
        (fires "MATH-088" "$x\\partial y$")
        (tag ^ ": no space around partial"));
  run "MATH-088 severity=Info" (fun tag ->
      match find_result "MATH-088" "$x\\partial y$" with
      | Some r -> expect (r.severity = Validators.Info) (tag ^ ": Info")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-088 clean with spacing" (fun tag ->
      expect (does_not_fire "MATH-088" "$\\partial{f}$") (tag ^ ": braced ok"));
  run "MATH-088 clean no partial" (fun tag ->
      expect (does_not_fire "MATH-088" "$x + y$") (tag ^ ": no partial"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-091: \operatorname{X} when predefined \X exists
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-091 fires on operatorname{det}" (fun tag ->
      expect (fires "MATH-091" "$\\operatorname{det}(A)$") (tag ^ ": det"));
  run "MATH-091 fires on operatorname{lim}" (fun tag ->
      expect (fires "MATH-091" "$\\operatorname{lim}_{n}$") (tag ^ ": lim"));
  run "MATH-091 severity=Info" (fun tag ->
      match find_result "MATH-091" "$\\operatorname{sin}(x)$" with
      | Some r -> expect (r.severity = Validators.Info) (tag ^ ": Info")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-091 clean custom op" (fun tag ->
      expect
        (does_not_fire "MATH-091" "$\\operatorname{Tr}(A)$")
        (tag ^ ": custom Tr"));
  run "MATH-091 clean no operatorname" (fun tag ->
      expect (does_not_fire "MATH-091" "$\\sin(x)$") (tag ^ ": none"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-092: \sum with explicit limits in inline math
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-092 fires on sum with limits inline" (fun tag ->
      expect (fires "MATH-092" "$\\sum_{i=1}^{n} x_i$") (tag ^ ": sum_ inline"));
  run "MATH-092 severity=Info" (fun tag ->
      match find_result "MATH-092" "$\\sum_{i}$" with
      | Some r -> expect (r.severity = Validators.Info) (tag ^ ": Info")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-092 clean in display math" (fun tag ->
      expect
        (does_not_fire "MATH-092" "\\[\\sum_{i=1}^{n}\\]")
        (tag ^ ": display ok"));
  run "MATH-092 clean sum without limits" (fun tag ->
      expect (does_not_fire "MATH-092" "$\\sum x_i$") (tag ^ ": no limits ok"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-095: Log base without braces (alias of MATH-061)
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-095 fires on log_10x" (fun tag ->
      expect (fires "MATH-095" "$\\log_10 x$") (tag ^ ": log_10x"));
  run "MATH-095 severity=Warning" (fun tag ->
      match find_result "MATH-095" "$\\log_10 x$" with
      | Some r -> expect (r.severity = Validators.Warning) (tag ^ ": Warning")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-095 clean braced" (fun tag ->
      expect (does_not_fire "MATH-095" "$\\log_{10} x$") (tag ^ ": braced ok"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-096: Bold Greek via \mathbf
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-096 fires on mathbf{alpha}" (fun tag ->
      expect (fires "MATH-096" "$\\mathbf{\\alpha}$") (tag ^ ": bold alpha"));
  run "MATH-096 fires on mathbf{Gamma}" (fun tag ->
      expect (fires "MATH-096" "$\\mathbf{\\Gamma}$") (tag ^ ": bold Gamma"));
  run "MATH-096 severity=Info" (fun tag ->
      match find_result "MATH-096" "$\\mathbf{\\alpha}$" with
      | Some r -> expect (r.severity = Validators.Info) (tag ^ ": Info")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-096 clean boldsymbol" (fun tag ->
      expect
        (does_not_fire "MATH-096" "$\\boldsymbol{\\alpha}$")
        (tag ^ ": boldsymbol ok"));
  run "MATH-096 clean mathbf on letters" (fun tag ->
      expect (does_not_fire "MATH-096" "$\\mathbf{x}$") (tag ^ ": non-Greek ok"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-097: Arrow => instead of \implies
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-097 fires on =>" (fun tag ->
      expect (fires "MATH-097" "$a => b$") (tag ^ ": => in math"));
  run "MATH-097 severity=Info" (fun tag ->
      match find_result "MATH-097" "$a => b$" with
      | Some r -> expect (r.severity = Validators.Info) (tag ^ ": Info")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-097 clean implies" (fun tag ->
      expect (does_not_fire "MATH-097" "$a \\implies b$") (tag ^ ": implies ok"));
  run "MATH-097 clean >=" (fun tag ->
      expect (does_not_fire "MATH-097" "$a >= b$") (tag ^ ": >= ok"));
  run "MATH-097 clean outside math" (fun tag ->
      expect (does_not_fire "MATH-097" "a => b") (tag ^ ": outside math"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-099: Large operator in inline math
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-099 fires on bigcup inline" (fun tag ->
      expect (fires "MATH-099" "$\\bigcup_{i} A_i$") (tag ^ ": bigcup inline"));
  run "MATH-099 fires on bigcap inline" (fun tag ->
      expect (fires "MATH-099" "$\\bigcap_{i} A_i$") (tag ^ ": bigcap inline"));
  run "MATH-099 fires on bigoplus inline" (fun tag ->
      expect
        (fires "MATH-099" "$\\bigoplus_{i} V_i$")
        (tag ^ ": bigoplus inline"));
  run "MATH-099 severity=Info" (fun tag ->
      match find_result "MATH-099" "$\\bigcup_{i} A_i$" with
      | Some r -> expect (r.severity = Validators.Info) (tag ^ ": Info")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-099 clean in display math" (fun tag ->
      expect
        (does_not_fire "MATH-099" "\\[\\bigcup_{i} A_i\\]")
        (tag ^ ": display ok"));
  run "MATH-099 clean no big ops" (fun tag ->
      expect (does_not_fire "MATH-099" "$x + y$") (tag ^ ": no ops"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-101: Deprecated \over primitive
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-101 fires on over" (fun tag ->
      expect (fires "MATH-101" "$a \\over b$") (tag ^ ": over"));
  run "MATH-101 severity=Warning" (fun tag ->
      match find_result "MATH-101" "$a \\over b$" with
      | Some r -> expect (r.severity = Validators.Warning) (tag ^ ": Warning")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-101 count=2" (fun tag ->
      expect
        (fires_with_count "MATH-101" "$a \\over b + c \\over d$" 2)
        (tag ^ ": count=2"));
  run "MATH-101 clean frac" (fun tag ->
      expect (does_not_fire "MATH-101" "$\\frac{a}{b}$") (tag ^ ": frac ok"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-104: Repeated \left(\right) pairs
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-104 fires on 3+ left/right pairs" (fun tag ->
      expect
        (fires "MATH-104"
           "$\\left(a\\right) + \\left(b\\right) + \\left(c\\right)$")
        (tag ^ ": 3 pairs"));
  run "MATH-104 severity=Info" (fun tag ->
      match
        find_result "MATH-104"
          "$\\left(a\\right) \\left(b\\right) \\left(c\\right)$"
      with
      | Some r -> expect (r.severity = Validators.Info) (tag ^ ": Info")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-104 clean 2 pairs" (fun tag ->
      expect
        (does_not_fire "MATH-104" "$\\left(a\\right) + \\left(b\\right)$")
        (tag ^ ": 2 pairs ok"));
  run "MATH-104 clean no left" (fun tag ->
      expect (does_not_fire "MATH-104" "$(a) + (b)$") (tag ^ ": no left"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-106: \not= used — prefer \neq
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-106 fires on not=" (fun tag ->
      expect (fires "MATH-106" "$a \\not= b$") (tag ^ ": not="));
  run "MATH-106 severity=Info" (fun tag ->
      match find_result "MATH-106" "$a \\not= b$" with
      | Some r -> expect (r.severity = Validators.Info) (tag ^ ": Info")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-106 count=2" (fun tag ->
      expect
        (fires_with_count "MATH-106" "$a \\not= b \\not= c$" 2)
        (tag ^ ": count=2"));
  run "MATH-106 clean neq" (fun tag ->
      expect (does_not_fire "MATH-106" "$a \\neq b$") (tag ^ ": neq ok"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-108: Middle dot U+00B7 in math — use \cdot
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-108 fires on middle dot" (fun tag ->
      expect (fires "MATH-108" "$a \xc2\xb7 b$") (tag ^ ": middle dot"));
  run "MATH-108 severity=Info" (fun tag ->
      match find_result "MATH-108" "$a \xc2\xb7 b$" with
      | Some r -> expect (r.severity = Validators.Info) (tag ^ ": Info")
      | None -> expect false (tag ^ ": should fire"));
  run "MATH-108 clean cdot" (fun tag ->
      expect (does_not_fire "MATH-108" "$a \\cdot b$") (tag ^ ": cdot ok"));
  run "MATH-108 clean outside math" (fun tag ->
      expect (does_not_fire "MATH-108" "a \xc2\xb7 b") (tag ^ ": outside math"));

  (* ════════════════════════════════════════════════════════════════════ Empty
     input
     ════════════════════════════════════════════════════════════════════ *)
  run "empty input fires nothing" (fun tag ->
      let results = Validators.run_all "" in
      let math_c3 =
        List.filter
          (fun (r : Validators.result) ->
            List.mem r.id
              [
                "MATH-072";
                "MATH-074";
                "MATH-087";
                "MATH-088";
                "MATH-091";
                "MATH-092";
                "MATH-095";
                "MATH-096";
                "MATH-097";
                "MATH-099";
                "MATH-101";
                "MATH-104";
                "MATH-106";
                "MATH-108";
              ])
          results
      in
      expect (math_c3 = []) (tag ^ ": no fires on empty"))

let () = finalise "math"
