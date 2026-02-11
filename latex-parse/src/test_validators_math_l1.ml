(** Unit tests for L1 MATH validator rules (core math-token validators).
    MATH-009 through MATH-022. *)

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
      expect (fires "MATH-022" src) (tag ^ ": MATH-022 fires"));

  (* Summary *)
  Printf.printf "[math-l1] %s %d cases\n"
    (if !fails = 0 then "PASS" else "FAIL")
    !cases;
  if !fails > 0 then (
    Printf.eprintf "[math-l1] %d / %d failures\n" !fails !cases;
    exit 1)
