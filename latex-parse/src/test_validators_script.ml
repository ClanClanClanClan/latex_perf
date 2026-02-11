(** Unit tests for SCRIPT validator rules (L1 subscript/superscript). SCRIPT-001
    through SCRIPT-022. *)

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
     SCRIPT-001: Multi-char subscript without braces
     ══════════════════════════════════════════════════════════════════════ *)
  run "SCRIPT-001 fires on _ab" (fun tag ->
      expect (fires "SCRIPT-001" "$x_ab$") (tag ^ ": _ab"));
  run "SCRIPT-001 fires on _xyz" (fun tag ->
      expect (fires "SCRIPT-001" "$a_xyz + b$") (tag ^ ": _xyz"));
  run "SCRIPT-001 clean: _{ab}" (fun tag ->
      expect (does_not_fire "SCRIPT-001" "$x_{ab}$") (tag ^ ": braced"));
  run "SCRIPT-001 clean: _a (single char)" (fun tag ->
      expect (does_not_fire "SCRIPT-001" "$x_a$") (tag ^ ": single char"));

  (* ══════════════════════════════════════════════════════════════════════
     SCRIPT-002: Superscript dash typed as unicode hyphen
     ══════════════════════════════════════════════════════════════════════ *)
  run "SCRIPT-002 fires on ^U+2011" (fun tag ->
      expect
        (fires "SCRIPT-002" "$x^\xe2\x80\x91$")
        (tag ^ ": non-breaking hyphen"));
  run "SCRIPT-002 fires on ^U+2010" (fun tag ->
      expect (fires "SCRIPT-002" "$x^\xe2\x80\x90$") (tag ^ ": hyphen U+2010"));
  run "SCRIPT-002 clean: ^{-}" (fun tag ->
      expect (does_not_fire "SCRIPT-002" "$x^{-}$") (tag ^ ": ascii dash"));
  run "SCRIPT-002 clean: no superscript" (fun tag ->
      expect (does_not_fire "SCRIPT-002" "$x + y$") (tag ^ ": no sup"));

  (* ══════════════════════════════════════════════════════════════════════
     SCRIPT-003: Comma-separated superscripts lack braces
     ══════════════════════════════════════════════════════════════════════ *)
  run "SCRIPT-003 fires on ^a,b" (fun tag ->
      expect (fires "SCRIPT-003" "$x^a,b$") (tag ^ ": ^a,b"));
  run "SCRIPT-003 fires on ^a,b,c" (fun tag ->
      expect (fires "SCRIPT-003" "$x^a,b,c$") (tag ^ ": ^a,b,c"));
  run "SCRIPT-003 clean: ^{a,b}" (fun tag ->
      expect (does_not_fire "SCRIPT-003" "$x^{a,b}$") (tag ^ ": braced"));
  run "SCRIPT-003 clean: ^a (no comma)" (fun tag ->
      expect (does_not_fire "SCRIPT-003" "$x^a$") (tag ^ ": no comma"));

  (* ══════════════════════════════════════════════════════════════════════
     SCRIPT-004: Subscript after prime notation mis-ordered
     ══════════════════════════════════════════════════════════════════════ *)
  run "SCRIPT-004 fires on f'_i" (fun tag ->
      expect (fires "SCRIPT-004" "$f'_i$") (tag ^ ": f'_i"));
  run "SCRIPT-004 fires on f''_j" (fun tag ->
      expect (fires "SCRIPT-004" "$f''_j$") (tag ^ ": f''_j"));
  run "SCRIPT-004 clean: f_i'" (fun tag ->
      expect (does_not_fire "SCRIPT-004" "$f_i'$") (tag ^ ": correct order"));
  run "SCRIPT-004 clean: no prime" (fun tag ->
      expect (does_not_fire "SCRIPT-004" "$f_i$") (tag ^ ": no prime"));

  (* ══════════════════════════════════════════════════════════════════════
     SCRIPT-005: Superscript uses letter l instead of \ell
     ══════════════════════════════════════════════════════════════════════ *)
  run "SCRIPT-005 fires on ^l" (fun tag ->
      expect (fires "SCRIPT-005" "$x^l$") (tag ^ ": ^l"));
  run "SCRIPT-005 fires on ^{l}" (fun tag ->
      expect (fires "SCRIPT-005" "$x^{l}$") (tag ^ ": ^{l}"));
  run "SCRIPT-005 clean: ^{\\ell}" (fun tag ->
      expect (does_not_fire "SCRIPT-005" "$x^{\\ell}$") (tag ^ ": \\ell"));
  run "SCRIPT-005 clean: ^{log}" (fun tag ->
      expect (does_not_fire "SCRIPT-005" "$x^{log}$") (tag ^ ": log not l"));

  (* ══════════════════════════════════════════════════════════════════════
     SCRIPT-006: Degree symbol typed ° (U+00B0) in math
     ══════════════════════════════════════════════════════════════════════ *)
  run "SCRIPT-006 fires on degree sign in math" (fun tag ->
      expect (fires "SCRIPT-006" "$90\xc2\xb0$") (tag ^ ": degree U+00B0"));
  run "SCRIPT-006 count=2" (fun tag ->
      expect
        (fires_with_count "SCRIPT-006" "$90\xc2\xb0 + 45\xc2\xb0$" 2)
        (tag ^ ": count=2"));
  run "SCRIPT-006 clean: ^{\\circ}" (fun tag ->
      expect
        (does_not_fire "SCRIPT-006" "$90^{\\circ}$")
        (tag ^ ": circ notation"));
  run "SCRIPT-006 clean: no degree" (fun tag ->
      expect (does_not_fire "SCRIPT-006" "$x + y$") (tag ^ ": no degree"));

  (* ══════════════════════════════════════════════════════════════════════
     SCRIPT-007: Subscript text not wrapped in \text{}
     ══════════════════════════════════════════════════════════════════════ *)
  run "SCRIPT-007 fires on _{total}" (fun tag ->
      expect (fires "SCRIPT-007" "$x_{total}$") (tag ^ ": _{total}"));
  run "SCRIPT-007 fires on _{eff}" (fun tag ->
      expect (fires "SCRIPT-007" "$T_{eff}$") (tag ^ ": _{eff}"));
  run "SCRIPT-007 clean: _{\\text{total}}" (fun tag ->
      expect
        (does_not_fire "SCRIPT-007" "$x_{\\text{total}}$")
        (tag ^ ": \\text{} wrapped"));
  run "SCRIPT-007 clean: _{min}" (fun tag ->
      expect (does_not_fire "SCRIPT-007" "$x_{min}$") (tag ^ ": known operator"));
  run "SCRIPT-007 clean: _{ab} (2 chars)" (fun tag ->
      (* 2-char subscripts are handled by SCRIPT-020 *)
      expect
        (does_not_fire "SCRIPT-007" "$x_{ab}$")
        (tag ^ ": 2 chars — no 3+ match"));

  (* ══════════════════════════════════════════════════════════════════════
     SCRIPT-008: Chemical formula lacks \mathrm{} in subscript
     ══════════════════════════════════════════════════════════════════════ *)
  run "SCRIPT-008 fires on H_2" (fun tag ->
      expect (fires "SCRIPT-008" "$H_2O$") (tag ^ ": H_2"));
  run "SCRIPT-008 fires on Na_2" (fun tag ->
      expect (fires "SCRIPT-008" "$Na_2SO_4$") (tag ^ ": Na_2"));
  run "SCRIPT-008 clean: \\ce{H_2O}" (fun tag ->
      expect (does_not_fire "SCRIPT-008" "$\\ce{H_2O}$") (tag ^ ": inside \\ce"));
  run "SCRIPT-008 clean: \\mathrm{H}_2" (fun tag ->
      expect
        (does_not_fire "SCRIPT-008" "$\\mathrm{H}_2$")
        (tag ^ ": mathrm wrapped"));

  (* ══════════════════════════════════════════════════════════════════════
     SCRIPT-009: Isotope superscript mass number missing
     ══════════════════════════════════════════════════════════════════════ *)
  run "SCRIPT-009 fires on ^{}_{Z}" (fun tag ->
      expect (fires "SCRIPT-009" "$^{}_{92}U$") (tag ^ ": empty mass"));
  run "SCRIPT-009 fires on ^{ }_{Z}" (fun tag ->
      expect (fires "SCRIPT-009" "$^{ }_{6}C$") (tag ^ ": space mass"));
  run "SCRIPT-009 clean: ^{14}_{6}C" (fun tag ->
      expect
        (does_not_fire "SCRIPT-009" "$^{14}_{6}C$")
        (tag ^ ": has mass number"));
  run "SCRIPT-009 clean: no isotope" (fun tag ->
      expect (does_not_fire "SCRIPT-009" "$x + y$") (tag ^ ": no isotope"));

  (* ══════════════════════════════════════════════════════════════════════
     SCRIPT-010: \limits on inline operator
     ══════════════════════════════════════════════════════════════════════ *)
  run "SCRIPT-010 fires on \\limits in $...$" (fun tag ->
      expect
        (fires "SCRIPT-010" "$\\sum\\limits_{i=0}^n$")
        (tag ^ ": limits in inline"));
  run "SCRIPT-010 clean: \\limits in display math" (fun tag ->
      expect
        (does_not_fire "SCRIPT-010" "\\[\\sum\\limits_{i=0}^n\\]")
        (tag ^ ": limits in display ok"));
  run "SCRIPT-010 clean: no limits" (fun tag ->
      expect (does_not_fire "SCRIPT-010" "$\\sum_{i=0}^n$") (tag ^ ": no limits"));

  (* ══════════════════════════════════════════════════════════════════════
     SCRIPT-011: Nested superscript three levels deep
     ══════════════════════════════════════════════════════════════════════ *)
  run "SCRIPT-011 fires on x^{a^{b^{c}}}" (fun tag ->
      expect (fires "SCRIPT-011" "$x^{a^{b^{c}}}$") (tag ^ ": 3 levels"));
  run "SCRIPT-011 clean: x^{a^{b}}" (fun tag ->
      expect (does_not_fire "SCRIPT-011" "$x^{a^{b}}$") (tag ^ ": 2 levels ok"));
  run "SCRIPT-011 clean: no nesting" (fun tag ->
      expect (does_not_fire "SCRIPT-011" "$x^a$") (tag ^ ": single level"));

  (* ══════════════════════════════════════════════════════════════════════
     SCRIPT-012: Prime notation f'''' (> 3) — prefer ^{(n)}
     ══════════════════════════════════════════════════════════════════════ *)
  run "SCRIPT-012 fires on 4 primes" (fun tag ->
      expect (fires "SCRIPT-012" "$f''''$") (tag ^ ": 4 primes"));
  run "SCRIPT-012 fires on 5 primes" (fun tag ->
      expect (fires "SCRIPT-012" "$f'''''$") (tag ^ ": 5 primes"));
  run "SCRIPT-012 clean: 3 primes" (fun tag ->
      expect (does_not_fire "SCRIPT-012" "$f'''$") (tag ^ ": 3 primes ok"));
  run "SCRIPT-012 clean: 1 prime" (fun tag ->
      expect (does_not_fire "SCRIPT-012" "$f'$") (tag ^ ": single prime"));

  (* ══════════════════════════════════════════════════════════════════════
     SCRIPT-013: Plus/minus typed in subscript
     ══════════════════════════════════════════════════════════════════════ *)
  run "SCRIPT-013 fires on _{+}" (fun tag ->
      expect (fires "SCRIPT-013" "$x_{+}$") (tag ^ ": _{+}"));
  run "SCRIPT-013 fires on _{-}" (fun tag ->
      expect (fires "SCRIPT-013" "$x_{-}$") (tag ^ ": _{-}"));
  run "SCRIPT-013 clean: _{\\pm}" (fun tag ->
      expect (does_not_fire "SCRIPT-013" "$x_{\\pm}$") (tag ^ ": \\pm ok"));
  run "SCRIPT-013 clean: no subscript" (fun tag ->
      expect (does_not_fire "SCRIPT-013" "$x + y$") (tag ^ ": no sub"));

  (* ══════════════════════════════════════════════════════════════════════
     SCRIPT-014: Logarithm base subscript italic
     ══════════════════════════════════════════════════════════════════════ *)
  run "SCRIPT-014 fires on \\log_x" (fun tag ->
      expect (fires "SCRIPT-014" "$\\log_x y$") (tag ^ ": \\log_x"));
  run "SCRIPT-014 fires on \\log_a" (fun tag ->
      expect (fires "SCRIPT-014" "$\\log_a b$") (tag ^ ": \\log_a"));
  run "SCRIPT-014 clean: \\log_{10}" (fun tag ->
      expect
        (does_not_fire "SCRIPT-014" "$\\log_{10} x$")
        (tag ^ ": braced base"));
  run "SCRIPT-014 clean: no log" (fun tag ->
      expect (does_not_fire "SCRIPT-014" "$x + y$") (tag ^ ": no log"));

  (* ══════════════════════════════════════════════════════════════════════
     SCRIPT-015: Time derivative dot in sub/superscript
     ══════════════════════════════════════════════════════════════════════ *)
  run "SCRIPT-015 fires on _{\\dot{x}}" (fun tag ->
      expect (fires "SCRIPT-015" "$a_{\\dot{x}}$") (tag ^ ": dot in subscript"));
  run "SCRIPT-015 fires on ^{\\ddot{x}}" (fun tag ->
      expect
        (fires "SCRIPT-015" "$a^{\\ddot{x}}$")
        (tag ^ ": ddot in superscript"));
  run "SCRIPT-015 clean: \\dot{x}" (fun tag ->
      expect
        (does_not_fire "SCRIPT-015" "$\\dot{x}$")
        (tag ^ ": dot at top level ok"));

  (* ══════════════════════════════════════════════════════════════════════
     SCRIPT-016: Prime on Greek letter typed '' not ^\prime
     ══════════════════════════════════════════════════════════════════════ *)
  run "SCRIPT-016 fires on \\alpha''" (fun tag ->
      expect (fires "SCRIPT-016" "$\\alpha''$") (tag ^ ": alpha double prime"));
  run "SCRIPT-016 fires on \\beta''" (fun tag ->
      expect (fires "SCRIPT-016" "$\\beta''$") (tag ^ ": beta double prime"));
  run "SCRIPT-016 clean: \\alpha^{\\prime\\prime}" (fun tag ->
      expect
        (does_not_fire "SCRIPT-016" "$\\alpha^{\\prime\\prime}$")
        (tag ^ ": proper notation"));
  run "SCRIPT-016 clean: \\alpha'" (fun tag ->
      (* Single prime is ok — rule looks for '' *)
      expect
        (does_not_fire "SCRIPT-016" "$\\alpha'$")
        (tag ^ ": single prime ok"));

  (* ══════════════════════════════════════════════════════════════════════
     SCRIPT-017: Inconsistent order of sub/superscripts
     ══════════════════════════════════════════════════════════════════════ *)
  run "SCRIPT-017 fires on mixed order" (fun tag ->
      expect
        (fires "SCRIPT-017" "$x_a^b + y^c_d$")
        (tag ^ ": mixed _a^b and ^c_d"));
  run "SCRIPT-017 clean: consistent _a^b" (fun tag ->
      expect
        (does_not_fire "SCRIPT-017" "$x_a^b + y_c^d$")
        (tag ^ ": consistent order"));
  run "SCRIPT-017 clean: only superscripts" (fun tag ->
      expect
        (does_not_fire "SCRIPT-017" "$x^a + y^b$")
        (tag ^ ": no sub/sup pairs"));

  (* ══════════════════════════════════════════════════════════════════════
     SCRIPT-018: Degree symbol ^\\circ without braces
     ══════════════════════════════════════════════════════════════════════ *)
  run "SCRIPT-018 fires on ^\\circ" (fun tag ->
      expect (fires "SCRIPT-018" "$90^\\circ$") (tag ^ ": ^\\circ"));
  run "SCRIPT-018 clean: ^{\\circ}" (fun tag ->
      expect (does_not_fire "SCRIPT-018" "$90^{\\circ}$") (tag ^ ": braced ok"));
  run "SCRIPT-018 clean: no circ" (fun tag ->
      expect (does_not_fire "SCRIPT-018" "$90 + 45$") (tag ^ ": no circ"));

  (* ══════════════════════════════════════════════════════════════════════
     SCRIPT-019: Double prime '' instead of ^{\prime\prime}
     ══════════════════════════════════════════════════════════════════════ *)
  run "SCRIPT-019 fires on ''" (fun tag ->
      expect (fires "SCRIPT-019" "$f''$") (tag ^ ": double prime"));
  run "SCRIPT-019 count=2" (fun tag ->
      expect (fires_with_count "SCRIPT-019" "$f'' + g''$" 2) (tag ^ ": count=2"));
  run "SCRIPT-019 clean: ^{\\prime\\prime}" (fun tag ->
      expect
        (does_not_fire "SCRIPT-019" "$f^{\\prime\\prime}$")
        (tag ^ ": proper notation"));
  run "SCRIPT-019 does not fire on '''" (fun tag ->
      (* Triple primes are handled by SCRIPT-012, not this rule *)
      expect
        (does_not_fire "SCRIPT-019" "$f'''$")
        (tag ^ ": triple prime skipped"));

  (* ══════════════════════════════════════════════════════════════════════
     SCRIPT-020: Subscript text italic instead of \mathrm
     ══════════════════════════════════════════════════════════════════════ *)
  run "SCRIPT-020 fires on _{eff}" (fun tag ->
      expect (fires "SCRIPT-020" "$T_{eff}$") (tag ^ ": _{eff}"));
  run "SCRIPT-020 fires on _{eq}" (fun tag ->
      expect (fires "SCRIPT-020" "$V_{eq}$") (tag ^ ": _{eq}"));
  run "SCRIPT-020 clean: _{\\mathrm{eff}}" (fun tag ->
      expect
        (does_not_fire "SCRIPT-020" "$T_{\\mathrm{eff}}$")
        (tag ^ ": mathrm wrapped"));
  run "SCRIPT-020 clean: _{min}" (fun tag ->
      expect
        (does_not_fire "SCRIPT-020" "$x_{min}$")
        (tag ^ ": known operator excluded"));

  (* ══════════════════════════════════════════════════════════════════════
     SCRIPT-021: Sub-sup order not canonical (a_{b}^{c} vs a^{c}_{b})
     ══════════════════════════════════════════════════════════════════════ *)
  run "SCRIPT-021 fires on _a^b" (fun tag ->
      expect (fires "SCRIPT-021" "$x_a^b$") (tag ^ ": _a^b"));
  run "SCRIPT-021 fires on _{x}^{y}" (fun tag ->
      expect (fires "SCRIPT-021" "$x_{a}^{b}$") (tag ^ ": _{a}^{b}"));
  run "SCRIPT-021 clean: ^b_a" (fun tag ->
      expect (does_not_fire "SCRIPT-021" "$x^b_a$") (tag ^ ": canonical order"));
  run "SCRIPT-021 clean: just subscript" (fun tag ->
      expect (does_not_fire "SCRIPT-021" "$x_a$") (tag ^ ": sub only"));

  (* ══════════════════════════════════════════════════════════════════════
     SCRIPT-022: Superscript prime stacked > 3 in braces
     ══════════════════════════════════════════════════════════════════════ *)
  run "SCRIPT-022 fires on ^{''''}" (fun tag ->
      expect (fires "SCRIPT-022" "$f^{''''}$") (tag ^ ": 4 primes braced"));
  run "SCRIPT-022 fires on ^{'''''}" (fun tag ->
      expect (fires "SCRIPT-022" "$f^{'''''}$") (tag ^ ": 5 primes braced"));
  run "SCRIPT-022 clean: ^{'''}" (fun tag ->
      expect (does_not_fire "SCRIPT-022" "$f^{'''}$") (tag ^ ": 3 primes ok"));

  (* ══════════════════════════════════════════════════════════════════════
     Cross-cutting edge cases
     ══════════════════════════════════════════════════════════════════════ *)
  run "empty input: no SCRIPT rules fire" (fun tag ->
      let results = Validators.run_all "" in
      let script_fires =
        List.filter
          (fun (r : Validators.result) ->
            String.length r.id >= 7 && String.sub r.id 0 7 = "SCRIPT-")
          results
      in
      expect (script_fires = []) (tag ^ ": no SCRIPT on empty input"));

  run "clean math: no SCRIPT rules fire" (fun tag ->
      let results = Validators.run_all "$x^{2} + y_{1}$" in
      let script_fires =
        List.filter
          (fun (r : Validators.result) ->
            String.length r.id >= 7 && String.sub r.id 0 7 = "SCRIPT-")
          results
      in
      expect (script_fires = []) (tag ^ ": no SCRIPT on clean math"));

  (* Registration: verify each SCRIPT rule fires on known-bad input *)
  run "registration: SCRIPT-001 registered" (fun tag ->
      expect (fires "SCRIPT-001" "$x_ab$") (tag ^ ": registered"));
  run "registration: SCRIPT-003 registered" (fun tag ->
      expect (fires "SCRIPT-003" "$x^a,b$") (tag ^ ": registered"));
  run "registration: SCRIPT-006 registered" (fun tag ->
      expect (fires "SCRIPT-006" "$90\xc2\xb0$") (tag ^ ": registered"));
  run "registration: SCRIPT-012 registered" (fun tag ->
      expect (fires "SCRIPT-012" "$f''''$") (tag ^ ": registered"));
  run "registration: SCRIPT-022 registered" (fun tag ->
      expect (fires "SCRIPT-022" "$f^{''''}$") (tag ^ ": registered"));

  (* Precondition check *)
  run "precondition: SCRIPT- maps to L1" (fun tag ->
      let layer = Validators.precondition_of_rule_id "SCRIPT-001" in
      expect (layer = L1) (tag ^ ": L1 layer"));

  (* Combined: multiple SCRIPT issues in one document *)
  run "combined: multiple SCRIPT rules fire" (fun tag ->
      let src = "$x_ab + f'''' + 90\xc2\xb0 + \\log_x y + x_{+}$" in
      expect (fires "SCRIPT-001" src) (tag ^ ": SCRIPT-001 fires");
      expect (fires "SCRIPT-012" src) (tag ^ ": SCRIPT-012 fires");
      expect (fires "SCRIPT-006" src) (tag ^ ": SCRIPT-006 fires");
      expect (fires "SCRIPT-014" src) (tag ^ ": SCRIPT-014 fires");
      expect (fires "SCRIPT-013" src) (tag ^ ": SCRIPT-013 fires"));

  (* Summary *)
  Printf.printf "[script] %s %d cases\n"
    (if !fails = 0 then "PASS" else "FAIL")
    !cases;
  if !fails > 0 then (
    Printf.eprintf "[script] %d / %d failures\n" !fails !cases;
    exit 1)
