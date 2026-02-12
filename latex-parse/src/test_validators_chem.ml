(** Unit tests for CHEM validator rules (L1 chemistry notation). CHEM-001
    through CHEM-009. *)

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
     CHEM-001: Missing \ce{} wrapper for chemical formula
     ══════════════════════════════════════════════════════════════════════ *)
  run "CHEM-001 fires on H_2O in math" (fun tag ->
      expect (fires "CHEM-001" "$H_2O$") (tag ^ ": H_2O"));
  run "CHEM-001 fires on CO_2" (fun tag ->
      expect (fires "CHEM-001" "$CO_2$") (tag ^ ": CO_2"));
  run "CHEM-001 fires on Na_2 (multi-digit)" (fun tag ->
      expect (fires "CHEM-001" "$Na_{23}$") (tag ^ ": Na_{23}"));
  run "CHEM-001 clean: inside \\ce{}" (fun tag ->
      expect (does_not_fire "CHEM-001" "$\\ce{H_2O}$") (tag ^ ": in ce"));
  run "CHEM-001 clean: not in math" (fun tag ->
      expect (does_not_fire "CHEM-001" "H_2O is water") (tag ^ ": not in math"));
  run "CHEM-001 clean: no chemistry" (fun tag ->
      expect (does_not_fire "CHEM-001" "$x + y = 0$") (tag ^ ": pure math"));

  (* ══════════════════════════════════════════════════════════════════════
     CHEM-002: Oxidation-state superscript missing braces
     ══════════════════════════════════════════════════════════════════════ *)
  run "CHEM-002 fires on Fe^2+" (fun tag ->
      expect (fires "CHEM-002" "$Fe^2+$") (tag ^ ": Fe^2+"));
  run "CHEM-002 fires on Cu^3+" (fun tag ->
      expect (fires "CHEM-002" "$Cu^3+$") (tag ^ ": Cu^3+"));
  run "CHEM-002 fires on O^2-" (fun tag ->
      expect (fires "CHEM-002" "$O^2-$") (tag ^ ": O^2-"));
  run "CHEM-002 clean: Fe^{2+}" (fun tag ->
      expect (does_not_fire "CHEM-002" "$Fe^{2+}$") (tag ^ ": braced"));
  run "CHEM-002 clean: not in math" (fun tag ->
      expect (does_not_fire "CHEM-002" "Fe^2+ outside math") (tag ^ ": text"));
  run "CHEM-002 fires on Na^1+ (single-letter element)" (fun tag ->
      expect (fires "CHEM-002" "$N^1+$") (tag ^ ": N^1+"));

  (* ══════════════════════════════════════════════════════════════════════
     CHEM-003: Isotope mass number subscripted not superscripted
     ══════════════════════════════════════════════════════════════════════ *)
  run "CHEM-003 fires on _14C" (fun tag ->
      expect (fires "CHEM-003" "$_14C$") (tag ^ ": _14C"));
  run "CHEM-003 fires on _{14}C" (fun tag ->
      expect (fires "CHEM-003" "$_{14}C$") (tag ^ ": _{14}C"));
  run "CHEM-003 fires on _6C" (fun tag ->
      expect (fires "CHEM-003" "$_6C$") (tag ^ ": _6C"));
  run "CHEM-003 clean: ^{14}C" (fun tag ->
      expect (does_not_fire "CHEM-003" "$^{14}C$") (tag ^ ": superscripted"));
  run "CHEM-003 clean: normal subscript" (fun tag ->
      expect (does_not_fire "CHEM-003" "$x_i$") (tag ^ ": variable subscript"));

  (* ══════════════════════════════════════════════════════════════════════
     CHEM-004: Charge written ^- instead of ^{-}
     ══════════════════════════════════════════════════════════════════════ *)
  run "CHEM-004 fires on Cl^-x" (fun tag ->
      expect (fires "CHEM-004" "$Cl^-x$") (tag ^ ": Cl^-x"));
  run "CHEM-004 fires on Na^+O" (fun tag ->
      expect (fires "CHEM-004" "$Na^+O$") (tag ^ ": Na^+O"));
  run "CHEM-004 clean: Cl^{-}" (fun tag ->
      expect (does_not_fire "CHEM-004" "$Cl^{-}$") (tag ^ ": braced"));
  run "CHEM-004 clean: Na^{+}" (fun tag ->
      expect (does_not_fire "CHEM-004" "$Na^{+}$") (tag ^ ": braced +"));
  run "CHEM-004 clean: not in math" (fun tag ->
      expect (does_not_fire "CHEM-004" "Cl^-x outside") (tag ^ ": text"));

  (* ══════════════════════════════════════════════════════════════════════
     CHEM-005: Chemical arrow typed '->' not \rightarrow
     ══════════════════════════════════════════════════════════════════════ *)
  run "CHEM-005 fires on -> in math" (fun tag ->
      expect (fires "CHEM-005" "$A -> B$") (tag ^ ": bare ->"));
  run "CHEM-005 fires count=2" (fun tag ->
      expect (fires_with_count "CHEM-005" "$A -> B -> C$" 2) (tag ^ ": count=2"));
  run "CHEM-005 clean: \\rightarrow" (fun tag ->
      expect
        (does_not_fire "CHEM-005" "$A \\rightarrow B$")
        (tag ^ ": rightarrow"));
  run "CHEM-005 clean: \\longrightarrow" (fun tag ->
      expect
        (does_not_fire "CHEM-005" "$A \\longrightarrow B$")
        (tag ^ ": longrightarrow"));
  run "CHEM-005 clean: not in math" (fun tag ->
      expect (does_not_fire "CHEM-005" "A -> B outside math") (tag ^ ": text"));

  (* ══════════════════════════════════════════════════════════════════════
     CHEM-006: Stoichiometry coefficient inside \ce missing
     ══════════════════════════════════════════════════════════════════════ *)
  run "CHEM-006 fires on \\ce{H2 + O2}" (fun tag ->
      expect (fires "CHEM-006" "\\ce{H2 + O2}") (tag ^ ": missing coefficients"));
  run "CHEM-006 fires on \\ce{Na + Cl2}" (fun tag ->
      expect
        (fires "CHEM-006" "\\ce{Na + Cl2}")
        (tag ^ ": Na and Cl2 lack coefficients"));
  run "CHEM-006 clean: \\ce{2H2 + O2}" (fun tag ->
      expect
        (does_not_fire "CHEM-006" "\\ce{2H2 + 1O2}")
        (tag ^ ": has coefficients"));
  run "CHEM-006 clean: \\ce{H2O} (no reaction)" (fun tag ->
      expect (does_not_fire "CHEM-006" "\\ce{H2O}") (tag ^ ": no + sign"));
  run "CHEM-006 clean: no \\ce at all" (fun tag ->
      expect (does_not_fire "CHEM-006" "$H_2O$") (tag ^ ": no ce"));
  run "CHEM-006 in math context" (fun tag ->
      expect
        (does_not_fire "CHEM-006" "$\\ce{H2O}$")
        (tag ^ ": ce in math, no reaction"));

  (* ══════════════════════════════════════════════════════════════════════
     CHEM-007: Reaction conditions not in \text above arrow
     ══════════════════════════════════════════════════════════════════════ *)
  run "CHEM-007 fires on ->[heat]" (fun tag ->
      expect (fires "CHEM-007" "$A ->[heat] B$") (tag ^ ": ->[heat]"));
  run "CHEM-007 fires on ->[cat]" (fun tag ->
      expect (fires "CHEM-007" "$X ->[cat] Y$") (tag ^ ": ->[cat]"));
  run "CHEM-007 clean: ->[\\text{heat}]" (fun tag ->
      expect
        (does_not_fire "CHEM-007" "$A ->[\\text{heat}] B$")
        (tag ^ ": text wrapped"));
  run "CHEM-007 clean: no arrow conditions" (fun tag ->
      expect (does_not_fire "CHEM-007" "$A -> B$") (tag ^ ": no brackets"));
  run "CHEM-007 clean: empty brackets" (fun tag ->
      expect (does_not_fire "CHEM-007" "$A ->[] B$") (tag ^ ": empty brackets"));

  (* ══════════════════════════════════════════════════════════════════════
     CHEM-008: State symbols (aq)/(s)/(l)/(g) not wrapped in \text
     ══════════════════════════════════════════════════════════════════════ *)
  run "CHEM-008 fires on bare (aq)" (fun tag ->
      expect (fires "CHEM-008" "$NaCl(aq)$") (tag ^ ": bare (aq)"));
  run "CHEM-008 fires on bare (s)" (fun tag ->
      expect (fires "CHEM-008" "$NaCl(s)$") (tag ^ ": bare (s)"));
  run "CHEM-008 fires on bare (l)" (fun tag ->
      expect (fires "CHEM-008" "$H_2O(l)$") (tag ^ ": bare (l)"));
  run "CHEM-008 fires on bare (g)" (fun tag ->
      expect (fires "CHEM-008" "$CO_2(g)$") (tag ^ ": bare (g)"));
  run "CHEM-008 clean: \\text{(aq)}" (fun tag ->
      expect
        (does_not_fire "CHEM-008" "$NaCl\\text{(aq)}$")
        (tag ^ ": text wrapped"));
  run "CHEM-008 clean: no state symbols" (fun tag ->
      expect (does_not_fire "CHEM-008" "$x + y$") (tag ^ ": no states"));
  run "CHEM-008 clean: not in math" (fun tag ->
      expect
        (does_not_fire "CHEM-008" "NaCl(aq) is dissolved in water")
        (tag ^ ": text mode"));

  (* ══════════════════════════════════════════════════════════════════════
     CHEM-009: Equilibrium arrow typed as <> or <->
     ══════════════════════════════════════════════════════════════════════ *)
  run "CHEM-009 fires on <->" (fun tag ->
      expect (fires "CHEM-009" "$A <-> B$") (tag ^ ": <->"));
  run "CHEM-009 fires on <=>" (fun tag ->
      expect (fires "CHEM-009" "$A <=> B$") (tag ^ ": <=>"));
  run "CHEM-009 fires count=2" (fun tag ->
      expect
        (fires_with_count "CHEM-009" "$A <-> B <=> C$" 2)
        (tag ^ ": count=2"));
  run "CHEM-009 clean: \\rightleftharpoons" (fun tag ->
      expect
        (does_not_fire "CHEM-009" "$A \\rightleftharpoons B$")
        (tag ^ ": proper symbol"));
  run "CHEM-009 clean: not in math" (fun tag ->
      expect (does_not_fire "CHEM-009" "A <-> B outside") (tag ^ ": text"));

  (* ══════════════════════════════════════════════════════════════════════
     Cross-cutting edge cases
     ══════════════════════════════════════════════════════════════════════ *)
  run "empty input: no CHEM rules fire" (fun tag ->
      let results = Validators.run_all "" in
      let chem_fires =
        List.filter
          (fun (r : Validators.result) ->
            String.length r.id >= 5 && String.sub r.id 0 5 = "CHEM-")
          results
      in
      expect (chem_fires = []) (tag ^ ": no CHEM on empty"));

  run "clean math: no CHEM rules fire" (fun tag ->
      let results = Validators.run_all "$x^{2} + y_{1} = 0$" in
      let chem_fires =
        List.filter
          (fun (r : Validators.result) ->
            String.length r.id >= 5 && String.sub r.id 0 5 = "CHEM-")
          results
      in
      expect (chem_fires = []) (tag ^ ": no CHEM on clean math"));

  (* Registration: verify each CHEM rule fires on known-bad input *)
  run "registration: CHEM-001" (fun tag ->
      expect (fires "CHEM-001" "$H_2O$") (tag ^ ": registered"));
  run "registration: CHEM-002" (fun tag ->
      expect (fires "CHEM-002" "$Fe^2+$") (tag ^ ": registered"));
  run "registration: CHEM-003" (fun tag ->
      expect (fires "CHEM-003" "$_{14}C$") (tag ^ ": registered"));
  run "registration: CHEM-004" (fun tag ->
      expect (fires "CHEM-004" "$Cl^-x$") (tag ^ ": registered"));
  run "registration: CHEM-005" (fun tag ->
      expect (fires "CHEM-005" "$A -> B$") (tag ^ ": registered"));
  run "registration: CHEM-006" (fun tag ->
      expect (fires "CHEM-006" "\\ce{Na + Cl}") (tag ^ ": registered"));
  run "registration: CHEM-007" (fun tag ->
      expect (fires "CHEM-007" "$->[heat]$") (tag ^ ": registered"));
  run "registration: CHEM-008" (fun tag ->
      expect (fires "CHEM-008" "$NaCl(aq)$") (tag ^ ": registered"));
  run "registration: CHEM-009" (fun tag ->
      expect (fires "CHEM-009" "$A <-> B$") (tag ^ ": registered"));

  (* Precondition check *)
  run "precondition: CHEM- maps to L1" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "CHEM-001" = L1)
        (tag ^ ": L1 layer"));

  (* Severity checks *)
  run "severity: CHEM-001 is Warning" (fun tag ->
      let results = Validators.run_all "$H_2O$" in
      match find_result "CHEM-001" results with
      | Some r -> expect (r.severity = Warning) (tag ^ ": Warning")
      | None -> expect false (tag ^ ": should fire"));
  run "severity: CHEM-004 is Info" (fun tag ->
      let results = Validators.run_all "$Cl^-x$" in
      match find_result "CHEM-004" results with
      | Some r -> expect (r.severity = Info) (tag ^ ": Info")
      | None -> expect false (tag ^ ": should fire"));
  run "severity: CHEM-009 is Warning" (fun tag ->
      let results = Validators.run_all "$A <-> B$" in
      match find_result "CHEM-009" results with
      | Some r -> expect (r.severity = Warning) (tag ^ ": Warning")
      | None -> expect false (tag ^ ": should fire"));

  (* Combined multi-rule test *)
  run "combined: chemistry document fires multiple rules" (fun tag ->
      let src = "$Fe^2+ + H_2O -> Fe^{2+}(aq)$" in
      expect (fires "CHEM-002" src) (tag ^ ": CHEM-002 (Fe^2+)");
      expect (fires "CHEM-005" src) (tag ^ ": CHEM-005 (->)");
      expect (fires "CHEM-008" src) (tag ^ ": CHEM-008 ((aq))"));

  (* \ce{} context: rules that operate inside \ce should work *)
  run "CHEM-006 with nested braces in \\ce" (fun tag ->
      expect
        (does_not_fire "CHEM-006" "\\ce{2H2O}")
        (tag ^ ": single compound ok"));

  (* Stress test: repeated calls don't accumulate state *)
  run "stress: 50 repeated calls" (fun tag ->
      let ok = ref true in
      for _ = 1 to 50 do
        let results = Validators.run_all "$Fe^2+$" in
        match find_result "CHEM-002" results with
        | Some r -> if r.count <> 1 then ok := false
        | None -> ok := false
      done;
      expect !ok (tag ^ ": stable across 50 calls"));

  (* Summary *)
  Printf.printf "[chem] %s %d cases\n"
    (if !fails = 0 then "PASS" else "FAIL")
    !cases;
  if !fails > 0 then (
    Printf.eprintf "[chem] %d / %d failures\n" !fails !cases;
    exit 1)
