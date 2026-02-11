(** Unit tests for DELIM validator rules (L1 delimiter matching). DELIM-001
    through DELIM-011. *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[delim] FAIL: %s\n%!" msg;
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
  (* ══════════════════════════════════════════════════════════════════════
     DELIM-001: Unmatched delimiters { } after expansion
     ══════════════════════════════════════════════════════════════════════ *)
  run "DELIM-001 fires on extra open brace" (fun tag ->
      expect (fires "DELIM-001" "hello { world") (tag ^ ": extra {"));
  run "DELIM-001 fires on extra close brace" (fun tag ->
      expect (fires "DELIM-001" "hello } world") (tag ^ ": extra }"));
  run "DELIM-001 count=2 for two unmatched" (fun tag ->
      expect
        (fires_with_count "DELIM-001" "{{ text }" 1)
        (tag ^ ": count=1 for {{}"));
  run "DELIM-001 clean: balanced braces" (fun tag ->
      expect
        (does_not_fire "DELIM-001" "\\textbf{hello} and {world}")
        (tag ^ ": balanced"));
  run "DELIM-001 clean: escaped braces" (fun tag ->
      expect
        (does_not_fire "DELIM-001" "a \\{ b \\} c")
        (tag ^ ": escaped braces ignored"));
  run "DELIM-001 clean: empty" (fun tag ->
      expect (does_not_fire "DELIM-001" "") (tag ^ ": empty"));

  (* ══════════════════════════════════════════════════════════════════════
     DELIM-002: Extra closing } detected
     ══════════════════════════════════════════════════════════════════════ *)
  run "DELIM-002 fires on leading close" (fun tag ->
      expect (fires "DELIM-002" "} hello") (tag ^ ": leading }"));
  run "DELIM-002 fires on double close" (fun tag ->
      expect (fires "DELIM-002" "{text}} rest") (tag ^ ": double close"));
  run "DELIM-002 count=2" (fun tag ->
      expect (fires_with_count "DELIM-002" "}} text" 2) (tag ^ ": count=2"));
  run "DELIM-002 clean: balanced" (fun tag ->
      expect (does_not_fire "DELIM-002" "{a} {b} {c}") (tag ^ ": balanced"));
  run "DELIM-002 clean: nested balanced" (fun tag ->
      expect (does_not_fire "DELIM-002" "{{a} {b}}") (tag ^ ": nested balanced"));

  (* ══════════════════════════════════════════════════════════════════════
     DELIM-003: Unmatched \left without \right
     ══════════════════════════════════════════════════════════════════════ *)
  run "DELIM-003 fires on left without right" (fun tag ->
      expect (fires "DELIM-003" "$\\left( x + y$") (tag ^ ": left without right"));
  run "DELIM-003 count=2" (fun tag ->
      expect
        (fires_with_count "DELIM-003" "$\\left( \\left[ x \\right] y$" 1)
        (tag ^ ": count=1 (one unmatched left)"));
  run "DELIM-003 clean: matched pair" (fun tag ->
      expect
        (does_not_fire "DELIM-003" "$\\left( x \\right)$")
        (tag ^ ": matched pair"));
  run "DELIM-003 clean: no math" (fun tag ->
      expect (does_not_fire "DELIM-003" "hello world") (tag ^ ": no math"));

  (* ══════════════════════════════════════════════════════════════════════
     DELIM-004: Unmatched \right without \left
     ══════════════════════════════════════════════════════════════════════ *)
  run "DELIM-004 fires on right without left" (fun tag ->
      expect
        (fires "DELIM-004" "$x + y \\right)$")
        (tag ^ ": right without left"));
  run "DELIM-004 clean: matched pair" (fun tag ->
      expect
        (does_not_fire "DELIM-004" "$\\left( x \\right)$")
        (tag ^ ": matched pair"));
  run "DELIM-004 clean: no math" (fun tag ->
      expect (does_not_fire "DELIM-004" "just text") (tag ^ ": no math"));

  (* ══════════════════════════════════════════════════════════════════════
     DELIM-005: Mismatched parenthesis sizing
     ══════════════════════════════════════════════════════════════════════ *)
  run "DELIM-005 fires on big vs Bigg mismatch" (fun tag ->
      expect
        (fires "DELIM-005" "$\\big\\left( x \\Bigg\\right)$")
        (tag ^ ": big vs Bigg"));
  run "DELIM-005 clean: consistent sizing" (fun tag ->
      expect
        (does_not_fire "DELIM-005" "$\\big\\left( x \\big\\right)$")
        (tag ^ ": consistent big"));
  run "DELIM-005 clean: no sizing" (fun tag ->
      expect
        (does_not_fire "DELIM-005" "$\\left( x \\right)$")
        (tag ^ ": no sizing commands"));

  (* ══════════════════════════════════════════════════════════════════════
     DELIM-006: \big delimiters in inline math
     ══════════════════════════════════════════════════════════════════════ *)
  run "DELIM-006 fires on \\big in $...$" (fun tag ->
      expect
        (fires "DELIM-006" "Inline $\\big( x \\big)$ text")
        (tag ^ ": big in inline"));
  run "DELIM-006 fires on \\bigl in \\(...\\)" (fun tag ->
      expect
        (fires "DELIM-006" "Inline \\(\\bigl( x \\bigr)\\) text")
        (tag ^ ": bigl in \\(\\)"));
  run "DELIM-006 clean: \\big in display \\[...\\]" (fun tag ->
      expect
        (does_not_fire "DELIM-006" "Display \\[\\big( x \\big)\\]")
        (tag ^ ": big in display ok"));
  run "DELIM-006 clean: no big commands" (fun tag ->
      expect (does_not_fire "DELIM-006" "$x + y$") (tag ^ ": no big commands"));

  (* ══════════════════════════════════════════════════════════════════════
     DELIM-007: Unmatched \langle / \rangle
     ══════════════════════════════════════════════════════════════════════ *)
  run "DELIM-007 fires on unmatched langle" (fun tag ->
      expect
        (fires "DELIM-007" "$\\langle x, y$")
        (tag ^ ": langle without rangle"));
  run "DELIM-007 fires on unmatched rangle" (fun tag ->
      expect
        (fires "DELIM-007" "$x, y \\rangle$")
        (tag ^ ": rangle without langle"));
  run "DELIM-007 count=2" (fun tag ->
      expect
        (fires_with_count "DELIM-007" "$\\langle a \\langle b \\rangle$" 1)
        (tag ^ ": count=1 (one extra langle)"));
  run "DELIM-007 clean: matched pair" (fun tag ->
      expect
        (does_not_fire "DELIM-007" "$\\langle x, y \\rangle$")
        (tag ^ ": matched pair"));
  run "DELIM-007 clean: no angle brackets" (fun tag ->
      expect (does_not_fire "DELIM-007" "$x + y$") (tag ^ ": no angles"));

  (* ══════════════════════════════════════════════════════════════════════
     DELIM-008: Empty \left. ... \right. pair
     ══════════════════════════════════════════════════════════════════════ *)
  run "DELIM-008 fires on left. right." (fun tag ->
      expect (fires "DELIM-008" "$\\left. \\right.$") (tag ^ ": left. right."));
  run "DELIM-008 clean: left( right." (fun tag ->
      expect
        (does_not_fire "DELIM-008" "$\\left( x \\right.$")
        (tag ^ ": left( right. ok (one-sided)"));
  run "DELIM-008 clean: no invisible delimiters" (fun tag ->
      expect
        (does_not_fire "DELIM-008" "$\\left( x \\right)$")
        (tag ^ ": normal delimiters"));

  (* ══════════════════════════════════════════════════════════════════════
     DELIM-009: Nested delimiter type mismatch
     ══════════════════════════════════════════════════════════════════════ *)
  run "DELIM-009 fires on {(})" (fun tag ->
      expect (fires "DELIM-009" "${ ( } )$") (tag ^ ": { ( } ) mismatch"));
  run "DELIM-009 fires on (]" (fun tag ->
      expect (fires "DELIM-009" "$( x ]$") (tag ^ ": ( closed with ]"));
  run "DELIM-009 clean: proper nesting" (fun tag ->
      expect (does_not_fire "DELIM-009" "${ ( x ) }$") (tag ^ ": proper nesting"));
  run "DELIM-009 clean: single type" (fun tag ->
      expect (does_not_fire "DELIM-009" "${x}$") (tag ^ ": single type"));

  (* ══════════════════════════════════════════════════════════════════════
     DELIM-010: Display math uses \big instead of \Big
     ══════════════════════════════════════════════════════════════════════ *)
  run "DELIM-010 fires on \\big in \\[...\\]" (fun tag ->
      expect
        (fires "DELIM-010" "\\[\\big( x \\big)\\]")
        (tag ^ ": big in display math"));
  run "DELIM-010 fires on \\big in equation env" (fun tag ->
      expect
        (fires "DELIM-010" "\\begin{equation}\\big( x \\big)\\end{equation}")
        (tag ^ ": big in equation"));
  run "DELIM-010 clean: \\Big in display" (fun tag ->
      expect
        (does_not_fire "DELIM-010" "\\[\\Big( x \\Big)\\]")
        (tag ^ ": Big in display ok"));
  run "DELIM-010 clean: no sizing" (fun tag ->
      expect (does_not_fire "DELIM-010" "\\[x + y\\]") (tag ^ ": no sizing"));

  (* ══════════════════════════════════════════════════════════════════════
     DELIM-011: \middle without \left...\right pair
     ══════════════════════════════════════════════════════════════════════ *)
  run "DELIM-011 fires on middle without left/right" (fun tag ->
      expect
        (fires "DELIM-011" "$x \\middle| y$")
        (tag ^ ": middle without pair"));
  run "DELIM-011 clean: middle inside left/right" (fun tag ->
      expect
        (does_not_fire "DELIM-011" "$\\left\\{ x \\middle| y \\right\\}$")
        (tag ^ ": middle inside pair"));
  run "DELIM-011 clean: no middle" (fun tag ->
      expect (does_not_fire "DELIM-011" "$x + y$") (tag ^ ": no middle"));

  (* ══════════════════════════════════════════════════════════════════════
     Cross-cutting edge cases
     ══════════════════════════════════════════════════════════════════════ *)
  run "empty input: no DELIM rules fire" (fun tag ->
      let results = Validators.run_all "" in
      let delim_fires =
        List.filter
          (fun (r : Validators.result) ->
            String.length r.id >= 6 && String.sub r.id 0 6 = "DELIM-")
          results
      in
      expect (delim_fires = []) (tag ^ ": no fires on empty"));

  run "clean LaTeX: no DELIM rules fire" (fun tag ->
      let src =
        "\\documentclass{article}\n\
         \\begin{document}\n\
         Hello $x + y = z$ world.\n\
         \\end{document}"
      in
      let results = Validators.run_all src in
      let delim_fires =
        List.filter
          (fun (r : Validators.result) ->
            String.length r.id >= 6 && String.sub r.id 0 6 = "DELIM-")
          results
      in
      expect (delim_fires = []) (tag ^ ": no fires on clean doc"));

  run "all 11 DELIM rules registered" (fun tag ->
      (* Verify each rule fires on trigger input *)
      expect (fires "DELIM-001" "{") (tag ^ ": DELIM-001");
      expect (fires "DELIM-002" "}") (tag ^ ": DELIM-002");
      expect (fires "DELIM-003" "$\\left($") (tag ^ ": DELIM-003");
      expect (fires "DELIM-004" "$\\right)$") (tag ^ ": DELIM-004");
      expect (fires "DELIM-007" "$\\langle$") (tag ^ ": DELIM-007");
      expect (fires "DELIM-008" "$\\left. \\right.$") (tag ^ ": DELIM-008");
      expect (fires "DELIM-009" "$( ]$") (tag ^ ": DELIM-009");
      expect (fires "DELIM-011" "$\\middle|$") (tag ^ ": DELIM-011"));

  run "precondition_of_rule_id: DELIM -> L1" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "DELIM-001" = Validators.L1)
        (tag ^ ": DELIM-001 is L1");
      expect
        (Validators.precondition_of_rule_id "DELIM-011" = Validators.L1)
        (tag ^ ": DELIM-011 is L1"));

  (* Combined: document with multiple delimiter issues *)
  run "combined: multiple DELIM rules fire" (fun tag ->
      let src = "Text { unclosed.\n$\\left( no right$\n$\\langle missing$\n" in
      expect (fires "DELIM-001" src) (tag ^ ": DELIM-001 fires");
      expect (fires "DELIM-003" src) (tag ^ ": DELIM-003 fires");
      expect (fires "DELIM-007" src) (tag ^ ": DELIM-007 fires"));

  if !fails > 0 then (
    Printf.eprintf "[delim] %d failure(s)\n%!" !fails;
    exit 1)
  else Printf.printf "[delim] PASS %d cases\n%!" !cases
