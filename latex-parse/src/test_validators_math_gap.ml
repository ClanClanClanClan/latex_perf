(** Tests for MATH-025, MATH-028, MATH-029 gap-fill rules. *)

open Latex_parse_lib
open Test_helpers

let () =
  (* ════════════════════════════════════════════════════════════════════
     MATH-025: align with single column → suggest equation
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-025 align no ampersand" (fun tag ->
      expect (fires "MATH-025" "\\begin{align}\nx = 1\n\\end{align}")
        (tag ^ ": should fire"));
  run "MATH-025 align* no ampersand" (fun tag ->
      expect (fires "MATH-025" "\\begin{align*}\ny = 2\n\\end{align*}")
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
           "\\begin{align}\nx = 1\n\\end{align}\n\\begin{align}\ny = 2\n\\end{align}"
           2)
        (tag ^ ": count 2"));
  run "MATH-025 no align env" (fun tag ->
      expect (does_not_fire "MATH-025" "Just some text $x = 1$")
        (tag ^ ": no align env"));
  run "MATH-025 equation env" (fun tag ->
      expect
        (does_not_fire "MATH-025"
           "\\begin{equation}\nx = 1\n\\end{equation}")
        (tag ^ ": equation env"));
  run "MATH-025 empty align body" (fun tag ->
      expect (fires "MATH-025" "\\begin{align}\n\\end{align}")
        (tag ^ ": should fire"));
  run "MATH-025 severity is info" (fun tag ->
      match find_result "MATH-025" "\\begin{align}\nx = 1\n\\end{align}" with
      | Some r ->
          expect (r.severity = Validators.Info) (tag ^ ": severity info")
      | None -> expect false (tag ^ ": did not fire"));
  run "MATH-025 empty input" (fun tag ->
      expect (does_not_fire "MATH-025" "") (tag ^ ": empty input"));

  (* ════════════════════════════════════════════════════════════════════
     MATH-028: array without column alignment spec
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-028 array no spec" (fun tag ->
      expect (fires "MATH-028" "$\\begin{array} 1 \\\\ 2 \\end{array}$")
        (tag ^ ": should fire"));
  run "MATH-028 array space after" (fun tag ->
      expect (fires "MATH-028" "$\\begin{array} x \\end{array}$")
        (tag ^ ": should fire"));
  run "MATH-028 array with {c}" (fun tag ->
      expect
        (does_not_fire "MATH-028"
           "$\\begin{array}{c} 1 \\\\ 2 \\end{array}$")
        (tag ^ ": has col spec"));
  run "MATH-028 array with {lcr}" (fun tag ->
      expect
        (does_not_fire "MATH-028"
           "$\\begin{array}{lcr} a & b & c \\end{array}$")
        (tag ^ ": has col spec"));
  run "MATH-028 array with {|c|}" (fun tag ->
      expect
        (does_not_fire "MATH-028"
           "$\\begin{array}{|c|} 1 \\end{array}$")
        (tag ^ ": has col spec"));
  run "MATH-028 two bare arrays" (fun tag ->
      expect
        (fires_with_count "MATH-028"
           "$\\begin{array} 1 \\end{array}$ $\\begin{array} 2 \\end{array}$"
           2)
        (tag ^ ": count 2"));
  run "MATH-028 no array env" (fun tag ->
      expect (does_not_fire "MATH-028" "$x + y$") (tag ^ ": no array env"));
  run "MATH-028 severity is info" (fun tag ->
      match find_result "MATH-028" "$\\begin{array} x \\end{array}$" with
      | Some r ->
          expect (r.severity = Validators.Info) (tag ^ ": severity info")
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
        (does_not_fire "MATH-029"
           "\\begin{equation}\nx = 1\n\\end{equation}")
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
      expect (does_not_fire "MATH-029" "Just text $x = 1$")
        (tag ^ ": no eqnarray"));
  run "MATH-029 severity is warning" (fun tag ->
      match
        find_result "MATH-029"
          "\\begin{eqnarray}\nx &=& 1\n\\end{eqnarray}"
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
  run "MATH-026 maps to L3" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "MATH-026" = Validators.L3)
        (tag ^ ": MATH-026 = L3"));
  run "MATH-027 maps to L3" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "MATH-027" = Validators.L3)
        (tag ^ ": MATH-027 = L3"));
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

let () = finalise "math-gap"
