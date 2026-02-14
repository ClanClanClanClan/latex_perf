(** Tests for MATH-025, MATH-028, MATH-029 gap-fill rules. *)

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[math-gap] FAIL: %s\n%!" msg;
    incr fails)

let run msg f =
  incr cases;
  f msg

let find_result id results =
  List.find_opt
    (fun (r : Latex_parse_lib.Validators.result) -> r.id = id)
    results

let fires tag id input =
  run (tag ^ " fires") (fun t ->
      let results = Latex_parse_lib.Validators.run_all input in
      expect (find_result id results <> None) (t ^ ": " ^ id ^ " should fire"))

let does_not_fire tag id input =
  run (tag ^ " clean") (fun t ->
      let results = Latex_parse_lib.Validators.run_all input in
      expect (find_result id results = None) (t ^ ": " ^ id ^ " should not fire"))

let fires_with_count tag id input expected_count =
  run (tag ^ " count") (fun t ->
      let results = Latex_parse_lib.Validators.run_all input in
      match find_result id results with
      | Some r ->
          expect (r.count = expected_count)
            (t
            ^ ": "
            ^ id
            ^ " count="
            ^ string_of_int r.count
            ^ " expected="
            ^ string_of_int expected_count)
      | None -> expect false (t ^ ": " ^ id ^ " did not fire"))

let () =
  (* ════════════════════════════════════════════════════════════════════
     MATH-025: align with single column → suggest equation
     ════════════════════════════════════════════════════════════════════ *)
  fires "MATH-025 align no ampersand" "MATH-025"
    "\\begin{align}\nx = 1\n\\end{align}";
  fires "MATH-025 align* no ampersand" "MATH-025"
    "\\begin{align*}\ny = 2\n\\end{align*}";
  does_not_fire "MATH-025 align with ampersand" "MATH-025"
    "\\begin{align}\nx &= 1 \\\\\ny &= 2\n\\end{align}";
  does_not_fire "MATH-025 align* with ampersand" "MATH-025"
    "\\begin{align*}\na &= b \\\\\nc &= d\n\\end{align*}";
  fires_with_count "MATH-025 two single-column aligns" "MATH-025"
    "\\begin{align}\nx = 1\n\\end{align}\n\\begin{align}\ny = 2\n\\end{align}" 2;
  does_not_fire "MATH-025 no align env" "MATH-025" "Just some text $x = 1$";
  does_not_fire "MATH-025 equation env" "MATH-025"
    "\\begin{equation}\nx = 1\n\\end{equation}";
  fires "MATH-025 empty align body" "MATH-025" "\\begin{align}\n\\end{align}";
  run "MATH-025 severity is info" (fun tag ->
      let results =
        Latex_parse_lib.Validators.run_all "\\begin{align}\nx = 1\n\\end{align}"
      in
      match find_result "MATH-025" results with
      | Some r ->
          expect
            (r.severity = Latex_parse_lib.Validators.Info)
            (tag ^ ": severity info")
      | None -> expect false (tag ^ ": did not fire"));
  does_not_fire "MATH-025 empty input" "MATH-025" "";

  (* ════════════════════════════════════════════════════════════════════
     MATH-028: array without column alignment spec
     ════════════════════════════════════════════════════════════════════ *)
  fires "MATH-028 array no spec" "MATH-028"
    "$\\begin{array} 1 \\\\ 2 \\end{array}$";
  fires "MATH-028 array space after" "MATH-028"
    "$\\begin{array} x \\end{array}$";
  does_not_fire "MATH-028 array with {c}" "MATH-028"
    "$\\begin{array}{c} 1 \\\\ 2 \\end{array}$";
  does_not_fire "MATH-028 array with {lcr}" "MATH-028"
    "$\\begin{array}{lcr} a & b & c \\end{array}$";
  does_not_fire "MATH-028 array with {|c|}" "MATH-028"
    "$\\begin{array}{|c|} 1 \\end{array}$";
  fires_with_count "MATH-028 two bare arrays" "MATH-028"
    "$\\begin{array} 1 \\end{array}$ $\\begin{array} 2 \\end{array}$" 2;
  does_not_fire "MATH-028 no array env" "MATH-028" "$x + y$";
  run "MATH-028 severity is info" (fun tag ->
      let results =
        Latex_parse_lib.Validators.run_all "$\\begin{array} x \\end{array}$"
      in
      match find_result "MATH-028" results with
      | Some r ->
          expect
            (r.severity = Latex_parse_lib.Validators.Info)
            (tag ^ ": severity info")
      | None -> expect false (tag ^ ": did not fire"));
  does_not_fire "MATH-028 empty input" "MATH-028" "";

  (* ════════════════════════════════════════════════════════════════════
     MATH-029: eqnarray usage
     ════════════════════════════════════════════════════════════════════ *)
  fires "MATH-029 eqnarray" "MATH-029"
    "\\begin{eqnarray}\nx &=& 1\n\\end{eqnarray}";
  fires "MATH-029 eqnarray*" "MATH-029"
    "\\begin{eqnarray*}\nx &=& 1\n\\end{eqnarray*}";
  does_not_fire "MATH-029 align" "MATH-029"
    "\\begin{align}\nx &= 1\n\\end{align}";
  does_not_fire "MATH-029 align*" "MATH-029"
    "\\begin{align*}\nx &= 1\n\\end{align*}";
  does_not_fire "MATH-029 equation" "MATH-029"
    "\\begin{equation}\nx = 1\n\\end{equation}";
  fires_with_count "MATH-029 two eqnarrays" "MATH-029"
    "\\begin{eqnarray}\n\
     a\n\
     \\end{eqnarray}\n\
     \\begin{eqnarray*}\n\
     b\n\
     \\end{eqnarray*}"
    2;
  does_not_fire "MATH-029 no env" "MATH-029" "Just text $x = 1$";
  run "MATH-029 severity is warning" (fun tag ->
      let results =
        Latex_parse_lib.Validators.run_all
          "\\begin{eqnarray}\nx &=& 1\n\\end{eqnarray}"
      in
      match find_result "MATH-029" results with
      | Some r ->
          expect
            (r.severity = Latex_parse_lib.Validators.Warning)
            (tag ^ ": severity warning")
      | None -> expect false (tag ^ ": did not fire"));
  does_not_fire "MATH-029 empty input" "MATH-029" "";

  (* ════════════════════════════════════════════════════════════════════
     precondition_of_rule_id for L2/L3 future rules
     ════════════════════════════════════════════════════════════════════ *)
  run "MATH-023 maps to L2" (fun tag ->
      expect
        (Latex_parse_lib.Validators.precondition_of_rule_id "MATH-023"
        = Latex_parse_lib.Validators.L2)
        (tag ^ ": MATH-023 = L2"));
  run "MATH-024 maps to L2" (fun tag ->
      expect
        (Latex_parse_lib.Validators.precondition_of_rule_id "MATH-024"
        = Latex_parse_lib.Validators.L2)
        (tag ^ ": MATH-024 = L2"));
  run "MATH-026 maps to L3" (fun tag ->
      expect
        (Latex_parse_lib.Validators.precondition_of_rule_id "MATH-026"
        = Latex_parse_lib.Validators.L3)
        (tag ^ ": MATH-026 = L3"));
  run "MATH-027 maps to L3" (fun tag ->
      expect
        (Latex_parse_lib.Validators.precondition_of_rule_id "MATH-027"
        = Latex_parse_lib.Validators.L3)
        (tag ^ ": MATH-027 = L3"));
  run "MATH-025 maps to L1" (fun tag ->
      expect
        (Latex_parse_lib.Validators.precondition_of_rule_id "MATH-025"
        = Latex_parse_lib.Validators.L1)
        (tag ^ ": MATH-025 = L1"));
  run "MATH-028 maps to L1" (fun tag ->
      expect
        (Latex_parse_lib.Validators.precondition_of_rule_id "MATH-028"
        = Latex_parse_lib.Validators.L1)
        (tag ^ ": MATH-028 = L1"));
  run "MATH-029 maps to L1" (fun tag ->
      expect
        (Latex_parse_lib.Validators.precondition_of_rule_id "MATH-029"
        = Latex_parse_lib.Validators.L1)
        (tag ^ ": MATH-029 = L1"));

  if !fails > 0 then (
    Printf.eprintf "[math-gap] %d failure(s)\n%!" !fails;
    exit 1)
  else Printf.printf "[math-gap] PASS %d cases\n%!" !cases
