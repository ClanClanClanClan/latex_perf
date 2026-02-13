(** Unit tests for MATH-C Part 1: MATH-055..105 simple detector rules. *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[math-c1] FAIL: %s\n%!" msg;
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
      expect (math_c = []) (tag ^ ": no fires on empty"));

  if !fails > 0 then (
    Printf.eprintf "[math-c1] %d failure(s)\n%!" !fails;
    exit 1)
  else Printf.printf "[math-c1] PASS %d cases\n%!" !cases
