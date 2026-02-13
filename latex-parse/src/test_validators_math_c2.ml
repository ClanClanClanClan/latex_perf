(** Unit tests for MATH-C Part 2: MATH-056..098 pattern matcher rules. *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[math-c2] FAIL: %s\n%!" msg;
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
      expect (math_c2 = []) (tag ^ ": no fires on empty"));

  if !fails > 0 then (
    Printf.eprintf "[math-c2] %d failure(s)\n%!" !fails;
    exit 1)
  else Printf.printf "[math-c2] PASS %d cases\n%!" !cases
