(** Unit tests for MATH-C Part 3: MATH-072..108 remaining rules. *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[math-c3] FAIL: %s\n%!" msg;
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
      expect (math_c3 = []) (tag ^ ": no fires on empty"));

  if !fails > 0 then (
    Printf.eprintf "[math-c3] %d failure(s)\n%!" !fails;
    exit 1)
  else Printf.printf "[math-c3] PASS %d cases\n%!" !cases
