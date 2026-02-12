(** Unit tests for L1 MATH Batch B validator rules. MATH-030 through MATH-053
    (excluding MATH-032 which is L2_Ast). *)

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
              try int_of_string (String.sub id 5 (n - 5)) with _ -> 0
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
              try int_of_string (String.sub id 5 (n - 5)) with _ -> 0
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
              try int_of_string (String.sub id 5 (n - 5)) with _ -> 0
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
        (tag ^ ": escaped $ ignored"));

  (* Summary *)
  Printf.printf "[math-l1b] %s %d cases\n"
    (if !fails = 0 then "PASS" else "FAIL")
    !cases;
  if !fails > 0 then (
    Printf.eprintf "[math-l1b] %d / %d failures\n" !fails !cases;
    exit 1)
