(** Unit tests for L3-* expl3/LaTeX3 validators: L3-001, L3-002, L3-003, L3-004,
    L3-005, L3-006, L3-007, L3-009, L3-011. *)

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
     L3-001: LaTeX3 \tl_new:N in preamble mixed with 2e macros
     ══════════════════════════════════════════════════════════════════════ *)
  run "L3-001 fires: expl3 + 2e in preamble" (fun tag ->
      expect
        (fires "L3-001"
           {|\documentclass{article}
\tl_new:N \l_my_tl
\newcommand{\foo}{bar}
\begin{document}
Hello
\end{document}|})
        (tag ^ ": mixed expl3 and 2e in preamble"));
  run "L3-001 fires: int_new:N + renewcommand" (fun tag ->
      expect
        (fires "L3-001"
           {|\documentclass{article}
\int_new:N \l_count
\renewcommand{\maketitle}{}
\begin{document}\end{document}|})
        (tag ^ ": int_new + renewcommand"));
  run "L3-001 clean: only 2e in preamble" (fun tag ->
      expect
        (does_not_fire "L3-001"
           {|\documentclass{article}
\newcommand{\foo}{bar}
\begin{document}\end{document}|})
        (tag ^ ": only 2e macros"));
  run "L3-001 clean: only expl3 in preamble" (fun tag ->
      expect
        (does_not_fire "L3-001"
           {|\documentclass{article}
\tl_new:N \l_my_tl
\begin{document}\end{document}|})
        (tag ^ ": only expl3"));
  run "L3-001 clean: mixing only in document body" (fun tag ->
      expect
        (does_not_fire "L3-001"
           {|\documentclass{article}
\begin{document}
\tl_new:N \l_my_tl
\newcommand{\foo}{bar}
\end{document}|})
        (tag ^ ": mixing in body not preamble"));

  (* ══════════════════════════════════════════════════════════════════════
     L3-002: Expl3 variable declared after \begin{document}
     ══════════════════════════════════════════════════════════════════════ *)
  run "L3-002 fires: tl_new:N after begin{document}" (fun tag ->
      expect
        (fires "L3-002"
           {|\documentclass{article}
\begin{document}
\tl_new:N \l_my_tl
\end{document}|})
        (tag ^ ": tl_new in body"));
  run "L3-002 fires: int_new:N after begin{document}" (fun tag ->
      expect
        (fires "L3-002"
           {|\documentclass{article}
\begin{document}
\int_new:N \l_cnt
\end{document}|})
        (tag ^ ": int_new in body"));
  run "L3-002 fires: count=2 for two declarations" (fun tag ->
      expect
        (fires_with_count "L3-002"
           {|\documentclass{article}
\begin{document}
\tl_new:N \l_a
\bool_new:N \l_flag
\end{document}|}
           2)
        (tag ^ ": count=2"));
  run "L3-002 clean: declaration in preamble" (fun tag ->
      expect
        (does_not_fire "L3-002"
           {|\documentclass{article}
\tl_new:N \l_my_tl
\begin{document}\end{document}|})
        (tag ^ ": declaration in preamble ok"));
  run "L3-002 clean: no begin{document}" (fun tag ->
      expect
        (does_not_fire "L3-002" {|\tl_new:N \l_my_tl|})
        (tag ^ ": no begin{document}"));

  (* ══════════════════════════════════════════════════════════════════════
     L3-003: Expl3 and etoolbox patch macros combined
     ══════════════════════════════════════════════════════════════════════ *)
  run "L3-003 fires: ExplSyntaxOn + patchcmd" (fun tag ->
      expect
        (fires "L3-003"
           {|\ExplSyntaxOn
\tl_set:Nn \l_foo {bar}
\ExplSyntaxOff
\patchcmd{\maketitle}{}{}{}{}|})
        (tag ^ ": expl3 + etoolbox"));
  run "L3-003 fires: expl3 func + apptocmd" (fun tag ->
      expect
        (fires "L3-003"
           {|\cs_new:Npn \my_func:n #1 {#1}
\apptocmd{\section}{code}{}{}|})
        (tag ^ ": cs_new + apptocmd"));
  run "L3-003 clean: only expl3" (fun tag ->
      expect
        (does_not_fire "L3-003"
           {|\ExplSyntaxOn
\tl_set:Nn \l_foo {bar}
\ExplSyntaxOff|})
        (tag ^ ": only expl3"));
  run "L3-003 clean: only etoolbox" (fun tag ->
      expect
        (does_not_fire "L3-003" {|\patchcmd{\maketitle}{}{}{}{}|})
        (tag ^ ": only etoolbox"));

  (* ══════════════════════════════════════════════════════════════════════
     L3-004: Undocumented \__module_internal:N used
     ══════════════════════════════════════════════════════════════════════ *)
  run "L3-004 fires: __module internal" (fun tag ->
      expect
        (fires "L3-004" {|\__mymodule_internal:N \l_tmp|})
        (tag ^ ": __module internal"));
  run "L3-004 fires: count=2" (fun tag ->
      expect
        (fires_with_count "L3-004" {|\__foo_bar:nn {a}{b}
\__baz_helper:N \l_x|}
           2)
        (tag ^ ": count=2"));
  run "L3-004 clean: public function" (fun tag ->
      expect
        (does_not_fire "L3-004" {|\tl_set:Nn \l_foo {bar}|})
        (tag ^ ": public function ok"));

  (* ══════════════════════════════════════════════════════════════════════
     L3-005: Missing \ExplSyntaxOn guard around expl3 code
     ══════════════════════════════════════════════════════════════════════ *)
  run "L3-005 fires: expl3 without guard" (fun tag ->
      expect
        (fires "L3-005" {|\tl_set:Nn \l_foo {bar}|})
        (tag ^ ": no ExplSyntaxOn"));
  run "L3-005 fires: cs_new without guard" (fun tag ->
      expect
        (fires "L3-005" {|\cs_new:Npn \my_func:n #1 {#1}|})
        (tag ^ ": cs_new without guard"));
  run "L3-005 clean: with ExplSyntaxOn" (fun tag ->
      expect
        (does_not_fire "L3-005"
           {|\ExplSyntaxOn
\tl_set:Nn \l_foo {bar}
\ExplSyntaxOff|})
        (tag ^ ": guarded ok"));
  run "L3-005 clean: no expl3 code" (fun tag ->
      expect
        (does_not_fire "L3-005" {|\newcommand{\foo}{bar}|})
        (tag ^ ": no expl3"));

  (* ══════════════════════════════════════════════════════════════════════
     L3-006: Expl3 variable clobbers package macro name
     ══════════════════════════════════════════════════════════════════════ *)
  run "L3-006 fires: var prefix matches package" (fun tag ->
      expect
        (fires "L3-006" {|\usepackage{amsmath}
\l_amsmath_extra:N \l_x|})
        (tag ^ ": amsmath prefix clash"));
  run "L3-006 fires: count with multiple matches" (fun tag ->
      expect
        (fires_with_count "L3-006"
           {|\usepackage{foo}
\l_foo_var:N \l_a
\g_foo_flag:N \g_b|} 2)
        (tag ^ ": count=2"));
  run "L3-006 clean: different prefix" (fun tag ->
      expect
        (does_not_fire "L3-006" {|\usepackage{amsmath}
\l_mymodule_var:N \l_x|})
        (tag ^ ": no clash"));
  run "L3-006 clean: no packages" (fun tag ->
      expect
        (does_not_fire "L3-006" {|\l_foo_var:N \l_x|})
        (tag ^ ": no packages loaded"));

  (* ══════════════════════════════════════════════════════════════════════
     L3-007: Mix of camelCase and snake_case in expl3 names
     ══════════════════════════════════════════════════════════════════════ *)
  run "L3-007 fires: camelCase in expl3" (fun tag ->
      expect
        (fires "L3-007" {|\ExplSyntaxOn
\myFunc_helper:n {x}
\ExplSyntaxOff|})
        (tag ^ ": camelCase function"));
  run "L3-007 clean: snake_case only" (fun tag ->
      expect
        (does_not_fire "L3-007"
           {|\ExplSyntaxOn
\my_func_helper:n {x}
\ExplSyntaxOff|})
        (tag ^ ": snake_case ok"));
  run "L3-007 clean: no expl3" (fun tag ->
      expect
        (does_not_fire "L3-007" {|\newcommand{\myCommand}{foo}|})
        (tag ^ ": no expl3 context"));

  (* ══════════════════════════════════════════════════════════════════════
     L3-009: LaTeX3 function deprecated _n: variant used
     ══════════════════════════════════════════════════════════════════════ *)
  run "L3-009 fires: tl_to_str:n" (fun tag ->
      expect
        (fires "L3-009" {|\tl_to_str:n {hello}|})
        (tag ^ ": deprecated tl_to_str:n"));
  run "L3-009 fires: int_eval:n" (fun tag ->
      expect
        (fires "L3-009" {|\int_eval:n { 1 + 2 }|})
        (tag ^ ": deprecated int_eval:n"));
  run "L3-009 fires: count=2 for two deprecated" (fun tag ->
      expect
        (fires_with_count "L3-009" {|\tl_to_str:n {a}
\fp_eval:n {3.14}|} 2)
        (tag ^ ": count=2"));
  run "L3-009 clean: non-deprecated functions" (fun tag ->
      expect
        (does_not_fire "L3-009" {|\tl_set:Nn \l_foo {bar}|})
        (tag ^ ": non-deprecated ok"));

  (* ══════════════════════════════════════════════════════════════════════
     L3-011: Engine-branch uses pdfTeX primitive in LuaTeX/XeTeX path
     ══════════════════════════════════════════════════════════════════════ *)
  run "L3-011 fires: ifluatex + pdfoutput" (fun tag ->
      expect
        (fires "L3-011" {|\ifluatex
\pdfoutput=1
\fi|})
        (tag ^ ": pdfTeX prim in LuaTeX branch"));
  run "L3-011 fires: ifXeTeX + pdfliteral" (fun tag ->
      expect
        (fires "L3-011" {|\ifXeTeX
\pdfliteral{q 1 0 0 rg}
\fi|})
        (tag ^ ": pdfliteral in XeTeX branch"));
  run "L3-011 fires: sys_if_engine_luatex:T + pdfcatalog" (fun tag ->
      expect
        (fires "L3-011"
           {|\sys_if_engine_luatex:T { \pdfcatalog{/PageMode /UseOutlines} }|})
        (tag ^ ": expl3 engine check + pdfcatalog"));
  run "L3-011 fires: count=2" (fun tag ->
      expect
        (fires_with_count "L3-011"
           {|\ifluatex
\pdfoutput=1
\pdfminorversion=7
\fi|} 2)
        (tag ^ ": count=2 prims"));
  run "L3-011 clean: no engine branch" (fun tag ->
      expect
        (does_not_fire "L3-011" {|\pdfoutput=1|})
        (tag ^ ": no engine branch, prim ok"));
  run "L3-011 clean: engine branch without pdfTeX prims" (fun tag ->
      expect
        (does_not_fire "L3-011" {|\ifluatex
\directlua{tex.print("hello")}
\fi|})
        (tag ^ ": lua code ok"));

  (* ══════════════════════════════════════════════════════════════════════
     Precondition mapping tests
     ══════════════════════════════════════════════════════════════════════ *)
  run "L3-001 maps to L1" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "L3-001" = Validators.L1)
        (tag ^ ": L3-001 = L1"));
  run "L3-005 maps to L1" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "L3-005" = Validators.L1)
        (tag ^ ": L3-005 = L1"));
  run "L3-008 maps to L2 (not implemented)" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "L3-008" = Validators.L2)
        (tag ^ ": L3-008 = L2"));
  run "L3-010 maps to L2 (not implemented)" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "L3-010" = Validators.L2)
        (tag ^ ": L3-010 = L2"));
  run "L3-011 maps to L1" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "L3-011" = Validators.L1)
        (tag ^ ": L3-011 = L1"));

  if !fails > 0 then (
    Printf.eprintf "[expl3] %d failure(s)\n%!" !fails;
    exit 1)
  else Printf.printf "[expl3] PASS %d cases\n%!" !cases
