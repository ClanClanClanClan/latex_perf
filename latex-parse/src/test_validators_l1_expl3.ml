(** Unit tests for Validators_l1_expl3:
    CHAR-004, MATH-006, L3-001..L3-011 (12 rules, 60+ cases). *)

open Latex_parse_lib
open Test_helpers

let () =
  (* ══════════════════════════════════════════════════════════════════════
     CHAR-004: Private-use (U+E000-F8FF) policy rule
     ══════════════════════════════════════════════════════════════════════ *)
  run "CHAR-004 fires: U+E000 (first PUA codepoint)" (fun tag ->
      expect
        (fires "CHAR-004" "Hello \xee\x80\x80 world")
        (tag ^ ": U+E000 detected"));
  run "CHAR-004 fires: U+F8FF (last PUA codepoint, Apple logo)" (fun tag ->
      expect
        (fires "CHAR-004" "Test \xef\xa3\xbf end")
        (tag ^ ": U+F8FF detected"));
  run "CHAR-004 fires: count=2 for two PUA chars" (fun tag ->
      expect
        (fires_with_count "CHAR-004"
           "A\xee\x80\x80B\xee\x80\x81C" 2)
        (tag ^ ": count=2"));
  run "CHAR-004 fires: U+F000 (mid-range PUA)" (fun tag ->
      expect
        (fires "CHAR-004" "X\xef\x80\x80Y")
        (tag ^ ": U+F000 detected"));
  run "CHAR-004 clean: plain ASCII" (fun tag ->
      expect
        (does_not_fire "CHAR-004" "Hello world, no special chars")
        (tag ^ ": ASCII only"));
  run "CHAR-004 clean: U+F900 (CJK, above PUA)" (fun tag ->
      expect
        (does_not_fire "CHAR-004" "Text \xef\xa4\x80 end")
        (tag ^ ": U+F900 is above PUA range"));
  run "CHAR-004 clean: normal UTF-8 (accented chars)" (fun tag ->
      expect
        (does_not_fire "CHAR-004"
           "R\xc3\xa9sum\xc3\xa9 with \xc3\xa0ccents")
        (tag ^ ": normal multibyte ok"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-006: Bra-ket spacing (quantum-style) rule
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-006 fires: langle/rangle without separator" (fun tag ->
      expect
        (fires "MATH-006" {|$\langle \psi \rangle$|})
        (tag ^ ": no separator"));
  run "MATH-006 fires: in align env" (fun tag ->
      expect
        (fires "MATH-006"
           {|\begin{align}\langle x \rangle\end{align}|})
        (tag ^ ": in align env"));
  run "MATH-006 fires: count=2" (fun tag ->
      expect
        (fires_with_count "MATH-006"
           {|$\langle a \rangle + \langle b \rangle$|} 2)
        (tag ^ ": count=2"));
  run "MATH-006 clean: with \\mid separator" (fun tag ->
      expect
        (does_not_fire "MATH-006" {|$\langle \psi \mid \phi \rangle$|})
        (tag ^ ": has \\mid"));
  run "MATH-006 clean: with | separator" (fun tag ->
      expect
        (does_not_fire "MATH-006" {|$\langle \psi | \phi \rangle$|})
        (tag ^ ": has pipe"));
  run "MATH-006 clean: not in math mode" (fun tag ->
      expect
        (does_not_fire "MATH-006"
           {|The symbols \langle and \rangle are delimiters.|})
        (tag ^ ": outside math"));

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
        (tag ^ ": mixed in preamble"));
  run "L3-001 fires: int_new + renewcommand" (fun tag ->
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
        (tag ^ ": only 2e"));
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
        (tag ^ ": mixing in body"));

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
        (tag ^ ": in preamble ok"));
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
  run "L3-003 fires: cs_new + apptocmd" (fun tag ->
      expect
        (fires "L3-003"
           {|\cs_new:Npn \my_func:n #1 {#1}
\apptocmd{\section}{code}{}{}|})
        (tag ^ ": cs_new + apptocmd"));
  run "L3-003 fires: expl3 + pretocmd" (fun tag ->
      expect
        (fires "L3-003"
           {|\ExplSyntaxOn
\cs_new:Npn \foo:n #1 {ok}
\ExplSyntaxOff
\pretocmd{\chapter}{code}{}{}|})
        (tag ^ ": expl3 + pretocmd"));
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
        (tag ^ ": internal fn"));
  run "L3-004 fires: count=2" (fun tag ->
      expect
        (fires_with_count "L3-004"
           {|\__foo_bar:nn {a}{b}
\__baz_helper:N \l_x|}
           2)
        (tag ^ ": count=2"));
  run "L3-004 fires: double underscore with empty argspec" (fun tag ->
      expect
        (fires "L3-004" {|\__kernel_check: something|})
        (tag ^ ": empty argspec"));
  run "L3-004 clean: public function" (fun tag ->
      expect
        (does_not_fire "L3-004" {|\tl_set:Nn \l_foo {bar}|})
        (tag ^ ": public function ok"));
  run "L3-004 clean: plain text" (fun tag ->
      expect
        (does_not_fire "L3-004" "Hello world")
        (tag ^ ": no expl3"));

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
  run "L3-005 clean: plain LaTeX" (fun tag ->
      expect
        (does_not_fire "L3-005"
           {|\documentclass{article}
\begin{document}Hello\end{document}|})
        (tag ^ ": plain LaTeX"));

  (* ══════════════════════════════════════════════════════════════════════
     L3-007: Mix of camelCase and snake_case in expl3 names
     ══════════════════════════════════════════════════════════════════════ *)
  run "L3-007 fires: camelCase in expl3" (fun tag ->
      expect
        (fires "L3-007"
           {|\ExplSyntaxOn
\myFunc_helper:n {x}
\ExplSyntaxOff|})
        (tag ^ ": camelCase function"));
  run "L3-007 fires: multiple camelCase" (fun tag ->
      expect
        (fires_with_count "L3-007"
           {|\ExplSyntaxOn
\myFunc_helper:n {x}
\anotherThing_test:N \l_x
\ExplSyntaxOff|}
           2)
        (tag ^ ": count=2"));
  run "L3-007 clean: snake_case only" (fun tag ->
      expect
        (does_not_fire "L3-007"
           {|\ExplSyntaxOn
\my_func_helper:n {x}
\ExplSyntaxOff|})
        (tag ^ ": snake_case ok"));
  run "L3-007 clean: no expl3 context" (fun tag ->
      expect
        (does_not_fire "L3-007" {|\newcommand{\myCommand}{foo}|})
        (tag ^ ": no expl3 region"));

  (* ══════════════════════════════════════════════════════════════════════
     L3-008: Expl3 module lacks \ProvidesExplPackage
     ══════════════════════════════════════════════════════════════════════ *)
  run "L3-008 fires: ExplSyntaxOn without Provides" (fun tag ->
      expect
        (fires "L3-008" {|\ExplSyntaxOn
\cs_new:Npn \foo:n #1 {#1}
\ExplSyntaxOff|})
        (tag ^ ": no ProvidesExplPackage"));
  run "L3-008 fires: expl3 functions without Provides" (fun tag ->
      expect
        (fires "L3-008" {|\tl_new:N \l_foo|})
        (tag ^ ": tl_new without Provides"));
  run "L3-008 clean: with ProvidesExplPackage" (fun tag ->
      expect
        (does_not_fire "L3-008"
           {|\ProvidesExplPackage{mypkg}{2024-01-01}{1.0}{My package}
\ExplSyntaxOn
\cs_new:Npn \foo:n #1 {#1}
\ExplSyntaxOff|})
        (tag ^ ": has ProvidesExplPackage"));
  run "L3-008 clean: with ProvidesExplClass" (fun tag ->
      expect
        (does_not_fire "L3-008"
           {|\ProvidesExplClass{mycls}{2024-01-01}{1.0}{My class}
\ExplSyntaxOn
\tl_new:N \l_foo
\ExplSyntaxOff|})
        (tag ^ ": has ProvidesExplClass"));
  run "L3-008 clean: no expl3 code" (fun tag ->
      expect
        (does_not_fire "L3-008" {|\documentclass{article}
\newcommand{\foo}{bar}|})
        (tag ^ ": no expl3"));

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
        (fires_with_count "L3-009"
           {|\tl_to_str:n {a}
\fp_eval:n {3.14}|}
           2)
        (tag ^ ": count=2"));
  run "L3-009 clean: non-deprecated functions" (fun tag ->
      expect
        (does_not_fire "L3-009" {|\tl_set:Nn \l_foo {bar}|})
        (tag ^ ": non-deprecated ok"));
  run "L3-009 clean: plain text" (fun tag ->
      expect
        (does_not_fire "L3-009" "Just some text")
        (tag ^ ": no expl3"));

  (* ══════════════════════════════════════════════════════════════════════
     L3-010: ExplSyntaxOff missing at end of file
     ══════════════════════════════════════════════════════════════════════ *)
  run "L3-010 fires: ExplSyntaxOn without Off" (fun tag ->
      expect
        (fires "L3-010"
           {|\ExplSyntaxOn
\cs_new:Npn \foo:n #1 {#1}|})
        (tag ^ ": On without Off"));
  run "L3-010 fires: two On, one Off" (fun tag ->
      expect
        (fires "L3-010"
           {|\ExplSyntaxOn
\tl_set:Nn \l_foo {bar}
\ExplSyntaxOff
\ExplSyntaxOn
\cs_new:Npn \bar:n #1 {#1}|})
        (tag ^ ": 2 On, 1 Off"));
  run "L3-010 fires: count reflects mismatch" (fun tag ->
      expect
        (fires_with_count "L3-010"
           {|\ExplSyntaxOn
\ExplSyntaxOn|} 2)
        (tag ^ ": count=2 for 2 On, 0 Off"));
  run "L3-010 clean: balanced On/Off" (fun tag ->
      expect
        (does_not_fire "L3-010"
           {|\ExplSyntaxOn
\cs_new:Npn \foo:n #1 {#1}
\ExplSyntaxOff|})
        (tag ^ ": balanced"));
  run "L3-010 clean: no ExplSyntaxOn" (fun tag ->
      expect
        (does_not_fire "L3-010" {|\newcommand{\foo}{bar}|})
        (tag ^ ": no expl3"));

  (* ══════════════════════════════════════════════════════════════════════
     L3-011: Engine-branch uses pdfTeX primitive in Lua/XeTeX path
     ══════════════════════════════════════════════════════════════════════ *)
  run "L3-011 fires: ifluatex + pdfoutput" (fun tag ->
      expect
        (fires "L3-011"
           {|\ifluatex
\pdfoutput=1
\fi|})
        (tag ^ ": pdfTeX prim in LuaTeX branch"));
  run "L3-011 fires: ifXeTeX + pdfliteral" (fun tag ->
      expect
        (fires "L3-011"
           {|\ifXeTeX
\pdfliteral{q 1 0 0 rg}
\fi|})
        (tag ^ ": pdfliteral in XeTeX branch"));
  run "L3-011 fires: fontspec + pdfoutput" (fun tag ->
      expect
        (fires "L3-011"
           {|\usepackage{fontspec}
\pdfoutput=1|})
        (tag ^ ": fontspec implies Lua/XeTeX"));
  run "L3-011 fires: count=2" (fun tag ->
      expect
        (fires_with_count "L3-011"
           {|\ifluatex
\pdfoutput=1
\pdfminorversion=7
\fi|}
           2)
        (tag ^ ": count=2 prims"));
  run "L3-011 clean: no engine branch" (fun tag ->
      expect
        (does_not_fire "L3-011" {|\pdfoutput=1|})
        (tag ^ ": no engine branch"));
  run "L3-011 clean: engine branch without pdfTeX prims" (fun tag ->
      expect
        (does_not_fire "L3-011"
           {|\ifluatex
\directlua{tex.print("hello")}
\fi|})
        (tag ^ ": lua code ok"));

  (* ══════════════════════════════════════════════════════════════════════
     Precondition mapping tests
     ══════════════════════════════════════════════════════════════════════ *)
  run "CHAR-004 maps to L0" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "CHAR-004" = Validators.L0)
        (tag ^ ": CHAR-004 = L0"));
  run "MATH-006 maps to L1" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "MATH-006" = Validators.L1)
        (tag ^ ": MATH-006 = L1"));
  run "L3-001 maps to L1" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "L3-001" = Validators.L1)
        (tag ^ ": L3-001 = L1"));
  run "L3-008 maps to L2" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "L3-008" = Validators.L2)
        (tag ^ ": L3-008 = L2"));
  run "L3-010 maps to L2" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "L3-010" = Validators.L2)
        (tag ^ ": L3-010 = L2"))

let () = finalise "l1_expl3"
