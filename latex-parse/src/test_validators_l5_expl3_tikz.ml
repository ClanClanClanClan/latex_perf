(** Unit tests for L5 batch: 25 rules across L3-expl3, TIKZ, LANG, and others.
    L3-001..L3-011, TIKZ-001/003/004/006/009/010, LANG-001/006/007/013, COL-006,
    L3-008/L3-010, LAY-024, META-002, RTL-005.

    ~104 total test cases. *)

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

let () =
  Unix.putenv "L0_VALIDATORS" "pilot";

  (* ══════════════════════════════════════════════════════════════════════
     L3-001: LaTeX3 \tl_new:N in preamble mixed with 2e macros
     ══════════════════════════════════════════════════════════════════════ *)
  run "L3-001 fires: expl3 + newcommand in preamble" (fun tag ->
      expect
        (fires "L3-001"
           {|\documentclass{article}
\tl_new:N \l_my_tl
\newcommand{\foo}{bar}
\begin{document}
Hello
\end{document}|})
        (tag ^ ": mixed expl3 and 2e in preamble"));
  run "L3-001 fires: cs_new + def in preamble" (fun tag ->
      expect
        (fires "L3-001"
           {|\documentclass{article}
\cs_new:Npn \my_func:n #1 {#1}
\def\myfoo{bar}
\begin{document}\end{document}|})
        (tag ^ ": cs_new + def"));
  run "L3-001 clean: only 2e macros" (fun tag ->
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

  (* ══════════════════════════════════════════════════════════════════════
     L3-002: Expl3 variable declared after \begin{document}
     ══════════════════════════════════════════════════════════════════════ *)
  run "L3-002 fires: tl_new in body" (fun tag ->
      expect
        (fires "L3-002"
           {|\documentclass{article}
\begin{document}
\tl_new:N \l_my_tl
\end{document}|})
        (tag ^ ": tl_new after begin{document}"));
  run "L3-002 fires: bool_new in body" (fun tag ->
      expect
        (fires "L3-002"
           {|\documentclass{article}
\begin{document}
\bool_new:N \l_flag
\end{document}|})
        (tag ^ ": bool_new in body"));
  run "L3-002 clean: declaration in preamble" (fun tag ->
      expect
        (does_not_fire "L3-002"
           {|\documentclass{article}
\tl_new:N \l_my_tl
\begin{document}\end{document}|})
        (tag ^ ": preamble ok"));
  run "L3-002 clean: no expl3" (fun tag ->
      expect
        (does_not_fire "L3-002"
           {|\documentclass{article}
\begin{document}
Hello world
\end{document}|})
        (tag ^ ": no expl3"));

  (* ══════════════════════════════════════════════════════════════════════
     L3-003: Expl3 and etoolbox patch macros combined
     ══════════════════════════════════════════════════════════════════════ *)
  run "L3-003 fires: expl3 + patchcmd" (fun tag ->
      expect
        (fires "L3-003"
           {|\ExplSyntaxOn
\tl_set:Nn \l_foo {bar}
\ExplSyntaxOff
\patchcmd{\maketitle}{}{}{}{}|})
        (tag ^ ": expl3 + patchcmd"));
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
\int_new:N \l_count
\ExplSyntaxOff
\pretocmd{\maketitle}{code}{}{}|})
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
        (tag ^ ": double underscore function"));
  run "L3-004 fires: __foo_bar:nn" (fun tag ->
      expect (fires "L3-004" {|\__foo_bar:nn {a}{b}|}) (tag ^ ": __foo_bar"));
  run "L3-004 clean: public function" (fun tag ->
      expect
        (does_not_fire "L3-004" {|\tl_set:Nn \l_foo {bar}|})
        (tag ^ ": public function ok"));
  run "L3-004 clean: no expl3" (fun tag ->
      expect
        (does_not_fire "L3-004" {|\newcommand{\foo}{bar}|})
        (tag ^ ": no expl3 at all"));

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
  run "L3-006 fires: amsmath prefix clash" (fun tag ->
      expect
        (fires "L3-006" {|\usepackage{amsmath}
\l_amsmath_extra:N \l_x|})
        (tag ^ ": amsmath prefix clash"));
  run "L3-006 fires: foo package clash" (fun tag ->
      expect
        (fires "L3-006" {|\usepackage{foo}
\l_foo_var:N \l_a|})
        (tag ^ ": foo prefix clash"));
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
  run "L3-007 fires: mixedCase function name" (fun tag ->
      expect
        (fires "L3-007"
           {|\ExplSyntaxOn
\parseResult_check:n {x}
\ExplSyntaxOff|})
        (tag ^ ": parseResult camelCase"));
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
  run "L3-009 fires: fp_eval:n" (fun tag ->
      expect
        (fires "L3-009" {|\fp_eval:n {3.14}|})
        (tag ^ ": deprecated fp_eval:n"));
  run "L3-009 clean: non-deprecated :N variant" (fun tag ->
      expect
        (does_not_fire "L3-009" {|\tl_set:Nn \l_foo {bar}|})
        (tag ^ ": :Nn not deprecated"));

  (* ══════════════════════════════════════════════════════════════════════
     L3-011: Engine-branch uses pdfTeX primitive in Lua/XeTeX path
     ══════════════════════════════════════════════════════════════════════ *)
  run "L3-011 fires: sys_if_engine_luatex + pdfoutput" (fun tag ->
      expect
        (fires "L3-011" {|\sys_if_engine_luatex:T { \pdfoutput=1 }|})
        (tag ^ ": pdfTeX prim in LuaTeX branch"));
  run "L3-011 fires: sys_if_engine_xetex + pdfliteral" (fun tag ->
      expect
        (fires "L3-011" {|\sys_if_engine_xetex:T { \pdfliteral{q 1 0 0 rg} }|})
        (tag ^ ": pdfliteral in XeTeX branch"));
  run "L3-011 fires: luatex + pdfcatalog" (fun tag ->
      expect
        (fires "L3-011"
           {|\sys_if_engine_luatex:T { \pdfcatalog{/PageMode /UseOutlines} }|})
        (tag ^ ": pdfcatalog in LuaTeX branch"));
  run "L3-011 clean: no engine branch" (fun tag ->
      expect
        (does_not_fire "L3-011" {|\pdfoutput=1|})
        (tag ^ ": pdfTeX prim without branch ok"));
  run "L3-011 clean: engine branch without pdfTeX prims" (fun tag ->
      expect
        (does_not_fire "L3-011"
           {|\sys_if_engine_luatex:T { \directlua{tex.print("hello")} }|})
        (tag ^ ": lua code ok"));

  (* ══════════════════════════════════════════════════════════════════════
     TIKZ-001: TikZ picture outside figure environment
     ══════════════════════════════════════════════════════════════════════ *)
  run "TIKZ-001 fires: tikzpicture not in figure" (fun tag ->
      expect
        (fires "TIKZ-001"
           {|\documentclass{article}
\begin{document}
\begin{tikzpicture}
\draw (0,0) -- (1,1);
\end{tikzpicture}
\end{document}|})
        (tag ^ ": tikzpicture outside figure"));
  run "TIKZ-001 fires: bare tikzpicture" (fun tag ->
      expect
        (fires "TIKZ-001"
           {|\begin{tikzpicture}
\draw (0,0) circle (1);
\end{tikzpicture}|})
        (tag ^ ": bare tikzpicture"));
  run "TIKZ-001 clean: tikzpicture inside figure" (fun tag ->
      expect
        (does_not_fire "TIKZ-001"
           {|\begin{figure}
\begin{tikzpicture}
\draw (0,0) -- (1,1);
\end{tikzpicture}
\caption{A diagram}
\end{figure}|})
        (tag ^ ": inside figure ok"));
  run "TIKZ-001 clean: no tikzpicture" (fun tag ->
      expect
        (does_not_fire "TIKZ-001"
           {|\documentclass{article}
\begin{document}
Hello
\end{document}|})
        (tag ^ ": no tikzpicture"));

  (* ══════════════════════════════════════════════════════════════════════
     TIKZ-003: pgfplots axis labels not in math mode
     ══════════════════════════════════════════════════════════════════════ *)
  run "TIKZ-003 fires: xlabel without math in axis body" (fun tag ->
      expect
        (fires "TIKZ-003"
           {|\begin{axis}
xlabel={Temperature}
\addplot coordinates {(1,2)(3,4)};
\end{axis}|})
        (tag ^ ": xlabel no math"));
  run "TIKZ-003 fires: ylabel without math in axis body" (fun tag ->
      expect
        (fires "TIKZ-003"
           {|\begin{axis}
ylabel={Pressure}
\addplot coordinates {(1,2)(3,4)};
\end{axis}|})
        (tag ^ ": ylabel no math"));
  run "TIKZ-003 clean: xlabel in math mode" (fun tag ->
      expect
        (does_not_fire "TIKZ-003"
           {|\begin{axis}
xlabel={$T$}
\addplot coordinates {(1,2)(3,4)};
\end{axis}|})
        (tag ^ ": xlabel with math ok"));
  run "TIKZ-003 clean: no axis environment" (fun tag ->
      expect
        (does_not_fire "TIKZ-003" {|xlabel={Temperature}|})
        (tag ^ ": outside axis ok"));

  (* ══════════════════════════════════════════════════════════════════════
     TIKZ-004: Hard-coded RGB values instead of xcolor names
     ══════════════════════════════════════════════════════════════════════ *)
  run "TIKZ-004 fires: color={rgb" (fun tag ->
      expect
        (fires "TIKZ-004" {|color={rgb,255:red,100;green,200;blue,50}|})
        (tag ^ ": hard-coded rgb"));
  run "TIKZ-004 fires: fill={RGB" (fun tag ->
      expect
        (fires "TIKZ-004" {|fill={RGB,255:red,100;green,200;blue,50}|})
        (tag ^ ": hard-coded RGB"));
  run "TIKZ-004 fires: draw={rgb" (fun tag ->
      expect
        (fires "TIKZ-004" {|draw={rgb,255:red,50;green,100;blue,150}|})
        (tag ^ ": draw with rgb"));
  run "TIKZ-004 clean: named color" (fun tag ->
      expect (does_not_fire "TIKZ-004" {|color=blue|}) (tag ^ ": named color ok"));
  run "TIKZ-004 clean: no color specification" (fun tag ->
      expect
        (does_not_fire "TIKZ-004" {|Just some plain text.|})
        (tag ^ ": no color"));

  (* ══════════════════════════════════════════════════════════════════════
     TIKZ-006: Missing \caption for tikzpicture inside figure
     ══════════════════════════════════════════════════════════════════════ *)
  run "TIKZ-006 fires: tikzpicture in figure, no caption" (fun tag ->
      expect
        (fires "TIKZ-006"
           {|\begin{figure}
\begin{tikzpicture}
\draw (0,0) -- (1,1);
\end{tikzpicture}
\end{figure}|})
        (tag ^ ": figure with tikz but no caption"));
  run "TIKZ-006 fires: figure* without caption" (fun tag ->
      expect
        (fires "TIKZ-006"
           {|\begin{figure*}
\begin{tikzpicture}
\draw (0,0) circle (1);
\end{tikzpicture}
\end{figure*}|})
        (tag ^ ": figure* no caption"));
  run "TIKZ-006 clean: tikzpicture in figure with caption" (fun tag ->
      expect
        (does_not_fire "TIKZ-006"
           {|\begin{figure}
\begin{tikzpicture}
\draw (0,0) -- (1,1);
\end{tikzpicture}
\caption{A diagram}
\end{figure}|})
        (tag ^ ": has caption ok"));
  run "TIKZ-006 clean: no tikzpicture in figure" (fun tag ->
      expect
        (does_not_fire "TIKZ-006"
           {|\begin{figure}
\includegraphics{img}
\caption{Image}
\end{figure}|})
        (tag ^ ": no tikz in figure"));

  (* ══════════════════════════════════════════════════════════════════════
     TIKZ-009: TikZ library arrows.meta missing for arrow tips
     ══════════════════════════════════════════════════════════════════════ *)
  run "TIKZ-009 fires: arrow tip without library" (fun tag ->
      expect
        (fires "TIKZ-009"
           {|\begin{tikzpicture}
\draw[->] (0,0) -- (1,1);
\end{tikzpicture}|})
        (tag ^ ": -> without arrows.meta"));
  run "TIKZ-009 fires: stealth tip without library" (fun tag ->
      expect
        (fires "TIKZ-009"
           {|\begin{tikzpicture}
\draw[stealth] (0,0) -- (1,0);
\end{tikzpicture}|})
        (tag ^ ": stealth without arrows.meta"));
  run "TIKZ-009 clean: arrows.meta loaded" (fun tag ->
      expect
        (does_not_fire "TIKZ-009"
           {|\usetikzlibrary{arrows.meta}
\begin{tikzpicture}
\draw[->] (0,0) -- (1,1);
\end{tikzpicture}|})
        (tag ^ ": has arrows.meta ok"));
  run "TIKZ-009 clean: no arrow tips" (fun tag ->
      expect
        (does_not_fire "TIKZ-009"
           {|\begin{tikzpicture}
\draw (0,0) -- (1,1);
\end{tikzpicture}|})
        (tag ^ ": no arrows"));

  (* ══════════════════════════════════════════════════════════════════════
     TIKZ-010: Deprecated \pgfplotsset key used
     ══════════════════════════════════════════════════════════════════════ *)
  run "TIKZ-010 fires: every axis" (fun tag ->
      expect
        (fires "TIKZ-010"
           {|\pgfplotsset{every axis/.append style={line width=1pt}}|})
        (tag ^ ": every axis deprecated"));
  run "TIKZ-010 fires: compat=1.5" (fun tag ->
      expect
        (fires "TIKZ-010" {|\pgfplotsset{compat=1.5}|})
        (tag ^ ": compat=1.5 deprecated"));
  run "TIKZ-010 fires: compat=1.3" (fun tag ->
      expect
        (fires "TIKZ-010" {|\pgfplotsset{compat=1.3}|})
        (tag ^ ": compat=1.3 deprecated"));
  run "TIKZ-010 clean: compat=1.9" (fun tag ->
      expect
        (does_not_fire "TIKZ-010" {|\pgfplotsset{compat=1.9}|})
        (tag ^ ": compat=1.9 ok"));
  run "TIKZ-010 clean: no pgfplotsset" (fun tag ->
      expect
        (does_not_fire "TIKZ-010" {|Just some text.|})
        (tag ^ ": no pgfplotsset"));

  (* ══════════════════════════════════════════════════════════════════════
     LANG-001: \usepackage[british]{babel} but US spelling detected
     ══════════════════════════════════════════════════════════════════════ *)
  run "LANG-001 fires: british babel + US spelling 'color'" (fun tag ->
      expect
        (fires "LANG-001"
           {|\documentclass{article}
\usepackage[british]{babel}
\begin{document}
The color of the sky is blue.
\end{document}|})
        (tag ^ ": british + color"));
  run "LANG-001 fires: british babel + US 'center'" (fun tag ->
      expect
        (fires "LANG-001"
           {|\documentclass{article}
\usepackage[british]{babel}
\begin{document}
Go to the center of town.
\end{document}|})
        (tag ^ ": british + center"));
  run "LANG-001 fires: UKenglish + US 'analyze'" (fun tag ->
      expect
        (fires "LANG-001"
           {|\documentclass{article}
\usepackage[UKenglish]{babel}
\begin{document}
We analyze the data carefully.
\end{document}|})
        (tag ^ ": UKenglish + analyze"));
  run "LANG-001 clean: british babel + British spellings" (fun tag ->
      expect
        (does_not_fire "LANG-001"
           {|\documentclass{article}
\usepackage[british]{babel}
\begin{document}
The colour of the sky is blue.
\end{document}|})
        (tag ^ ": british + colour ok"));
  run "LANG-001 clean: american babel + US spellings" (fun tag ->
      expect
        (does_not_fire "LANG-001"
           {|\documentclass{article}
\usepackage[american]{babel}
\begin{document}
The color is nice.
\end{document}|})
        (tag ^ ": american + color ok"));

  (* ══════════════════════════════════════════════════════════════════════
     LANG-006: Non-English abstract before \selectlanguage
     ══════════════════════════════════════════════════════════════════════ *)
  run "LANG-006 fires: abstract before selectlanguage" (fun tag ->
      expect
        (fires "LANG-006"
           {|\documentclass{article}
\begin{document}
\begin{abstract}
This is the abstract.
\end{abstract}
\selectlanguage{french}
Content here.
\end{document}|})
        (tag ^ ": abstract before selectlanguage"));
  run "LANG-006 clean: selectlanguage before abstract" (fun tag ->
      expect
        (does_not_fire "LANG-006"
           {|\documentclass{article}
\begin{document}
\selectlanguage{french}
\begin{abstract}
Ceci est le resume.
\end{abstract}
\end{document}|})
        (tag ^ ": selectlanguage first ok"));
  run "LANG-006 clean: no selectlanguage" (fun tag ->
      expect
        (does_not_fire "LANG-006"
           {|\documentclass{article}
\begin{document}
\begin{abstract}
Abstract text.
\end{abstract}
\end{document}|})
        (tag ^ ": no selectlanguage"));
  run "LANG-006 clean: no abstract" (fun tag ->
      expect
        (does_not_fire "LANG-006"
           {|\documentclass{article}
\begin{document}
\selectlanguage{french}
Content here.
\end{document}|})
        (tag ^ ": no abstract"));

  (* ══════════════════════════════════════════════════════════════════════
     LANG-007: babel shorthand mis-used instead of og/fg
     ══════════════════════════════════════════════════════════════════════ *)
  run "LANG-007 fires: french babel + double quotes" (fun tag ->
      expect
        (fires "LANG-007"
           {|\documentclass{article}
\usepackage[french]{babel}
\begin{document}
Il a dit ""bonjour"" au professeur.
\end{document}|})
        (tag ^ ": french + double quotes"));
  run "LANG-007 fires: francais babel + quotes" (fun tag ->
      expect
        (fires "LANG-007"
           {|\documentclass{article}
\usepackage[francais]{babel}
\begin{document}
Un ""mot"" special.
\end{document}|})
        (tag ^ ": francais + quotes"));
  run "LANG-007 clean: french babel without shorthand" (fun tag ->
      expect
        (does_not_fire "LANG-007"
           {|\documentclass{article}
\usepackage[french]{babel}
\begin{document}
Il a dit \og bonjour \fg au professeur.
\end{document}|})
        (tag ^ ": og/fg ok"));
  run "LANG-007 clean: not french babel" (fun tag ->
      expect
        (does_not_fire "LANG-007"
           {|\documentclass{article}
\usepackage[english]{babel}
\begin{document}
He said ""hello"" to the teacher.
\end{document}|})
        (tag ^ ": not french"));

  (* ══════════════════════════════════════════════════════════════════════
     LANG-013: Abstract language differs from \selectlanguage (Implementation
     checks: first \selectlanguage in body vs. first \selectlanguage before
     \begin{abstract}. These differ only when there are multiple \selectlanguage
     calls with different languages before the abstract.)
     ══════════════════════════════════════════════════════════════════════ *)
  run "LANG-013 fires: different languages" (fun tag ->
      expect
        (fires "LANG-013"
           {|\documentclass{article}
\begin{document}
\selectlanguage{english}
\begin{abstract}
Abstract text.
\end{abstract}
\selectlanguage{french}
Le texte principal.
\end{document}|})
        (tag ^ ": english then french"));
  run "LANG-013 clean: same language before abstract" (fun tag ->
      expect
        (does_not_fire "LANG-013"
           {|\documentclass{article}
\begin{document}
\selectlanguage{french}
\begin{abstract}
Resume ici.
\end{abstract}
\selectlanguage{french}
Suite.
\end{document}|})
        (tag ^ ": same language ok"));
  run "LANG-013 clean: no selectlanguage" (fun tag ->
      expect
        (does_not_fire "LANG-013"
           {|\documentclass{article}
\begin{document}
\begin{abstract}
Abstract text.
\end{abstract}
\end{document}|})
        (tag ^ ": no selectlanguage"));
  run "LANG-013 clean: selectlanguage after abstract only" (fun tag ->
      expect
        (does_not_fire "LANG-013"
           {|\documentclass{article}
\begin{document}
\begin{abstract}
Abstract here.
\end{abstract}
\selectlanguage{english}
\end{document}|})
        (tag ^ ": selectlanguage only after abstract"));
  run "LANG-013 clean: no abstract" (fun tag ->
      expect
        (does_not_fire "LANG-013"
           {|\documentclass{article}
\begin{document}
\selectlanguage{french}
Content here.
\end{document}|})
        (tag ^ ": no abstract"));

  (* ══════════════════════════════════════════════════════════════════════
     COL-006: xcolor option dvipsnames used with pdfLaTeX
     ══════════════════════════════════════════════════════════════════════ *)
  run "COL-006 fires: dvipsnames xcolor + T1 fontenc" (fun tag ->
      expect
        (fires "COL-006"
           {|\documentclass{article}
\usepackage[T1]{fontenc}
\usepackage[dvipsnames]{xcolor}
\begin{document}\end{document}|})
        (tag ^ ": dvipsnames + T1 fontenc"));
  run "COL-006 fires: dvipsnames xcolor + inputenc" (fun tag ->
      expect
        (fires "COL-006"
           {|\documentclass{article}
\usepackage[utf8]{inputenc}
\usepackage[dvipsnames]{xcolor}
\begin{document}\end{document}|})
        (tag ^ ": dvipsnames + inputenc"));
  run "COL-006 clean: dvipsnames without pdfLaTeX markers" (fun tag ->
      expect
        (does_not_fire "COL-006"
           {|\documentclass{article}
\usepackage[dvipsnames]{xcolor}
\begin{document}\end{document}|})
        (tag ^ ": dvipsnames alone ok"));
  run "COL-006 clean: xcolor without dvipsnames" (fun tag ->
      expect
        (does_not_fire "COL-006"
           {|\documentclass{article}
\usepackage[T1]{fontenc}
\usepackage{xcolor}
\begin{document}\end{document}|})
        (tag ^ ": xcolor no dvipsnames"));

  (* ══════════════════════════════════════════════════════════════════════
     L3-008: Expl3 module lacks \ProvidesExplPackage
     ══════════════════════════════════════════════════════════════════════ *)
  run "L3-008 fires: expl3 without ProvidesExplPackage" (fun tag ->
      expect
        (fires "L3-008"
           {|\ExplSyntaxOn
\tl_new:N \l_my_tl
\cs_new:Npn \my_func:n #1 {#1}
\ExplSyntaxOff|})
        (tag ^ ": no ProvidesExplPackage"));
  run "L3-008 fires: expl3 code only" (fun tag ->
      expect
        (fires "L3-008" {|\int_new:N \l_count|})
        (tag ^ ": bare expl3 no provides"));
  run "L3-008 clean: with ProvidesExplPackage" (fun tag ->
      expect
        (does_not_fire "L3-008"
           {|\ProvidesExplPackage{mypackage}{2024/01/01}{1.0}{My package}
\tl_new:N \l_my_tl|})
        (tag ^ ": ProvidesExplPackage present"));
  run "L3-008 clean: with ProvidesExplClass" (fun tag ->
      expect
        (does_not_fire "L3-008"
           {|\ProvidesExplClass{myclass}{2024/01/01}{1.0}{My class}
\cs_new:Npn \my_func:n #1 {#1}|})
        (tag ^ ": ProvidesExplClass present"));
  run "L3-008 clean: no expl3 code" (fun tag ->
      expect
        (does_not_fire "L3-008" {|\newcommand{\foo}{bar}|})
        (tag ^ ": no expl3"));

  (* ══════════════════════════════════════════════════════════════════════
     L3-010: \ExplSyntaxOff missing at end of file
     ══════════════════════════════════════════════════════════════════════ *)
  run "L3-010 fires: ExplSyntaxOn without Off" (fun tag ->
      expect
        (fires "L3-010" {|\ExplSyntaxOn
\tl_new:N \l_my_tl|})
        (tag ^ ": missing ExplSyntaxOff"));
  run "L3-010 fires: two On, one Off" (fun tag ->
      expect
        (fires "L3-010"
           {|\ExplSyntaxOn
\tl_new:N \l_a
\ExplSyntaxOff
\ExplSyntaxOn
\tl_new:N \l_b|})
        (tag ^ ": 2 On, 1 Off"));
  run "L3-010 clean: balanced On/Off" (fun tag ->
      expect
        (does_not_fire "L3-010"
           {|\ExplSyntaxOn
\tl_new:N \l_my_tl
\ExplSyntaxOff|})
        (tag ^ ": balanced ok"));
  run "L3-010 clean: no ExplSyntaxOn" (fun tag ->
      expect
        (does_not_fire "L3-010" {|\newcommand{\foo}{bar}|})
        (tag ^ ": no ExplSyntaxOn"));

  (* ══════════════════════════════════════════════════════════════════════
     LAY-024: \subsubsubsection depth > 3 without class support
     ══════════════════════════════════════════════════════════════════════ *)
  run "LAY-024 fires: subsubsubsection present" (fun tag ->
      expect
        (fires "LAY-024"
           {|\documentclass{article}
\begin{document}
\subsubsubsection{Too Deep}
Content here.
\end{document}|})
        (tag ^ ": subsubsubsection found"));
  run "LAY-024 fires: multiple subsubsubsections" (fun tag ->
      expect
        (fires "LAY-024" {|\subsubsubsection{First}
\subsubsubsection{Second}|})
        (tag ^ ": two subsubsubsections"));
  run "LAY-024 clean: subsubsection only" (fun tag ->
      expect
        (does_not_fire "LAY-024"
           {|\documentclass{article}
\begin{document}
\subsubsection{This is Fine}
\end{document}|})
        (tag ^ ": subsubsection ok"));
  run "LAY-024 clean: no section commands" (fun tag ->
      expect
        (does_not_fire "LAY-024" {|Just some plain text.|})
        (tag ^ ": no sections"));

  (* ══════════════════════════════════════════════════════════════════════
     META-002: Revision hash missing from \date field
     ══════════════════════════════════════════════════════════════════════ *)
  run "META-002 fires: date without hash" (fun tag ->
      expect
        (fires "META-002"
           {|\documentclass{article}
\date{2024-01-15}
\begin{document}\end{document}|})
        (tag ^ ": date without hash"));
  run "META-002 fires: date with text only" (fun tag ->
      expect
        (fires "META-002"
           {|\documentclass{article}
\date{January 2024}
\begin{document}\end{document}|})
        (tag ^ ": date text no hash"));
  run "META-002 clean: date with hash" (fun tag ->
      expect
        (does_not_fire "META-002"
           {|\documentclass{article}
\date{2024-01-15 abc1234}
\begin{document}\end{document}|})
        (tag ^ ": date with hash ok"));
  run "META-002 clean: no date command" (fun tag ->
      expect
        (does_not_fire "META-002"
           {|\documentclass{article}
\begin{document}\end{document}|})
        (tag ^ ": no date"));
  run "META-002 clean: empty preamble" (fun tag ->
      expect (does_not_fire "META-002" {|Hello world.|}) (tag ^ ": no preamble"));

  (* ══════════════════════════════════════════════════════════════════════
     RTL-005: Polyglossia RTL font not specified
     ══════════════════════════════════════════════════════════════════════ *)
  run "RTL-005 fires: polyglossia + arabic, no font" (fun tag ->
      expect
        (fires "RTL-005"
           {|\documentclass{article}
\usepackage{polyglossia}
\setdefaultlanguage{arabic}
\begin{document}\end{document}|})
        (tag ^ ": arabic without font spec"));
  run "RTL-005 fires: polyglossia + hebrew, no font" (fun tag ->
      expect
        (fires "RTL-005"
           {|\documentclass{article}
\usepackage{polyglossia}
\setdefaultlanguage{hebrew}
\begin{document}\end{document}|})
        (tag ^ ": hebrew without font spec"));
  run "RTL-005 fires: polyglossia + persian, no font" (fun tag ->
      expect
        (fires "RTL-005"
           {|\documentclass{article}
\usepackage{polyglossia}
\setdefaultlanguage{persian}
\begin{document}\end{document}|})
        (tag ^ ": persian without font spec"));
  run "RTL-005 clean: polyglossia + arabic + newfontfamily" (fun tag ->
      expect
        (does_not_fire "RTL-005"
           {|\documentclass{article}
\usepackage{polyglossia}
\setdefaultlanguage{arabic}
\newfontfamily\arabicfont{Amiri}
\begin{document}\end{document}|})
        (tag ^ ": newfontfamily present"));
  run "RTL-005 clean: polyglossia + arabic + setmainfont" (fun tag ->
      expect
        (does_not_fire "RTL-005"
           {|\documentclass{article}
\usepackage{polyglossia}
\setdefaultlanguage{arabic}
\setmainfont{Amiri}
\begin{document}\end{document}|})
        (tag ^ ": setmainfont present"));
  run "RTL-005 clean: polyglossia without RTL language" (fun tag ->
      expect
        (does_not_fire "RTL-005"
           {|\documentclass{article}
\usepackage{polyglossia}
\setdefaultlanguage{english}
\begin{document}\end{document}|})
        (tag ^ ": no RTL language"));
  run "RTL-005 clean: no polyglossia" (fun tag ->
      expect
        (does_not_fire "RTL-005"
           {|\documentclass{article}
\usepackage[arabic]{babel}
\begin{document}\end{document}|})
        (tag ^ ": no polyglossia"));

  (* ══════════════════════════════════════════════════════════════════════
     Summary
     ══════════════════════════════════════════════════════════════════════ *)
  if !fails > 0 then (
    Printf.eprintf "[l5-expl3-tikz] %d failure(s) in %d cases\n%!" !fails !cases;
    exit 1)
  else Printf.printf "[l5-expl3-tikz] PASS %d cases\n%!" !cases
