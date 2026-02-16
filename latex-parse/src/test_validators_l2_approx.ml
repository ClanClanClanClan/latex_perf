(** Unit tests for L2-approximable rules (FIG, TAB, PKG, CJK). Comprehensive
    edge-case coverage including starred variants, package-with-options, count
    accuracy, and boundary conditions. *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[l2-approx] FAIL: %s\n%!" msg;
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
  Unix.putenv "L0_VALIDATORS" "pilot";

  (* ══════════════════════════════════════════════════════════════════════
     FIG-001: Figure without caption
     ══════════════════════════════════════════════════════════════════════ *)
  run "FIG-001 fires when figure has no caption" (fun tag ->
      expect
        (fires "FIG-001"
           "\\begin{figure}\n\
            \\includegraphics{img.png}\n\
            \\label{fig:x}\n\
            \\end{figure}")
        (tag ^ ": no caption"));
  run "FIG-001 clean with caption" (fun tag ->
      expect
        (does_not_fire "FIG-001"
           "\\begin{figure}\n\
            \\includegraphics{img.png}\n\
            \\caption{A fig}\n\
            \\label{fig:x}\n\
            \\end{figure}")
        (tag ^ ": has caption"));
  run "FIG-001 count=2" (fun tag ->
      expect
        (fires_with_count "FIG-001"
           "\\begin{figure}\n\
            \\includegraphics{a.png}\n\
            \\end{figure}\n\
            \\begin{figure}\n\
            \\includegraphics{b.png}\n\
            \\end{figure}"
           2)
        (tag ^ ": two figures no caption"));
  run "FIG-001 clean no figure" (fun tag ->
      expect
        (does_not_fire "FIG-001" "\\includegraphics{img.png}")
        (tag ^ ": no figure env"));
  (* Starred variant *)
  run "FIG-001 fires on figure* without caption" (fun tag ->
      expect
        (fires "FIG-001"
           "\\begin{figure*}\n\\includegraphics{img.png}\n\\end{figure*}")
        (tag ^ ": figure* no caption"));
  run "FIG-001 clean figure* with caption" (fun tag ->
      expect
        (does_not_fire "FIG-001"
           "\\begin{figure*}\n\
            \\includegraphics{img.png}\n\
            \\caption{Wide fig}\n\
            \\end{figure*}")
        (tag ^ ": figure* has caption"));
  (* captionsetup should not count as a real caption *)
  run "FIG-001 fires when only captionsetup present" (fun tag ->
      expect
        (fires "FIG-001"
           "\\begin{figure}\n\
            \\captionsetup{font=small}\n\
            \\includegraphics{img.png}\n\
            \\end{figure}")
        (tag ^ ": captionsetup is not caption"));
  (* Mixed: one with caption, one without *)
  run "FIG-001 count=1 mixed" (fun tag ->
      expect
        (fires_with_count "FIG-001"
           "\\begin{figure}\n\
            \\caption{Has one}\n\
            \\end{figure}\n\
            \\begin{figure}\n\
            \\includegraphics{b.png}\n\
            \\end{figure}"
           1)
        (tag ^ ": one with, one without"));
  (* Empty figure *)
  run "FIG-001 fires on empty figure" (fun tag ->
      expect
        (fires "FIG-001" "\\begin{figure}\\end{figure}")
        (tag ^ ": empty figure"));
  (* Empty string *)
  run "FIG-001 clean empty string" (fun tag ->
      expect (does_not_fire "FIG-001" "") (tag ^ ": empty string"));
  (* caption with optional arg *)
  run "FIG-001 clean with caption[short]" (fun tag ->
      expect
        (does_not_fire "FIG-001"
           "\\begin{figure}\n\\caption[Short]{Long caption}\n\\end{figure}")
        (tag ^ ": caption with optional arg"));

  (* ══════════════════════════════════════════════════════════════════════
     FIG-002: Figure without label
     ══════════════════════════════════════════════════════════════════════ *)
  run "FIG-002 fires when figure has no label" (fun tag ->
      expect
        (fires "FIG-002"
           "\\begin{figure}\n\
            \\includegraphics{img.png}\n\
            \\caption{A fig}\n\
            \\end{figure}")
        (tag ^ ": no label"));
  run "FIG-002 clean with label" (fun tag ->
      expect
        (does_not_fire "FIG-002"
           "\\begin{figure}\n\
            \\includegraphics{img.png}\n\
            \\caption{A fig}\n\
            \\label{fig:x}\n\
            \\end{figure}")
        (tag ^ ": has label"));
  run "FIG-002 clean no figure" (fun tag ->
      expect (does_not_fire "FIG-002" "plain text") (tag ^ ": no figure"));
  (* Starred variant *)
  run "FIG-002 fires on figure* without label" (fun tag ->
      expect
        (fires "FIG-002" "\\begin{figure*}\n\\caption{Wide}\n\\end{figure*}")
        (tag ^ ": figure* no label"));
  (* Count accuracy *)
  run "FIG-002 count=2" (fun tag ->
      expect
        (fires_with_count "FIG-002"
           "\\begin{figure}\n\
            \\caption{A}\n\
            \\end{figure}\n\
            \\begin{figure*}\n\
            \\caption{B}\n\
            \\end{figure*}"
           2)
        (tag ^ ": two figures no label"));
  (* Empty string *)
  run "FIG-002 clean empty string" (fun tag ->
      expect (does_not_fire "FIG-002" "") (tag ^ ": empty string"));

  (* ══════════════════════════════════════════════════════════════════════
     FIG-003: Label before caption in figure
     ══════════════════════════════════════════════════════════════════════ *)
  run "FIG-003 fires when label before caption" (fun tag ->
      expect
        (fires "FIG-003"
           "\\begin{figure}\n\
            \\includegraphics{img.png}\n\
            \\label{fig:x}\n\
            \\caption{A fig}\n\
            \\end{figure}")
        (tag ^ ": label before caption"));
  run "FIG-003 clean caption before label" (fun tag ->
      expect
        (does_not_fire "FIG-003"
           "\\begin{figure}\n\
            \\includegraphics{img.png}\n\
            \\caption{A fig}\n\
            \\label{fig:x}\n\
            \\end{figure}")
        (tag ^ ": caption before label"));
  run "FIG-003 clean no label" (fun tag ->
      expect
        (does_not_fire "FIG-003"
           "\\begin{figure}\n\
            \\includegraphics{img.png}\n\
            \\caption{A fig}\n\
            \\end{figure}")
        (tag ^ ": no label"));
  (* Starred variant *)
  run "FIG-003 fires on figure* with label before caption" (fun tag ->
      expect
        (fires "FIG-003"
           "\\begin{figure*}\n\\label{fig:x}\n\\caption{A fig}\n\\end{figure*}")
        (tag ^ ": figure* label before caption"));
  (* Label but no caption: should not fire *)
  run "FIG-003 clean label but no caption" (fun tag ->
      expect
        (does_not_fire "FIG-003"
           "\\begin{figure}\n\\label{fig:x}\n\\end{figure}")
        (tag ^ ": label but no caption"));
  (* Count accuracy *)
  run "FIG-003 count=2" (fun tag ->
      expect
        (fires_with_count "FIG-003"
           "\\begin{figure}\n\
            \\label{fig:a}\n\
            \\caption{A}\n\
            \\end{figure}\n\
            \\begin{figure}\n\
            \\label{fig:b}\n\
            \\caption{B}\n\
            \\end{figure}"
           2)
        (tag ^ ": two bad figures"));
  (* Empty string *)
  run "FIG-003 clean empty string" (fun tag ->
      expect (does_not_fire "FIG-003" "") (tag ^ ": empty string"));

  (* ══════════════════════════════════════════════════════════════════════
     FIG-007: Figure lacks alt text for accessibility
     ══════════════════════════════════════════════════════════════════════ *)
  run "FIG-007 fires when includegraphics lacks alt" (fun tag ->
      expect
        (fires "FIG-007"
           "\\begin{figure}\n\
            \\includegraphics[width=0.5\\textwidth]{img.png}\n\
            \\end{figure}")
        (tag ^ ": no alt="));
  run "FIG-007 fires when no options at all" (fun tag ->
      expect
        (fires "FIG-007"
           "\\begin{figure}\n\\includegraphics{img.png}\n\\end{figure}")
        (tag ^ ": no options"));
  run "FIG-007 clean with alt" (fun tag ->
      expect
        (does_not_fire "FIG-007"
           "\\begin{figure}\n\
            \\includegraphics[alt={A description}]{img.png}\n\
            \\end{figure}")
        (tag ^ ": has alt="));
  run "FIG-007 clean no figure" (fun tag ->
      expect
        (does_not_fire "FIG-007" "\\includegraphics{img.png}")
        (tag ^ ": outside figure"));
  (* Starred variant *)
  run "FIG-007 fires on figure* without alt" (fun tag ->
      expect
        (fires "FIG-007"
           "\\begin{figure*}\n\\includegraphics{img.png}\n\\end{figure*}")
        (tag ^ ": figure* no alt"));
  (* Multiple includegraphics: one with alt, one without *)
  run "FIG-007 count=1 mixed" (fun tag ->
      expect
        (fires_with_count "FIG-007"
           "\\begin{figure}\n\
            \\includegraphics[alt={Good}]{a.png}\n\
            \\includegraphics{b.png}\n\
            \\end{figure}"
           1)
        (tag ^ ": one with alt, one without"));
  (* Empty string *)
  run "FIG-007 clean empty string" (fun tag ->
      expect (does_not_fire "FIG-007" "") (tag ^ ": empty string"));

  (* ══════════════════════════════════════════════════════════════════════
     FIG-009: Float position specifier ! used excessively
     ══════════════════════════════════════════════════════════════════════ *)
  run "FIG-009 fires on figure with !" (fun tag ->
      expect
        (fires "FIG-009"
           "\\begin{figure}[!ht]\n\\includegraphics{img.png}\n\\end{figure}")
        (tag ^ ": figure [!ht]"));
  run "FIG-009 fires on table with !" (fun tag ->
      expect
        (fires "FIG-009"
           "\\begin{table}[!t]\n\
            \\begin{tabular}{c}x\\end{tabular}\n\
            \\end{table}")
        (tag ^ ": table [!t]"));
  run "FIG-009 clean without !" (fun tag ->
      expect
        (does_not_fire "FIG-009"
           "\\begin{figure}[ht]\n\\includegraphics{img.png}\n\\end{figure}")
        (tag ^ ": figure [ht] ok"));
  run "FIG-009 clean no options" (fun tag ->
      expect
        (does_not_fire "FIG-009"
           "\\begin{figure}\n\\includegraphics{img.png}\n\\end{figure}")
        (tag ^ ": no options ok"));
  (* Starred variants *)
  run "FIG-009 fires on figure* with !" (fun tag ->
      expect
        (fires "FIG-009"
           "\\begin{figure*}[!htbp]\n\\includegraphics{img.png}\n\\end{figure*}")
        (tag ^ ": figure* [!htbp]"));
  run "FIG-009 fires on table* with !" (fun tag ->
      expect
        (fires "FIG-009"
           "\\begin{table*}[!p]\n\
            \\begin{tabular}{c}x\\end{tabular}\n\
            \\end{table*}")
        (tag ^ ": table* [!p]"));
  (* Count accuracy *)
  run "FIG-009 count=2" (fun tag ->
      expect
        (fires_with_count "FIG-009"
           "\\begin{figure}[!h]\n\
            x\n\
            \\end{figure}\n\
            \\begin{table}[!t]\n\
            y\n\
            \\end{table}"
           2)
        (tag ^ ": figure + table with !"));
  (* Empty string *)
  run "FIG-009 clean empty string" (fun tag ->
      expect (does_not_fire "FIG-009" "") (tag ^ ": empty string"));

  (* ══════════════════════════════════════════════════════════════════════
     TAB-001: Table lacks caption
     ══════════════════════════════════════════════════════════════════════ *)
  run "TAB-001 fires when table has no caption" (fun tag ->
      expect
        (fires "TAB-001"
           "\\begin{table}\n\
            \\begin{tabular}{cc}\n\
            a & b\n\
            \\end{tabular}\n\
            \\end{table}")
        (tag ^ ": no caption"));
  run "TAB-001 clean with caption" (fun tag ->
      expect
        (does_not_fire "TAB-001"
           "\\begin{table}\n\
            \\caption{A table}\n\
            \\begin{tabular}{cc}\n\
            a & b\n\
            \\end{tabular}\n\
            \\end{table}")
        (tag ^ ": has caption"));
  run "TAB-001 clean no table env" (fun tag ->
      expect
        (does_not_fire "TAB-001" "\\begin{tabular}{cc}\na & b\n\\end{tabular}")
        (tag ^ ": no table env"));
  (* Starred variant *)
  run "TAB-001 fires on table* without caption" (fun tag ->
      expect
        (fires "TAB-001"
           "\\begin{table*}\n\
            \\begin{tabular}{cc}\n\
            a & b\n\
            \\end{tabular}\n\
            \\end{table*}")
        (tag ^ ": table* no caption"));
  run "TAB-001 clean table* with caption" (fun tag ->
      expect
        (does_not_fire "TAB-001"
           "\\begin{table*}\n\
            \\caption{Wide table}\n\
            \\begin{tabular}{cc}\n\
            a & b\n\
            \\end{tabular}\n\
            \\end{table*}")
        (tag ^ ": table* has caption"));
  (* captionsetup should not count as caption *)
  run "TAB-001 fires when only captionsetup" (fun tag ->
      expect
        (fires "TAB-001"
           "\\begin{table}\n\
            \\captionsetup{justification=centering}\n\
            \\begin{tabular}{cc}\n\
            a & b\n\
            \\end{tabular}\n\
            \\end{table}")
        (tag ^ ": captionsetup is not caption"));
  (* Count accuracy *)
  run "TAB-001 count=2" (fun tag ->
      expect
        (fires_with_count "TAB-001"
           "\\begin{table}\n\
            \\begin{tabular}{c}x\\end{tabular}\n\
            \\end{table}\n\
            \\begin{table}\n\
            \\begin{tabular}{c}y\\end{tabular}\n\
            \\end{table}"
           2)
        (tag ^ ": two tables no caption"));
  (* Empty string *)
  run "TAB-001 clean empty string" (fun tag ->
      expect (does_not_fire "TAB-001" "") (tag ^ ": empty string"));

  (* ══════════════════════════════════════════════════════════════════════
     TAB-002: Caption below table (journal requires above)
     ══════════════════════════════════════════════════════════════════════ *)
  run "TAB-002 fires on caption below tabular" (fun tag ->
      expect
        (fires "TAB-002"
           "\\begin{table}\n\
            \\begin{tabular}{cc}\n\
            a & b\n\
            \\end{tabular}\n\
            \\caption{A table}\n\
            \\end{table}")
        (tag ^ ": caption below"));
  run "TAB-002 clean caption above" (fun tag ->
      expect
        (does_not_fire "TAB-002"
           "\\begin{table}\n\
            \\caption{A table}\n\
            \\begin{tabular}{cc}\n\
            a & b\n\
            \\end{tabular}\n\
            \\end{table}")
        (tag ^ ": caption above"));
  run "TAB-002 clean no caption" (fun tag ->
      expect
        (does_not_fire "TAB-002"
           "\\begin{table}\n\
            \\begin{tabular}{cc}\n\
            a & b\n\
            \\end{tabular}\n\
            \\end{table}")
        (tag ^ ": no caption"));
  (* Starred variant: table* *)
  run "TAB-002 fires on table* caption below" (fun tag ->
      expect
        (fires "TAB-002"
           "\\begin{table*}\n\
            \\begin{tabular}{cc}\n\
            a & b\n\
            \\end{tabular}\n\
            \\caption{Wide table}\n\
            \\end{table*}")
        (tag ^ ": table* caption below"));
  (* tabular* variant *)
  run "TAB-002 fires on caption below tabular*" (fun tag ->
      expect
        (fires "TAB-002"
           "\\begin{table}\n\
            \\begin{tabular*}{\\textwidth}{cc}\n\
            a & b\n\
            \\end{tabular*}\n\
            \\caption{A table}\n\
            \\end{table}")
        (tag ^ ": tabular* caption below"));
  (* No tabular at all *)
  run "TAB-002 clean no tabular" (fun tag ->
      expect
        (does_not_fire "TAB-002"
           "\\begin{table}\n\\caption{A table}\nSome text\n\\end{table}")
        (tag ^ ": no tabular in table"));
  (* Count accuracy *)
  run "TAB-002 count=2" (fun tag ->
      expect
        (fires_with_count "TAB-002"
           "\\begin{table}\n\
            \\begin{tabular}{c}x\\end{tabular}\n\
            \\caption{A}\n\
            \\end{table}\n\
            \\begin{table}\n\
            \\begin{tabular}{c}y\\end{tabular}\n\
            \\caption{B}\n\
            \\end{table}"
           2)
        (tag ^ ": two tables caption below"));
  (* Empty string *)
  run "TAB-002 clean empty string" (fun tag ->
      expect (does_not_fire "TAB-002" "") (tag ^ ": empty string"));

  (* ══════════════════════════════════════════════════════════════════════
     TAB-005: Vertical rules present in tabular
     ══════════════════════════════════════════════════════════════════════ *)
  run "TAB-005 fires on vertical rules" (fun tag ->
      expect
        (fires "TAB-005" "\\begin{tabular}{|c|c|}\na & b\n\\end{tabular}")
        (tag ^ ": has | in col spec"));
  run "TAB-005 count=2" (fun tag ->
      expect
        (fires_with_count "TAB-005"
           "\\begin{tabular}{|c|}\n\
            x\\end{tabular}\n\
            \\begin{tabular}{l|r}\n\
            y\\end{tabular}"
           2)
        (tag ^ ": two tabulars"));
  run "TAB-005 clean no pipes" (fun tag ->
      expect
        (does_not_fire "TAB-005"
           "\\begin{tabular}{ccc}\na & b & c\n\\end{tabular}")
        (tag ^ ": no pipes"));
  run "TAB-005 clean no tabular" (fun tag ->
      expect (does_not_fire "TAB-005" "plain text") (tag ^ ": no tabular"));
  (* tabular* variant: pipe in colspec (second braces), not width (first) *)
  run "TAB-005 fires on tabular* with pipes in colspec" (fun tag ->
      expect
        (fires "TAB-005"
           "\\begin{tabular*}{\\textwidth}{|c|c|}\na & b\n\\end{tabular*}")
        (tag ^ ": tabular* pipe in colspec"));
  (* tabular*: no pipe in colspec, but | in width arg — should NOT fire *)
  run "TAB-005 clean tabular* pipe only in width" (fun tag ->
      expect
        (does_not_fire "TAB-005"
           "\\begin{tabular*}{0.5|\\textwidth}{cc}\na & b\n\\end{tabular*}")
        (tag ^ ": tabular* pipe in width only"));
  (* Nested braces in colspec *)
  run "TAB-005 fires on pipes with nested braces" (fun tag ->
      expect
        (fires "TAB-005" "\\begin{tabular}{>{$}c<{$}|r}\na & b\n\\end{tabular}")
        (tag ^ ": pipe with nested braces"));
  (* Empty colspec *)
  run "TAB-005 clean empty colspec" (fun tag ->
      expect
        (does_not_fire "TAB-005" "\\begin{tabular}{}\n\\end{tabular}")
        (tag ^ ": empty colspec"));
  (* Empty string *)
  run "TAB-005 clean empty string" (fun tag ->
      expect (does_not_fire "TAB-005" "") (tag ^ ": empty string"));

  (* ══════════════════════════════════════════════════════════════════════
     PKG-001: Package duplicate inclusion detected
     ══════════════════════════════════════════════════════════════════════ *)
  run "PKG-001 fires on duplicate package" (fun tag ->
      expect
        (fires "PKG-001"
           "\\usepackage{amsmath}\n\
            \\usepackage{graphicx}\n\
            \\usepackage{amsmath}\n\
            \\begin{document}\n\
            \\end{document}")
        (tag ^ ": amsmath duplicated"));
  run "PKG-001 count=2" (fun tag ->
      expect
        (fires_with_count "PKG-001"
           "\\usepackage{amsmath}\n\
            \\usepackage{amsmath}\n\
            \\usepackage{amsmath}\n\
            \\begin{document}\n\
            \\end{document}"
           2)
        (tag ^ ": amsmath 3x = count 2"));
  run "PKG-001 clean no duplicates" (fun tag ->
      expect
        (does_not_fire "PKG-001"
           "\\usepackage{amsmath}\n\
            \\usepackage{graphicx}\n\
            \\begin{document}\n\
            \\end{document}")
        (tag ^ ": no dups"));
  run "PKG-001 clean with options" (fun tag ->
      expect
        (does_not_fire "PKG-001"
           "\\usepackage[utf8]{inputenc}\n\
            \\usepackage{amsmath}\n\
            \\begin{document}\n\
            \\end{document}")
        (tag ^ ": different packages with options"));
  (* Comma-separated packages with duplicate *)
  run "PKG-001 fires on comma-separated duplicate" (fun tag ->
      expect
        (fires "PKG-001"
           "\\usepackage{amsmath,graphicx}\n\
            \\usepackage{amsmath}\n\
            \\begin{document}\n\
            \\end{document}")
        (tag ^ ": comma-separated dup"));
  (* Same package different options *)
  run "PKG-001 fires same pkg different options" (fun tag ->
      expect
        (fires "PKG-001"
           "\\usepackage[utf8]{inputenc}\n\
            \\usepackage[latin1]{inputenc}\n\
            \\begin{document}\n\
            \\end{document}")
        (tag ^ ": same pkg different opts"));
  (* Empty string *)
  run "PKG-001 clean empty string" (fun tag ->
      expect (does_not_fire "PKG-001" "") (tag ^ ": empty string"));

  (* ══════════════════════════════════════════════════════════════════════
     PKG-002: geometry loaded after hyperref — must precede
     ══════════════════════════════════════════════════════════════════════ *)
  run "PKG-002 fires when geometry after hyperref" (fun tag ->
      expect
        (fires "PKG-002"
           "\\usepackage{hyperref}\n\
            \\usepackage{geometry}\n\
            \\begin{document}\n\
            \\end{document}")
        (tag ^ ": geometry after hyperref"));
  run "PKG-002 clean geometry before hyperref" (fun tag ->
      expect
        (does_not_fire "PKG-002"
           "\\usepackage{geometry}\n\
            \\usepackage{hyperref}\n\
            \\begin{document}\n\
            \\end{document}")
        (tag ^ ": correct order"));
  run "PKG-002 clean no hyperref" (fun tag ->
      expect
        (does_not_fire "PKG-002"
           "\\usepackage{geometry}\n\\begin{document}\n\\end{document}")
        (tag ^ ": no hyperref"));
  run "PKG-002 clean no geometry" (fun tag ->
      expect
        (does_not_fire "PKG-002"
           "\\usepackage{hyperref}\n\\begin{document}\n\\end{document}")
        (tag ^ ": no geometry"));
  (* With options *)
  run "PKG-002 fires with options" (fun tag ->
      expect
        (fires "PKG-002"
           "\\usepackage[colorlinks]{hyperref}\n\
            \\usepackage[margin=1in]{geometry}\n\
            \\begin{document}\n\
            \\end{document}")
        (tag ^ ": both with options, wrong order"));
  (* Empty string *)
  run "PKG-002 clean empty string" (fun tag ->
      expect (does_not_fire "PKG-002" "") (tag ^ ": empty string"));

  (* ══════════════════════════════════════════════════════════════════════
     PKG-004: Package loaded after \begin{document}
     ══════════════════════════════════════════════════════════════════════ *)
  run "PKG-004 fires on usepackage in body" (fun tag ->
      expect
        (fires "PKG-004"
           "\\usepackage{amsmath}\n\
            \\begin{document}\n\
            \\usepackage{graphicx}\n\
            \\end{document}")
        (tag ^ ": usepackage in body"));
  run "PKG-004 count=2" (fun tag ->
      expect
        (fires_with_count "PKG-004"
           "\\begin{document}\n\
            \\usepackage{a}\n\
            \\usepackage{b}\n\
            \\end{document}"
           2)
        (tag ^ ": two packages in body"));
  run "PKG-004 clean all in preamble" (fun tag ->
      expect
        (does_not_fire "PKG-004"
           "\\usepackage{amsmath}\n\
            \\usepackage{graphicx}\n\
            \\begin{document}\n\
            hello\n\
            \\end{document}")
        (tag ^ ": all in preamble"));
  run "PKG-004 clean no document env" (fun tag ->
      expect
        (does_not_fire "PKG-004" "\\usepackage{amsmath}\nhello world")
        (tag ^ ": no document env"));
  (* Usepackage with options in body *)
  run "PKG-004 fires on usepackage with options in body" (fun tag ->
      expect
        (fires "PKG-004"
           "\\begin{document}\n\\usepackage[utf8]{inputenc}\n\\end{document}")
        (tag ^ ": usepackage with options in body"));
  (* Empty string *)
  run "PKG-004 clean empty string" (fun tag ->
      expect (does_not_fire "PKG-004" "") (tag ^ ": empty string"));

  (* ══════════════════════════════════════════════════════════════════════
     PKG-005: Unknown option for geometry
     ══════════════════════════════════════════════════════════════════════ *)
  run "PKG-005 fires on unknown option" (fun tag ->
      expect
        (fires "PKG-005" "\\usepackage[margin=1in, foobar]{geometry}")
        (tag ^ ": foobar unknown"));
  run "PKG-005 count=2" (fun tag ->
      expect
        (fires_with_count "PKG-005" "\\usepackage[xyz=1, abc]{geometry}" 2)
        (tag ^ ": two unknown options"));
  run "PKG-005 clean known options" (fun tag ->
      expect
        (does_not_fire "PKG-005"
           "\\usepackage[margin=1in, top=2cm, left=3cm]{geometry}")
        (tag ^ ": all known"));
  run "PKG-005 clean no geometry" (fun tag ->
      expect
        (does_not_fire "PKG-005" "\\usepackage{amsmath}")
        (tag ^ ": no geometry"));
  (* Boolean option (no =) that is known *)
  run "PKG-005 clean boolean known option" (fun tag ->
      expect
        (does_not_fire "PKG-005" "\\usepackage[landscape, showframe]{geometry}")
        (tag ^ ": boolean known options"));
  (* Empty options *)
  run "PKG-005 clean empty options" (fun tag ->
      expect
        (does_not_fire "PKG-005" "\\usepackage[]{geometry}")
        (tag ^ ": empty options"));
  (* Whitespace around option keys *)
  run "PKG-005 clean whitespace in options" (fun tag ->
      expect
        (does_not_fire "PKG-005"
           "\\usepackage[ margin = 1in , top = 2cm ]{geometry}")
        (tag ^ ": whitespace in options"));
  (* Empty string *)
  run "PKG-005 clean empty string" (fun tag ->
      expect (does_not_fire "PKG-005" "") (tag ^ ": empty string"));

  (* ══════════════════════════════════════════════════════════════════════
     CJK-004: xeCJK package missing when CJK glyphs present
     ══════════════════════════════════════════════════════════════════════ *)
  run "CJK-004 fires on CJK without package" (fun tag ->
      expect
        (fires "CJK-004"
           "\\documentclass{article}\n\
            \\begin{document}\n\
            \xe4\xb8\xad\xe6\x96\x87\n\
            \\end{document}")
        (tag ^ ": CJK without xeCJK"));
  run "CJK-004 clean with xeCJK" (fun tag ->
      expect
        (does_not_fire "CJK-004"
           "\\usepackage{xeCJK}\n\
            \\begin{document}\n\
            \xe4\xb8\xad\xe6\x96\x87\n\
            \\end{document}")
        (tag ^ ": has xeCJK"));
  run "CJK-004 clean with ctex" (fun tag ->
      expect
        (does_not_fire "CJK-004"
           "\\usepackage{ctex}\n\
            \\begin{document}\n\
            \xe4\xb8\xad\xe6\x96\x87\n\
            \\end{document}")
        (tag ^ ": has ctex"));
  run "CJK-004 clean no CJK" (fun tag ->
      expect
        (does_not_fire "CJK-004"
           "\\documentclass{article}\n\\begin{document}\nhello\n\\end{document}")
        (tag ^ ": no CJK glyphs"));
  (* Package with options — fixed bug *)
  run "CJK-004 clean with xeCJK with options" (fun tag ->
      expect
        (does_not_fire "CJK-004"
           "\\usepackage[AutoFakeBold]{xeCJK}\n\
            \\begin{document}\n\
            \xe4\xb8\xad\xe6\x96\x87\n\
            \\end{document}")
        (tag ^ ": xeCJK with options"));
  run "CJK-004 clean with CJKutf8" (fun tag ->
      expect
        (does_not_fire "CJK-004"
           "\\usepackage{CJKutf8}\n\
            \\begin{document}\n\
            \xe4\xb8\xad\xe6\x96\x87\n\
            \\end{document}")
        (tag ^ ": has CJKutf8"));
  (* Empty string *)
  run "CJK-004 clean empty string" (fun tag ->
      expect (does_not_fire "CJK-004" "") (tag ^ ": empty string"));

  (* ══════════════════════════════════════════════════════════════════════
     CJK-006: Ruby annotation requires ruby package
     ══════════════════════════════════════════════════════════════════════ *)
  run "CJK-006 fires on ruby without package" (fun tag ->
      expect
        (fires "CJK-006" "\\ruby{\xe6\xbc\xa2}{\xe3\x81\x8b\xe3\x82\x93}")
        (tag ^ ": ruby without package"));
  run "CJK-006 count=2" (fun tag ->
      expect
        (fires_with_count "CJK-006" "\\ruby{a}{b} and \\ruby{c}{d}" 2)
        (tag ^ ": two ruby calls"));
  run "CJK-006 clean with package" (fun tag ->
      expect
        (does_not_fire "CJK-006"
           "\\usepackage{ruby}\n\\ruby{\xe6\xbc\xa2}{\xe3\x81\x8b\xe3\x82\x93}")
        (tag ^ ": has ruby package"));
  run "CJK-006 clean with pxrubrica" (fun tag ->
      expect
        (does_not_fire "CJK-006" "\\usepackage{pxrubrica}\n\\ruby{a}{b}")
        (tag ^ ": has pxrubrica"));
  run "CJK-006 clean no ruby" (fun tag ->
      expect (does_not_fire "CJK-006" "plain text") (tag ^ ": no ruby"));
  (* Package with options — fixed bug *)
  run "CJK-006 clean with ruby package with options" (fun tag ->
      expect
        (does_not_fire "CJK-006"
           "\\usepackage[encoding=utf8]{ruby}\n\\ruby{a}{b}")
        (tag ^ ": ruby package with options"));
  run "CJK-006 clean with luatexja-ruby" (fun tag ->
      expect
        (does_not_fire "CJK-006" "\\usepackage{luatexja-ruby}\n\\ruby{a}{b}")
        (tag ^ ": has luatexja-ruby"));
  (* Empty string *)
  run "CJK-006 clean empty string" (fun tag ->
      expect (does_not_fire "CJK-006" "") (tag ^ ": empty string"));

  (* ─── summary ─────────────────────────────────────────────────────── *)
  Printf.printf "[l2-approx] PASS %d cases\n%!" !cases;
  if !fails > 0 then (
    Printf.eprintf "[l2-approx] %d FAILURES\n%!" !fails;
    exit 1)
