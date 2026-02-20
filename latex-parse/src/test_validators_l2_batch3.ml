(** Unit tests for L2-approximable batch 3 rules (CMD, DOC, TAB, PKG, LANG,
    TIKZ, FIG). *)

open Test_helpers

let () =
  Unix.putenv "L0_VALIDATORS" "pilot";

  (* ══════════════════════════════════════════════════════════════════════
     CMD-014: \AtBeginDocument placed after \begin{document}
     ══════════════════════════════════════════════════════════════════════ *)
  run "CMD-014 fires when AtBeginDocument after begin{document}" (fun tag ->
      expect
        (fires "CMD-014" "\\begin{document}\n\\AtBeginDocument{\\color{red}}")
        (tag ^ ": after doc"));
  run "CMD-014 clean when AtBeginDocument before begin{document}" (fun tag ->
      expect
        (does_not_fire "CMD-014"
           "\\AtBeginDocument{\\color{red}}\n\\begin{document}")
        (tag ^ ": before doc"));
  run "CMD-014 clean without begin{document}" (fun tag ->
      expect
        (does_not_fire "CMD-014" "\\AtBeginDocument{\\color{red}}")
        (tag ^ ": no document"));
  run "CMD-014 clean empty" (fun tag ->
      expect (does_not_fire "CMD-014" "") (tag ^ ": empty"));

  (* ══════════════════════════════════════════════════════════════════════
     DOC-001: Title missing \maketitle (requires article-like class)
     ══════════════════════════════════════════════════════════════════════ *)
  run "DOC-001 fires when no maketitle" (fun tag ->
      expect
        (fires "DOC-001"
           "\\documentclass{article}\n\\begin{document}\nHello\n\\end{document}")
        (tag ^ ": no maketitle"));
  run "DOC-001 clean with maketitle" (fun tag ->
      expect
        (does_not_fire "DOC-001"
           "\\documentclass{article}\n\
            \\begin{document}\n\
            \\maketitle\n\
            \\end{document}")
        (tag ^ ": has maketitle"));
  run "DOC-001 clean without document" (fun tag ->
      expect (does_not_fire "DOC-001" "just text") (tag ^ ": no document"));
  run "DOC-001 clean empty" (fun tag ->
      expect (does_not_fire "DOC-001" "") (tag ^ ": empty"));

  (* ══════════════════════════════════════════════════════════════════════
     DOC-002: Abstract environment missing (requires article-like class)
     ══════════════════════════════════════════════════════════════════════ *)
  run "DOC-002 fires when no abstract" (fun tag ->
      expect
        (fires "DOC-002"
           "\\documentclass{article}\n\\begin{document}\nHello\n\\end{document}")
        (tag ^ ": no abstract"));
  run "DOC-002 clean with abstract" (fun tag ->
      expect
        (does_not_fire "DOC-002"
           "\\documentclass{article}\n\
            \\begin{document}\n\
            \\begin{abstract}\n\
            Text\n\
            \\end{abstract}\n\
            \\end{document}")
        (tag ^ ": has abstract"));
  run "DOC-002 clean without document" (fun tag ->
      expect (does_not_fire "DOC-002" "just text") (tag ^ ": no document"));
  run "DOC-002 clean empty" (fun tag ->
      expect (does_not_fire "DOC-002" "") (tag ^ ": empty"));

  (* ══════════════════════════════════════════════════════════════════════
     DOC-003: Keywords missing (requires article-like class)
     ══════════════════════════════════════════════════════════════════════ *)
  run "DOC-003 fires when no keywords" (fun tag ->
      expect
        (fires "DOC-003"
           "\\documentclass{article}\n\\begin{document}\nHello\n\\end{document}")
        (tag ^ ": no keywords"));
  run "DOC-003 clean with keywords" (fun tag ->
      expect
        (does_not_fire "DOC-003"
           "\\documentclass{article}\n\
            \\begin{document}\n\
            \\keywords{foo, bar}\n\
            \\end{document}")
        (tag ^ ": has keywords"));
  run "DOC-003 clean without document" (fun tag ->
      expect (does_not_fire "DOC-003" "just text") (tag ^ ": no document"));
  run "DOC-003 clean empty" (fun tag ->
      expect (does_not_fire "DOC-003" "") (tag ^ ": empty"));

  (* ══════════════════════════════════════════════════════════════════════
     TAB-006: Consecutive \hline duplicated
     ══════════════════════════════════════════════════════════════════════ *)
  run "TAB-006 fires on consecutive hline" (fun tag ->
      expect (fires "TAB-006" "\\hline\n\\hline") (tag ^ ": consecutive hlines"));
  run "TAB-006 fires on adjacent hline" (fun tag ->
      expect (fires "TAB-006" "\\hline\\hline") (tag ^ ": adjacent hlines"));
  run "TAB-006 clean with single hline" (fun tag ->
      expect (does_not_fire "TAB-006" "\\hline") (tag ^ ": single hline"));
  run "TAB-006 clean empty" (fun tag ->
      expect (does_not_fire "TAB-006" "") (tag ^ ": empty"));

  (* ══════════════════════════════════════════════════════════════════════
     TAB-009: Floating table missing \label
     ══════════════════════════════════════════════════════════════════════ *)
  run "TAB-009 fires on table without label" (fun tag ->
      expect
        (fires "TAB-009"
           "\\begin{table}\n\
            \\caption{T}\n\
            \\begin{tabular}{c}\n\
            a\n\
            \\end{tabular}\n\
            \\end{table}")
        (tag ^ ": table no label"));
  run "TAB-009 clean with label" (fun tag ->
      expect
        (does_not_fire "TAB-009"
           "\\begin{table}\n\
            \\caption{T}\n\
            \\label{tab:x}\n\
            \\begin{tabular}{c}\n\
            a\n\
            \\end{tabular}\n\
            \\end{table}")
        (tag ^ ": table with label"));
  run "TAB-009 fires on table*" (fun tag ->
      expect
        (fires "TAB-009"
           "\\begin{table*}\n\
            \\caption{T}\n\
            \\begin{tabular}{c}\n\
            a\n\
            \\end{tabular}\n\
            \\end{table*}")
        (tag ^ ": table* no label"));
  run "TAB-009 clean empty" (fun tag ->
      expect (does_not_fire "TAB-009" "") (tag ^ ": empty"));

  (* ══════════════════════════════════════════════════════════════════════
     TAB-010: Footnote placed inside table environment
     ══════════════════════════════════════════════════════════════════════ *)
  run "TAB-010 fires on footnote in table" (fun tag ->
      expect
        (fires "TAB-010" "\\begin{table}\n\\footnote{note}\n\\end{table}")
        (tag ^ ": footnote in table"));
  run "TAB-010 clean with footnote outside table" (fun tag ->
      expect
        (does_not_fire "TAB-010"
           "text\\footnote{note}\n\\begin{table}\n\\end{table}")
        (tag ^ ": footnote outside table"));
  run "TAB-010 clean empty" (fun tag ->
      expect (does_not_fire "TAB-010" "") (tag ^ ": empty"));

  (* ══════════════════════════════════════════════════════════════════════
     TAB-011: Top/bottom \hline instead of \toprule/\bottomrule
     ══════════════════════════════════════════════════════════════════════ *)
  run "TAB-011 fires with hline in tabular" (fun tag ->
      expect
        (fires "TAB-011"
           "\\begin{tabular}{c}\n\\hline\na\n\\hline\n\\end{tabular}")
        (tag ^ ": hline in tabular"));
  run "TAB-011 clean with toprule/bottomrule" (fun tag ->
      expect
        (does_not_fire "TAB-011"
           "\\begin{tabular}{c}\n\\toprule\na\n\\bottomrule\n\\end{tabular}")
        (tag ^ ": booktabs rules"));
  run "TAB-011 clean with both hline and toprule" (fun tag ->
      expect
        (does_not_fire "TAB-011"
           "\\begin{tabular}{c}\n\
            \\toprule\n\
            a\n\
            \\hline\n\
            b\n\
            \\bottomrule\n\
            \\end{tabular}")
        (tag ^ ": mixed (has booktabs = OK)"));
  run "TAB-011 clean empty" (fun tag ->
      expect (does_not_fire "TAB-011" "") (tag ^ ": empty"));

  (* ══════════════════════════════════════════════════════════════════════
     TAB-014: Empty multicolumn alignment spec {} encountered
     ══════════════════════════════════════════════════════════════════════ *)
  run "TAB-014 fires on empty multicolumn alignment" (fun tag ->
      expect
        (fires "TAB-014" "\\multicolumn{2}{}{text}")
        (tag ^ ": empty alignment"));
  run "TAB-014 clean with alignment" (fun tag ->
      expect
        (does_not_fire "TAB-014" "\\multicolumn{2}{c}{text}")
        (tag ^ ": has alignment"));
  run "TAB-014 clean empty" (fun tag ->
      expect (does_not_fire "TAB-014" "") (tag ^ ": empty"));

  (* ══════════════════════════════════════════════════════════════════════
     PKG-007: hyperref loaded before geometry
     ══════════════════════════════════════════════════════════════════════ *)
  run "PKG-007 fires when hyperref before geometry" (fun tag ->
      expect
        (fires "PKG-007"
           "\\usepackage{hyperref}\n\\usepackage{geometry}\n\\begin{document}")
        (tag ^ ": hyperref before geometry"));
  run "PKG-007 clean when geometry before hyperref" (fun tag ->
      expect
        (does_not_fire "PKG-007"
           "\\usepackage{geometry}\n\\usepackage{hyperref}\n\\begin{document}")
        (tag ^ ": geometry first"));
  run "PKG-007 clean without both" (fun tag ->
      expect
        (does_not_fire "PKG-007" "\\usepackage{graphicx}\n\\begin{document}")
        (tag ^ ": neither pkg"));
  run "PKG-007 clean empty" (fun tag ->
      expect (does_not_fire "PKG-007" "") (tag ^ ": empty"));

  (* ══════════════════════════════════════════════════════════════════════
     PKG-009: TikZ libraries loaded inside document body
     ══════════════════════════════════════════════════════════════════════ *)
  run "PKG-009 fires when usetikzlibrary after begin{document}" (fun tag ->
      expect
        (fires "PKG-009" "\\begin{document}\n\\usetikzlibrary{calc}")
        (tag ^ ": tikzlib in body"));
  run "PKG-009 clean when usetikzlibrary before begin{document}" (fun tag ->
      expect
        (does_not_fire "PKG-009" "\\usetikzlibrary{calc}\n\\begin{document}")
        (tag ^ ": tikzlib in preamble"));
  run "PKG-009 clean empty" (fun tag ->
      expect (does_not_fire "PKG-009" "") (tag ^ ": empty"));

  (* ══════════════════════════════════════════════════════════════════════
     PKG-011: booktabs required but not loaded for \toprule
     ══════════════════════════════════════════════════════════════════════ *)
  run "PKG-011 fires when toprule without booktabs" (fun tag ->
      expect
        (fires "PKG-011" "\\begin{tabular}{c}\n\\toprule\na\n\\end{tabular}")
        (tag ^ ": toprule no booktabs"));
  run "PKG-011 fires when midrule without booktabs" (fun tag ->
      expect (fires "PKG-011" "\\midrule") (tag ^ ": midrule no booktabs"));
  run "PKG-011 clean with booktabs loaded" (fun tag ->
      expect
        (does_not_fire "PKG-011" "\\usepackage{booktabs}\n\\toprule")
        (tag ^ ": booktabs loaded"));
  run "PKG-011 clean with booktabs with options" (fun tag ->
      expect
        (does_not_fire "PKG-011"
           "\\usepackage[heavyrulewidth=1pt]{booktabs}\n\\toprule")
        (tag ^ ": booktabs with options"));
  run "PKG-011 clean empty" (fun tag ->
      expect (does_not_fire "PKG-011" "") (tag ^ ": empty"));

  (* ══════════════════════════════════════════════════════════════════════
     PKG-012: csquotes not loaded when \enquote used
     ══════════════════════════════════════════════════════════════════════ *)
  run "PKG-012 fires when enquote without csquotes" (fun tag ->
      expect (fires "PKG-012" "\\enquote{hello}") (tag ^ ": enquote no csquotes"));
  run "PKG-012 clean with csquotes loaded" (fun tag ->
      expect
        (does_not_fire "PKG-012" "\\usepackage{csquotes}\n\\enquote{hello}")
        (tag ^ ": csquotes loaded"));
  run "PKG-012 clean without enquote" (fun tag ->
      expect (does_not_fire "PKG-012" "just text") (tag ^ ": no enquote"));
  run "PKG-012 clean empty" (fun tag ->
      expect (does_not_fire "PKG-012" "") (tag ^ ": empty"));

  (* ══════════════════════════════════════════════════════════════════════
     PKG-015: inputenc loaded under XeLaTeX/LuaLaTeX
     ══════════════════════════════════════════════════════════════════════ *)
  run "PKG-015 fires with inputenc + fontspec" (fun tag ->
      expect
        (fires "PKG-015" "\\usepackage[utf8]{inputenc}\n\\usepackage{fontspec}")
        (tag ^ ": inputenc + fontspec"));
  run "PKG-015 clean without fontspec" (fun tag ->
      expect
        (does_not_fire "PKG-015" "\\usepackage[utf8]{inputenc}")
        (tag ^ ": inputenc only"));
  run "PKG-015 clean without inputenc" (fun tag ->
      expect
        (does_not_fire "PKG-015" "\\usepackage{fontspec}")
        (tag ^ ": fontspec only"));
  run "PKG-015 clean empty" (fun tag ->
      expect (does_not_fire "PKG-015" "") (tag ^ ": empty"));

  (* ══════════════════════════════════════════════════════════════════════
     PKG-020: tikz external library not loaded when externalising
     ══════════════════════════════════════════════════════════════════════ *)
  run "PKG-020 fires when tikzexternalize without library" (fun tag ->
      expect (fires "PKG-020" "\\tikzexternalize") (tag ^ ": externalize no lib"));
  run "PKG-020 clean with external library" (fun tag ->
      expect
        (does_not_fire "PKG-020" "\\usetikzlibrary{external}\n\\tikzexternalize")
        (tag ^ ": has external lib"));
  run "PKG-020 clean without tikzexternalize" (fun tag ->
      expect (does_not_fire "PKG-020" "just text") (tag ^ ": no externalize"));
  run "PKG-020 clean empty" (fun tag ->
      expect (does_not_fire "PKG-020" "") (tag ^ ": empty"));

  (* ══════════════════════════════════════════════════════════════════════
     PKG-022: Obsolete package (epsfig, subfigure, natbib) detected
     ══════════════════════════════════════════════════════════════════════ *)
  run "PKG-022 fires with epsfig" (fun tag ->
      expect (fires "PKG-022" "\\usepackage{epsfig}") (tag ^ ": epsfig"));
  run "PKG-022 fires with subfigure" (fun tag ->
      expect (fires "PKG-022" "\\usepackage{subfigure}") (tag ^ ": subfigure"));
  run "PKG-022 fires with natbib" (fun tag ->
      expect (fires "PKG-022" "\\usepackage{natbib}") (tag ^ ": natbib"));
  run "PKG-022 count=2 with two obsolete" (fun tag ->
      expect
        (fires_with_count "PKG-022" "\\usepackage{epsfig}\n\\usepackage{natbib}"
           2)
        (tag ^ ": two obsolete"));
  run "PKG-022 clean with modern packages" (fun tag ->
      expect
        (does_not_fire "PKG-022" "\\usepackage{graphicx}")
        (tag ^ ": modern pkg"));
  run "PKG-022 clean empty" (fun tag ->
      expect (does_not_fire "PKG-022" "") (tag ^ ": empty"));

  (* ══════════════════════════════════════════════════════════════════════
     PKG-023: unicode-math must load before microtype
     ══════════════════════════════════════════════════════════════════════ *)
  run "PKG-023 fires when unicode-math after microtype" (fun tag ->
      expect
        (fires "PKG-023"
           "\\usepackage{microtype}\n\
            \\usepackage{unicode-math}\n\
            \\begin{document}")
        (tag ^ ": unicode-math after microtype"));
  run "PKG-023 clean when unicode-math before microtype" (fun tag ->
      expect
        (does_not_fire "PKG-023"
           "\\usepackage{unicode-math}\n\
            \\usepackage{microtype}\n\
            \\begin{document}")
        (tag ^ ": correct order"));
  run "PKG-023 clean without both" (fun tag ->
      expect
        (does_not_fire "PKG-023" "\\usepackage{graphicx}\n\\begin{document}")
        (tag ^ ": neither pkg"));
  run "PKG-023 clean empty" (fun tag ->
      expect (does_not_fire "PKG-023" "") (tag ^ ": empty"));

  (* ══════════════════════════════════════════════════════════════════════
     LANG-002: babel language option missing
     ══════════════════════════════════════════════════════════════════════ *)
  run "LANG-002 fires when babel has no option" (fun tag ->
      expect (fires "LANG-002" "\\usepackage{babel}") (tag ^ ": bare babel"));
  run "LANG-002 fires when babel has empty option" (fun tag ->
      expect (fires "LANG-002" "\\usepackage[]{babel}") (tag ^ ": empty opt"));
  run "LANG-002 clean with babel option" (fun tag ->
      expect
        (does_not_fire "LANG-002" "\\usepackage[english]{babel}")
        (tag ^ ": has option"));
  run "LANG-002 clean without babel" (fun tag ->
      expect (does_not_fire "LANG-002" "just text") (tag ^ ": no babel"));
  run "LANG-002 clean empty" (fun tag ->
      expect (does_not_fire "LANG-002" "") (tag ^ ": empty"));

  (* ══════════════════════════════════════════════════════════════════════
     LANG-004: Polyglossia loaded alongside babel – mutual exclusion
     ══════════════════════════════════════════════════════════════════════ *)
  run "LANG-004 fires with both polyglossia and babel" (fun tag ->
      expect
        (fires "LANG-004"
           "\\usepackage{polyglossia}\n\\usepackage[english]{babel}")
        (tag ^ ": both loaded"));
  run "LANG-004 clean with only polyglossia" (fun tag ->
      expect
        (does_not_fire "LANG-004" "\\usepackage{polyglossia}")
        (tag ^ ": only polyglossia"));
  run "LANG-004 clean with only babel" (fun tag ->
      expect
        (does_not_fire "LANG-004" "\\usepackage[english]{babel}")
        (tag ^ ": only babel"));
  run "LANG-004 clean empty" (fun tag ->
      expect (does_not_fire "LANG-004" "") (tag ^ ": empty"));

  (* ══════════════════════════════════════════════════════════════════════
     TIKZ-007: TikZ loaded after hyperref – reorder required
     ══════════════════════════════════════════════════════════════════════ *)
  run "TIKZ-007 fires when tikz after hyperref" (fun tag ->
      expect
        (fires "TIKZ-007"
           "\\usepackage{hyperref}\n\\usepackage{tikz}\n\\begin{document}")
        (tag ^ ": tikz after hyperref"));
  run "TIKZ-007 clean when tikz before hyperref" (fun tag ->
      expect
        (does_not_fire "TIKZ-007"
           "\\usepackage{tikz}\n\\usepackage{hyperref}\n\\begin{document}")
        (tag ^ ": correct order"));
  run "TIKZ-007 clean without both" (fun tag ->
      expect
        (does_not_fire "TIKZ-007" "\\usepackage{graphicx}\n\\begin{document}")
        (tag ^ ": neither pkg"));
  run "TIKZ-007 clean empty" (fun tag ->
      expect (does_not_fire "TIKZ-007" "") (tag ^ ": empty"));

  (* ══════════════════════════════════════════════════════════════════════
     FIG-010: Subfigure environment without \subcaption
     ══════════════════════════════════════════════════════════════════════ *)
  run "FIG-010 fires on subfigure without subcaption" (fun tag ->
      expect
        (fires "FIG-010"
           "\\begin{subfigure}{0.5\\textwidth}\n\
            \\includegraphics{a.png}\n\
            \\end{subfigure}")
        (tag ^ ": no subcaption"));
  run "FIG-010 clean with subcaption" (fun tag ->
      expect
        (does_not_fire "FIG-010"
           "\\begin{subfigure}{0.5\\textwidth}\n\
            \\includegraphics{a.png}\n\
            \\subcaption{A}\n\
            \\end{subfigure}")
        (tag ^ ": has subcaption"));
  run "FIG-010 clean with caption" (fun tag ->
      expect
        (does_not_fire "FIG-010"
           "\\begin{subfigure}{0.5\\textwidth}\n\
            \\includegraphics{a.png}\n\
            \\caption{A}\n\
            \\end{subfigure}")
        (tag ^ ": has caption"));
  run "FIG-010 count=2 two subfigures without subcaption" (fun tag ->
      expect
        (fires_with_count "FIG-010"
           "\\begin{subfigure}{0.5\\textwidth}\n\
            \\includegraphics{a.png}\n\
            \\end{subfigure}\n\
            \\begin{subfigure}{0.5\\textwidth}\n\
            \\includegraphics{b.png}\n\
            \\end{subfigure}"
           2)
        (tag ^ ": two subfigures"));
  run "FIG-010 clean empty" (fun tag ->
      expect (does_not_fire "FIG-010" "") (tag ^ ": empty"));

  (* ══════════════════════════════════════════════════════════════════════
     FIG-013: Graphicx option scale used instead of width
     ══════════════════════════════════════════════════════════════════════ *)
  run "FIG-013 fires on scale option" (fun tag ->
      expect
        (fires "FIG-013" "\\includegraphics[scale=0.5]{img.png}")
        (tag ^ ": scale option"));
  run "FIG-013 clean with width option" (fun tag ->
      expect
        (does_not_fire "FIG-013"
           "\\includegraphics[width=0.5\\textwidth]{img.png}")
        (tag ^ ": width option"));
  run "FIG-013 clean without options" (fun tag ->
      expect
        (does_not_fire "FIG-013" "\\includegraphics{img.png}")
        (tag ^ ": no options"));
  run "FIG-013 count=2 two scale options" (fun tag ->
      expect
        (fires_with_count "FIG-013"
           "\\includegraphics[scale=0.5]{a.png}\n\
            \\includegraphics[scale=0.8]{b.png}"
           2)
        (tag ^ ": two scale options"));
  run "FIG-013 clean empty" (fun tag ->
      expect (does_not_fire "FIG-013" "") (tag ^ ": empty"))

let () = finalise "l2-batch3"
