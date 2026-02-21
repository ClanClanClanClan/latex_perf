(** Unit tests for L2-approx batch 4: 27 text-scannable rules
    PKG-008/010/013/014/016/017/021/024/025, TAB-003/007/008/012/013/015/016,
    FIG-012/014/017/019/022/024/025, MATH-075/080, CMD-012, DOC-004 *)

open Test_helpers

let () =
  Unix.putenv "L0_VALIDATORS" "pilot";

  (* ══════════════════════════════════════════════════════════════════════
     PKG-008: xcolor loaded without dvipsnames option
     ══════════════════════════════════════════════════════════════════════ *)
  run "PKG-008 fires when xcolor loaded without dvipsnames" (fun tag ->
      expect
        (fires "PKG-008"
           "\\documentclass{article}\n\
            \\usepackage{xcolor}\n\
            \\begin{document}\n\
            \\end{document}")
        tag);
  run "PKG-008 clean when dvipsnames present" (fun tag ->
      expect
        (does_not_fire "PKG-008"
           "\\documentclass{article}\n\
            \\usepackage[dvipsnames]{xcolor}\n\
            \\begin{document}\n\
            \\end{document}")
        tag);
  run "PKG-008 clean when no xcolor" (fun tag ->
      expect
        (does_not_fire "PKG-008"
           "\\documentclass{article}\n\\begin{document}\n\\end{document}")
        tag);

  (* ══════════════════════════════════════════════════════════════════════
     PKG-010: biblatex loaded with deprecated backend=biber
     ══════════════════════════════════════════════════════════════════════ *)
  run "PKG-010 fires with backend=biber" (fun tag ->
      expect
        (fires "PKG-010"
           "\\documentclass{article}\n\
            \\usepackage[backend=biber]{biblatex}\n\
            \\begin{document}\n\
            \\end{document}")
        tag);
  run "PKG-010 clean without backend option" (fun tag ->
      expect
        (does_not_fire "PKG-010"
           "\\documentclass{article}\n\
            \\usepackage{biblatex}\n\
            \\begin{document}\n\
            \\end{document}")
        tag);
  run "PKG-010 clean with backend=bibtex" (fun tag ->
      expect
        (does_not_fire "PKG-010"
           "\\documentclass{article}\n\
            \\usepackage[backend=bibtex]{biblatex}\n\
            \\begin{document}\n\
            \\end{document}")
        tag);

  (* ══════════════════════════════════════════════════════════════════════
     PKG-013: microtype not loaded on XeLaTeX path
     ══════════════════════════════════════════════════════════════════════ *)
  run "PKG-013 fires when fontspec without microtype" (fun tag ->
      expect
        (fires "PKG-013"
           "\\documentclass{article}\n\
            \\usepackage{fontspec}\n\
            \\begin{document}\n\
            \\end{document}")
        tag);
  run "PKG-013 clean when both present" (fun tag ->
      expect
        (does_not_fire "PKG-013"
           "\\documentclass{article}\n\
            \\usepackage{fontspec}\n\
            \\usepackage{microtype}\n\
            \\begin{document}\n\
            \\end{document}")
        tag);
  run "PKG-013 clean when no fontspec" (fun tag ->
      expect
        (does_not_fire "PKG-013"
           "\\documentclass{article}\n\\begin{document}\n\\end{document}")
        tag);

  (* ══════════════════════════════════════════════════════════════════════
     PKG-014: siunitx v2 API detected (outdated)
     ══════════════════════════════════════════════════════════════════════ *)
  run "PKG-014 fires with \\SI{" (fun tag ->
      expect
        (fires "PKG-014"
           "\\documentclass{article}\n\
            \\usepackage{siunitx}\n\
            \\begin{document}\n\
            \\SI{10}{kg}\n\
            \\end{document}")
        tag);
  run "PKG-014 fires with \\si{" (fun tag ->
      expect
        (fires "PKG-014"
           "\\documentclass{article}\n\
            \\usepackage{siunitx}\n\
            \\begin{document}\n\
            \\si{m/s}\n\
            \\end{document}")
        tag);
  run "PKG-014 clean with v3 API \\qty" (fun tag ->
      expect
        (does_not_fire "PKG-014"
           "\\documentclass{article}\n\
            \\usepackage{siunitx}\n\
            \\begin{document}\n\
            \\qty{10}{kg}\n\
            \\end{document}")
        tag);
  run "PKG-014 clean when siunitx not loaded" (fun tag ->
      expect
        (does_not_fire "PKG-014"
           "\\documentclass{article}\n\
            \\begin{document}\n\
            \\SI{10}{kg}\n\
            \\end{document}")
        tag);

  (* ══════════════════════════════════════════════════════════════════════
     PKG-016: graphicx option pdftex incompatible with engine
     ══════════════════════════════════════════════════════════════════════ *)
  run "PKG-016 fires with [pdftex]{graphicx}" (fun tag ->
      expect
        (fires "PKG-016"
           "\\documentclass{article}\n\
            \\usepackage[pdftex]{graphicx}\n\
            \\begin{document}\n\
            \\end{document}")
        tag);
  run "PKG-016 clean without pdftex option" (fun tag ->
      expect
        (does_not_fire "PKG-016"
           "\\documentclass{article}\n\
            \\usepackage{graphicx}\n\
            \\begin{document}\n\
            \\end{document}")
        tag);

  (* ══════════════════════════════════════════════════════════════════════
     PKG-017: fontspec loaded in pdfLaTeX
     ══════════════════════════════════════════════════════════════════════ *)
  run "PKG-017 fires with fontspec + T1 fontenc" (fun tag ->
      expect
        (fires "PKG-017"
           "\\documentclass{article}\n\
            \\usepackage[T1]{fontenc}\n\
            \\usepackage{fontspec}\n\
            \\begin{document}\n\
            \\end{document}")
        tag);
  run "PKG-017 fires with fontspec + inputenc" (fun tag ->
      expect
        (fires "PKG-017"
           "\\documentclass{article}\n\
            \\usepackage[utf8]{inputenc}\n\
            \\usepackage{fontspec}\n\
            \\begin{document}\n\
            \\end{document}")
        tag);
  run "PKG-017 clean with fontspec alone (XeLaTeX assumed)" (fun tag ->
      expect
        (does_not_fire "PKG-017"
           "\\documentclass{article}\n\
            \\usepackage{fontspec}\n\
            \\begin{document}\n\
            \\end{document}")
        tag);

  (* ══════════════════════════════════════════════════════════════════════
     PKG-021: Package loaded twice with conflicting options
     ══════════════════════════════════════════════════════════════════════ *)
  run "PKG-021 fires with conflicting options" (fun tag ->
      expect
        (fires "PKG-021"
           "\\documentclass{article}\n\
            \\usepackage[a]{foo}\n\
            \\usepackage[b]{foo}\n\
            \\begin{document}\n\
            \\end{document}")
        tag);
  run "PKG-021 clean with same options" (fun tag ->
      expect
        (does_not_fire "PKG-021"
           "\\documentclass{article}\n\
            \\usepackage[a]{foo}\n\
            \\usepackage[a]{foo}\n\
            \\begin{document}\n\
            \\end{document}")
        tag);
  run "PKG-021 clean with different packages" (fun tag ->
      expect
        (does_not_fire "PKG-021"
           "\\documentclass{article}\n\
            \\usepackage[a]{foo}\n\
            \\usepackage[b]{bar}\n\
            \\begin{document}\n\
            \\end{document}")
        tag);

  (* ══════════════════════════════════════════════════════════════════════
     PKG-024: polyglossia language duplicated via \setdefaultlanguage
     ══════════════════════════════════════════════════════════════════════ *)
  run "PKG-024 fires with duplicate language" (fun tag ->
      expect
        (fires "PKG-024"
           "\\setdefaultlanguage{english}\n\\setotherlanguage{english}")
        tag);
  run "PKG-024 clean with different languages" (fun tag ->
      expect
        (does_not_fire "PKG-024"
           "\\setdefaultlanguage{english}\n\\setotherlanguage{french}")
        tag);
  run "PKG-024 clean with no polyglossia" (fun tag ->
      expect (does_not_fire "PKG-024" "\\documentclass{article}") tag);

  (* ══════════════════════════════════════════════════════════════════════
     PKG-025: Engine option mismatch
     ══════════════════════════════════════════════════════════════════════ *)
  run "PKG-025 fires with fontspec + fontenc + inputenc" (fun tag ->
      expect
        (fires "PKG-025"
           "\\documentclass{article}\n\
            \\usepackage[T1]{fontenc}\n\
            \\usepackage[utf8]{inputenc}\n\
            \\usepackage{fontspec}\n\
            \\begin{document}\n\
            \\end{document}")
        tag);
  run "PKG-025 clean with fontspec alone" (fun tag ->
      expect
        (does_not_fire "PKG-025"
           "\\documentclass{article}\n\
            \\usepackage{fontspec}\n\
            \\begin{document}\n\
            \\end{document}")
        tag);
  run "PKG-025 clean with only pdflatex markers" (fun tag ->
      expect
        (does_not_fire "PKG-025"
           "\\documentclass{article}\n\
            \\usepackage[T1]{fontenc}\n\
            \\usepackage[utf8]{inputenc}\n\
            \\begin{document}\n\
            \\end{document}")
        tag);

  (* ══════════════════════════════════════════════════════════════════════
     TAB-003: Decimal column not aligned on dot
     ══════════════════════════════════════════════════════════════════════ *)
  run "TAB-003 fires with decimal in r column" (fun tag ->
      expect
        (fires "TAB-003"
           "\\begin{tabular}{lr}\nName & 1.5 \\\\\nOther & 2.3\n\\end{tabular}")
        tag);
  run "TAB-003 clean with S column" (fun tag ->
      expect
        (does_not_fire "TAB-003"
           "\\begin{tabular}{lS}\nName & 1.5 \\\\\nOther & 2.3\n\\end{tabular}")
        tag);
  run "TAB-003 clean without decimals" (fun tag ->
      expect
        (does_not_fire "TAB-003"
           "\\begin{tabular}{lr}\nName & 5 \\\\\nOther & 3\n\\end{tabular}")
        tag);

  (* ══════════════════════════════════════════════════════════════════════
     TAB-007: Text in numeric column without \multicolumn
     ══════════════════════════════════════════════════════════════════════ *)
  run "TAB-007 fires with text in S column" (fun tag ->
      expect
        (fires "TAB-007"
           "\\begin{tabular}{lS}\nText & hello \\\\\n\\end{tabular}")
        tag);
  run "TAB-007 clean with multicolumn wrapper" (fun tag ->
      expect
        (does_not_fire "TAB-007"
           "\\begin{tabular}{lS}\n\
            \\multicolumn{1}{c}{Header} & 1.0 \\\\\n\
            \\end{tabular}")
        tag);
  run "TAB-007 clean without S column" (fun tag ->
      expect
        (does_not_fire "TAB-007"
           "\\begin{tabular}{lr}\nText & hello \\\\\n\\end{tabular}")
        tag);

  (* ══════════════════════════════════════════════════════════════════════
     TAB-008: Table > 30 rows - suggest longtable
     ══════════════════════════════════════════════════════════════════════ *)
  run "TAB-008 fires with > 30 rows" (fun tag ->
      let rows =
        String.concat " \\\\\n"
          (List.init 32 (fun i -> Printf.sprintf "a%d & b%d" i i))
      in
      expect
        (fires "TAB-008"
           (Printf.sprintf "\\begin{tabular}{ll}\n%s\n\\end{tabular}" rows))
        tag);
  run "TAB-008 clean with < 30 rows" (fun tag ->
      let rows =
        String.concat " \\\\\n"
          (List.init 10 (fun i -> Printf.sprintf "a%d & b%d" i i))
      in
      expect
        (does_not_fire "TAB-008"
           (Printf.sprintf "\\begin{tabular}{ll}\n%s\n\\end{tabular}" rows))
        tag);

  (* ══════════════════════════════════════════════════════════════════════
     TAB-012: Numeric column not aligned using siunitx S-column
     ══════════════════════════════════════════════════════════════════════ *)
  run "TAB-012 fires with numbers in r column" (fun tag ->
      expect
        (fires "TAB-012"
           "\\begin{tabular}{lr}\nItem & 42.5 \\\\\n\\end{tabular}")
        tag);
  run "TAB-012 clean with S column" (fun tag ->
      expect
        (does_not_fire "TAB-012"
           "\\begin{tabular}{lS}\nItem & 42.5 \\\\\n\\end{tabular}")
        tag);
  run "TAB-012 clean without numbers" (fun tag ->
      expect
        (does_not_fire "TAB-012"
           "\\begin{tabular}{lr}\nItem & text \\\\\n\\end{tabular}")
        tag);

  (* ══════════════════════════════════════════════════════════════════════
     TAB-013: Caption position for longtable must be at top
     ══════════════════════════════════════════════════════════════════════ *)
  run "TAB-013 fires with caption after data" (fun tag ->
      expect
        (fires "TAB-013"
           "\\begin{longtable}{ll}\n\
            a & b \\\\\n\
            \\caption{Test}\n\
            \\end{longtable}")
        tag);
  run "TAB-013 clean with caption before data" (fun tag ->
      expect
        (does_not_fire "TAB-013"
           "\\begin{longtable}{ll}\n\
            \\caption{Test}\n\
            a & b \\\\\n\
            \\end{longtable}")
        tag);
  run "TAB-013 clean without caption" (fun tag ->
      expect
        (does_not_fire "TAB-013"
           "\\begin{longtable}{ll}\na & b \\\\\n\\end{longtable}")
        tag);

  (* ══════════════════════════════════════════════════════════════════════
     TAB-015: \multirow inside tabularx X column without raggedright
     ══════════════════════════════════════════════════════════════════════ *)
  run "TAB-015 fires with multirow in tabularx no raggedright" (fun tag ->
      expect
        (fires "TAB-015"
           "\\begin{tabularx}{\\textwidth}{lX}\n\
            a & \\multirow{2}{*}{text} \\\\\n\
            \\end{tabularx}")
        tag);
  run "TAB-015 clean with raggedright" (fun tag ->
      expect
        (does_not_fire "TAB-015"
           "\\begin{tabularx}{\\textwidth}{lX}\n\
            a & \\raggedright \\multirow{2}{*}{text} \\\\\n\
            \\end{tabularx}")
        tag);
  run "TAB-015 clean without multirow" (fun tag ->
      expect
        (does_not_fire "TAB-015"
           "\\begin{tabularx}{\\textwidth}{lX}\na & text \\\\\n\\end{tabularx}")
        tag);

  (* ══════════════════════════════════════════════════════════════════════
     TAB-016: Centred 'c' column in longtable holds ragged text
     ══════════════════════════════════════════════════════════════════════ *)
  run "TAB-016 fires with c column in longtable" (fun tag ->
      expect
        (fires "TAB-016" "\\begin{longtable}{cc}\na & b \\\\\n\\end{longtable}")
        tag);
  run "TAB-016 clean with l columns" (fun tag ->
      expect
        (does_not_fire "TAB-016"
           "\\begin{longtable}{ll}\na & b \\\\\n\\end{longtable}")
        tag);

  (* ══════════════════════════════════════════════════════════════════════
     FIG-012: Figure listed in LoF but not referenced
     ══════════════════════════════════════════════════════════════════════ *)
  run "FIG-012 fires with unreferenced figure label" (fun tag ->
      expect
        (fires "FIG-012"
           "\\begin{figure}\n\
            \\includegraphics{img}\n\
            \\caption{Test}\n\
            \\label{fig:test}\n\
            \\end{figure}")
        tag);
  run "FIG-012 clean when referenced" (fun tag ->
      expect
        (does_not_fire "FIG-012"
           "See Figure~\\ref{fig:test}.\n\
            \\begin{figure}\n\
            \\includegraphics{img}\n\
            \\caption{Test}\n\
            \\label{fig:test}\n\
            \\end{figure}")
        tag);
  run "FIG-012 clean without fig label" (fun tag ->
      expect
        (does_not_fire "FIG-012"
           "\\begin{figure}\n\
            \\includegraphics{img}\n\
            \\caption{Test}\n\
            \\end{figure}")
        tag);

  (* ══════════════════════════════════════════════════════════════════════
     FIG-014: Figure caption exceeds 300 characters
     ══════════════════════════════════════════════════════════════════════ *)
  run "FIG-014 fires with long caption" (fun tag ->
      let long_text = String.make 310 'x' in
      expect
        (fires "FIG-014"
           (Printf.sprintf
              "\\begin{figure}\n\
               \\includegraphics{img}\n\
               \\caption{%s}\n\
               \\end{figure}"
              long_text))
        tag);
  run "FIG-014 clean with short caption" (fun tag ->
      expect
        (does_not_fire "FIG-014"
           "\\begin{figure}\n\
            \\includegraphics{img}\n\
            \\caption{Short caption}\n\
            \\end{figure}")
        tag);

  (* ══════════════════════════════════════════════════════════════════════
     FIG-017: Sidewaysfigure used with portrait page layout
     ══════════════════════════════════════════════════════════════════════ *)
  run "FIG-017 fires with sidewaysfigure" (fun tag ->
      expect
        (fires "FIG-017"
           "\\documentclass{article}\n\
            \\begin{document}\n\
            \\begin{sidewaysfigure}\n\
            \\includegraphics{img}\n\
            \\end{sidewaysfigure}\n\
            \\end{document}")
        tag);
  run "FIG-017 clean with landscape" (fun tag ->
      expect
        (does_not_fire "FIG-017"
           "\\documentclass{article}\n\
            \\usepackage[landscape]{geometry}\n\
            \\begin{document}\n\
            \\begin{sidewaysfigure}\n\
            \\includegraphics{img}\n\
            \\end{sidewaysfigure}\n\
            \\end{document}")
        tag);
  run "FIG-017 clean without sidewaysfigure" (fun tag ->
      expect
        (does_not_fire "FIG-017"
           "\\documentclass{article}\n\
            \\begin{document}\n\
            \\begin{figure}\n\
            \\includegraphics{img}\n\
            \\end{figure}\n\
            \\end{document}")
        tag);

  (* ══════════════════════════════════════════════════════════════════════
     FIG-019: Subcaption label missing (a), (b)...
     ══════════════════════════════════════════════════════════════════════ *)
  run "FIG-019 fires with subfigure without subcaption" (fun tag ->
      expect
        (fires "FIG-019"
           "\\begin{figure}\n\
            \\begin{subfigure}{0.5\\textwidth}\n\
            \\includegraphics{img}\n\
            \\end{subfigure}\n\
            \\end{figure}")
        tag);
  run "FIG-019 clean with subcaption" (fun tag ->
      expect
        (does_not_fire "FIG-019"
           "\\begin{figure}\n\
            \\begin{subfigure}{0.5\\textwidth}\n\
            \\includegraphics{img}\n\
            \\subcaption{Part A}\n\
            \\end{subfigure}\n\
            \\end{figure}")
        tag);
  run "FIG-019 clean with caption in subfigure" (fun tag ->
      expect
        (does_not_fire "FIG-019"
           "\\begin{figure}\n\
            \\begin{subfigure}{0.5\\textwidth}\n\
            \\includegraphics{img}\n\
            \\caption{Part A}\n\
            \\end{subfigure}\n\
            \\end{figure}")
        tag);

  (* ══════════════════════════════════════════════════════════════════════
     FIG-022: Figure caption identical to surrounding sentence
     ══════════════════════════════════════════════════════════════════════ *)
  run "FIG-022 fires with duplicated caption text" (fun tag ->
      expect
        (fires "FIG-022"
           "This shows the results of the experiment.\n\
            \\begin{figure}\n\
            \\includegraphics{img}\n\
            \\caption{This shows the results of the experiment.}\n\
            \\end{figure}")
        tag);
  run "FIG-022 clean with different caption" (fun tag ->
      expect
        (does_not_fire "FIG-022"
           "Discussion of results follows.\n\
            \\begin{figure}\n\
            \\includegraphics{img}\n\
            \\caption{Performance comparison}\n\
            \\end{figure}")
        tag);

  (* ══════════════════════════════════════════════════════════════════════
     FIG-024: Alt-text exceeds 140 chars
     ══════════════════════════════════════════════════════════════════════ *)
  run "FIG-024 fires with long alt text" (fun tag ->
      let long_alt = String.make 150 'a' in
      expect
        (fires "FIG-024"
           (Printf.sprintf "\\includegraphics[alt={%s}]{img.png}" long_alt))
        tag);
  run "FIG-024 clean with short alt text" (fun tag ->
      expect
        (does_not_fire "FIG-024"
           "\\includegraphics[alt={A graph showing performance}]{img.png}")
        tag);
  run "FIG-024 clean without alt text" (fun tag ->
      expect (does_not_fire "FIG-024" "\\includegraphics{img.png}") tag);

  (* ══════════════════════════════════════════════════════════════════════
     FIG-025: Alt-text identical to caption
     ══════════════════════════════════════════════════════════════════════ *)
  run "FIG-025 fires with matching alt and caption" (fun tag ->
      expect
        (fires "FIG-025"
           "\\begin{figure}\n\
            \\includegraphics[alt={Performance graph}]{img}\n\
            \\caption{Performance graph}\n\
            \\end{figure}")
        tag);
  run "FIG-025 clean with different alt and caption" (fun tag ->
      expect
        (does_not_fire "FIG-025"
           "\\begin{figure}\n\
            \\includegraphics[alt={A bar chart}]{img}\n\
            \\caption{Performance comparison}\n\
            \\end{figure}")
        tag);
  run "FIG-025 clean without alt text" (fun tag ->
      expect
        (does_not_fire "FIG-025"
           "\\begin{figure}\n\
            \\includegraphics{img}\n\
            \\caption{Test}\n\
            \\end{figure}")
        tag);

  (* ══════════════════════════════════════════════════════════════════════
     MATH-075: Equation number suppressed with \nonumber but referenced
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-075 fires with nonumber but referenced" (fun tag ->
      expect
        (fires "MATH-075"
           "See \\ref{eq:x}.\n\
            \\begin{equation}\\label{eq:x}\\nonumber x=1\\end{equation}")
        tag);
  run "MATH-075 clean without ref" (fun tag ->
      expect
        (does_not_fire "MATH-075"
           "\\begin{equation}\\label{eq:x}\\nonumber x=1\\end{equation}")
        tag);
  run "MATH-075 clean without nonumber" (fun tag ->
      expect
        (does_not_fire "MATH-075"
           "See \\ref{eq:x}.\n\\begin{equation}\\label{eq:x} x=1\\end{equation}")
        tag);

  (* ══════════════════════════════════════════════════════════════════════
     MATH-080: Equation exceeds 3 alignment columns
     ══════════════════════════════════════════════════════════════════════ *)
  run "MATH-080 fires with > 3 alignment points" (fun tag ->
      expect
        (fires "MATH-080" "\\begin{align}\na & b & c & d & e\n\\end{align}")
        tag);
  run "MATH-080 clean with <= 3 alignment points" (fun tag ->
      expect
        (does_not_fire "MATH-080" "\\begin{align}\na & = & b\n\\end{align}")
        tag);
  run "MATH-080 fires in align* too" (fun tag ->
      expect
        (fires "MATH-080" "\\begin{align*}\nx & y & z & w & v\n\\end{align*}")
        tag);

  (* ══════════════════════════════════════════════════════════════════════
     CMD-012: \renewcommand\thesection after hyperref
     ══════════════════════════════════════════════════════════════════════ *)
  run "CMD-012 fires with thesection after hyperref" (fun tag ->
      expect
        (fires "CMD-012"
           "\\documentclass{article}\n\
            \\usepackage{hyperref}\n\
            \\renewcommand{\\thesection}{S\\arabic{section}}\n\
            \\begin{document}\n\
            \\end{document}")
        tag);
  run "CMD-012 clean with thesection before hyperref" (fun tag ->
      expect
        (does_not_fire "CMD-012"
           "\\documentclass{article}\n\
            \\renewcommand{\\thesection}{S\\arabic{section}}\n\
            \\usepackage{hyperref}\n\
            \\begin{document}\n\
            \\end{document}")
        tag);
  run "CMD-012 clean without hyperref" (fun tag ->
      expect
        (does_not_fire "CMD-012"
           "\\documentclass{article}\n\
            \\renewcommand{\\thesection}{S\\arabic{section}}\n\
            \\begin{document}\n\
            \\end{document}")
        tag);

  (* ══════════════════════════════════════════════════════════════════════
     DOC-004: Acknowledgment section before conclusion
     ══════════════════════════════════════════════════════════════════════ *)
  run "DOC-004 fires when acknowledgment before conclusion" (fun tag ->
      expect
        (fires "DOC-004"
           "\\section{Acknowledgment}\nThanks.\n\\section{Conclusion}\nDone.")
        tag);
  run "DOC-004 clean when conclusion first" (fun tag ->
      expect
        (does_not_fire "DOC-004"
           "\\section{Conclusion}\nDone.\n\\section{Acknowledgment}\nThanks.")
        tag);
  run "DOC-004 clean without both sections" (fun tag ->
      expect (does_not_fire "DOC-004" "\\section{Introduction}\nHello.") tag)

let () = finalise "l2-batch4"
