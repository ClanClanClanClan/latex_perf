(** Unit tests for L3 text-scannable approximation rules: 22 rules.
    BIB-002..016, PKG-018/019, FONT-005, LAY-015/020/022, REF-008, META-001,
    PDF-010, TIKZ-005.

    ~100 total test cases. *)

open Test_helpers

let () =
  Unix.putenv "L0_VALIDATORS" "pilot";

  (* ══════════════════════════════════════════════════════════════════════
     BIB-002: DOI not normalised to https://doi.org/ form
     ══════════════════════════════════════════════════════════════════════ *)
  run "BIB-002 fires: bare DOI" (fun tag ->
      expect
        (fires "BIB-002"
           {|@article{key1,
  author = {Smith, John},
  doi = {10.1234/foo}
}|})
        (tag ^ ": bare DOI not https"));
  run "BIB-002 fires: http DOI" (fun tag ->
      expect
        (fires "BIB-002"
           {|@article{key1,
  doi = {http://doi.org/10.1234/foo}
}|})
        (tag ^ ": http DOI not https"));
  run "BIB-002 clean: https://doi.org/ DOI" (fun tag ->
      expect
        (does_not_fire "BIB-002"
           {|@article{key1,
  doi = {https://doi.org/10.1234/foo}
}|})
        (tag ^ ": normalised https doi"));
  run "BIB-002 clean: no DOI field" (fun tag ->
      expect
        (does_not_fire "BIB-002"
           {|@article{key1,
  author = {Smith, John},
  title = {A Paper}
}|})
        (tag ^ ": no doi field"));

  (* ══════════════════════════════════════════════════════════════════════
     BIB-003: Journal title capitalisation inconsistent
     ══════════════════════════════════════════════════════════════════════ *)
  run "BIB-003 fires: multiple cap words" (fun tag ->
      expect
        (fires "BIB-003"
           {|@article{key1,
  journal = {Physical Review Letters}
}|})
        (tag ^ ": Physical Review Letters"));
  run "BIB-003 fires: two capitalised words" (fun tag ->
      expect
        (fires "BIB-003" {|@article{key1,
  journal = {Nature Physics}
}|})
        (tag ^ ": Nature Physics"));
  run "BIB-003 clean: abbreviation lowercase" (fun tag ->
      expect
        (does_not_fire "BIB-003"
           {|@article{key1,
  journal = {phys. rev. lett.}
}|})
        (tag ^ ": abbreviated lowercase"));
  run "BIB-003 clean: single capitalised word" (fun tag ->
      expect
        (does_not_fire "BIB-003" {|@article{key1,
  journal = {Nature}
}|})
        (tag ^ ": single cap word ok"));
  run "BIB-003 clean: no journal field" (fun tag ->
      expect
        (does_not_fire "BIB-003" {|@article{key1,
  title = {A Paper}
}|})
        (tag ^ ": no journal field"));

  (* ══════════════════════════════════════════════════════════════════════
     BIB-004: Book entry lacks publisher field
     ══════════════════════════════════════════════════════════════════════ *)
  run "BIB-004 fires: @Book without publisher" (fun tag ->
      expect
        (fires "BIB-004"
           {|@Book{key1,
  author = {Doe, Jane},
  title = {My Book}
}|})
        (tag ^ ": Book without publisher"));
  run "BIB-004 fires: @book lowercase without publisher" (fun tag ->
      expect
        (fires "BIB-004"
           {|@book{key2,
  author = {Doe, Jane},
  title = {Another Book}
}|})
        (tag ^ ": book lowercase no publisher"));
  run "BIB-004 clean: @Book with publisher" (fun tag ->
      expect
        (does_not_fire "BIB-004"
           {|@Book{key1,
  author = {Doe, Jane},
  title = {My Book},
  publisher = {Springer}
}|})
        (tag ^ ": Book with publisher"));
  run "BIB-004 clean: @article (not book)" (fun tag ->
      expect
        (does_not_fire "BIB-004"
           {|@article{key1,
  author = {Doe, Jane},
  title = {A Paper}
}|})
        (tag ^ ": article not book"));

  (* ══════════════════════════════════════════════════════════════════════
     BIB-005: URL present without urldate
     ══════════════════════════════════════════════════════════════════════ *)
  run "BIB-005 fires: url without urldate" (fun tag ->
      expect
        (fires "BIB-005"
           {|@article{key1,
  author = {Smith, John},
  url = {http://example.com}
}|})
        (tag ^ ": url without urldate"));
  run "BIB-005 fires: url with https but no urldate" (fun tag ->
      expect
        (fires "BIB-005" {|@misc{key2,
  url = {https://example.org/path}
}|})
        (tag ^ ": https url no urldate"));
  run "BIB-005 clean: url with urldate" (fun tag ->
      expect
        (does_not_fire "BIB-005"
           {|@article{key1,
  url = {http://example.com},
  urldate = {2024-01-15}
}|})
        (tag ^ ": url with urldate"));
  run "BIB-005 clean: no url field" (fun tag ->
      expect
        (does_not_fire "BIB-005"
           {|@article{key1,
  author = {Smith, John},
  title = {A Paper}
}|})
        (tag ^ ": no url field"));

  (* ══════════════════════════════════════════════════════════════════════
     BIB-006: Author names not in "von Last, First" scheme
     ══════════════════════════════════════════════════════════════════════ *)
  run "BIB-006 fires: First Last pattern" (fun tag ->
      expect
        (fires "BIB-006" {|@article{key1,
  author = {John Smith}
}|})
        (tag ^ ": John Smith = First Last"));
  run "BIB-006 fires: First Last in multi-author" (fun tag ->
      expect
        (fires "BIB-006"
           {|@article{key1,
  author = {Alice Johnson and Bob Williams}
}|})
        (tag ^ ": First Last multi-author"));
  run "BIB-006 clean: Last, First" (fun tag ->
      expect
        (does_not_fire "BIB-006" {|@article{key1,
  author = {Smith, John}
}|})
        (tag ^ ": Smith, John ok"));
  run "BIB-006 clean: Last, First multi-author" (fun tag ->
      expect
        (does_not_fire "BIB-006"
           {|@article{key1,
  author = {Smith, John and Doe, Jane}
}|})
        (tag ^ ": Last, First multi ok"));

  (* ══════════════════════════════════════════════════════════════════════
     BIB-008: CamelCase field names
     ══════════════════════════════════════════════════════════════════════ *)
  run "BIB-008 fires: Title capitalised field" (fun tag ->
      expect
        (fires "BIB-008" {|@article{key1,
  Title = {Some Title}
}|})
        (tag ^ ": Title capitalised"));
  run "BIB-008 fires: Author capitalised field" (fun tag ->
      expect
        (fires "BIB-008" {|@article{key1,
  Author = {Doe, Jane}
}|})
        (tag ^ ": Author capitalised"));
  run "BIB-008 clean: lowercase field" (fun tag ->
      expect
        (does_not_fire "BIB-008" {|@article{key1,
  title = {Some Title}
}|})
        (tag ^ ": lowercase title ok"));
  run "BIB-008 clean: no bib entries" (fun tag ->
      expect
        (does_not_fire "BIB-008" {|Just some plain text with Title = {foo}.|})
        (tag ^ ": no bib entry context"));

  (* ══════════════════════════════════════════════════════════════════════
     BIB-009: inproceedings missing booktitle
     ══════════════════════════════════════════════════════════════════════ *)
  run "BIB-009 fires: @InProceedings no booktitle" (fun tag ->
      expect
        (fires "BIB-009"
           {|@InProceedings{key1,
  author = {Doe, Jane},
  title = {A Paper}
}|})
        (tag ^ ": InProceedings no booktitle"));
  run "BIB-009 fires: @inproceedings lowercase no booktitle" (fun tag ->
      expect
        (fires "BIB-009" {|@inproceedings{key2,
  author = {Smith, John}
}|})
        (tag ^ ": inproceedings no booktitle"));
  run "BIB-009 clean: @InProceedings with booktitle" (fun tag ->
      expect
        (does_not_fire "BIB-009"
           {|@InProceedings{key1,
  author = {Doe, Jane},
  booktitle = {Proceedings of ICML}
}|})
        (tag ^ ": has booktitle"));
  run "BIB-009 clean: @article (not inproceedings)" (fun tag ->
      expect
        (does_not_fire "BIB-009"
           {|@article{key1,
  author = {Doe, Jane},
  title = {A Paper}
}|})
        (tag ^ ": article not inproceedings"));

  (* ══════════════════════════════════════════════════════════════════════
     BIB-010: month uses numeric literal
     ══════════════════════════════════════════════════════════════════════ *)
  run "BIB-010 fires: month = {3}" (fun tag ->
      expect
        (fires "BIB-010" {|@article{key1,
  month = {3}
}|})
        (tag ^ ": month numeric brace"));
  run "BIB-010 fires: month = \"March\"" (fun tag ->
      expect
        (fires "BIB-010" {|@article{key1,
  month = "March"
}|})
        (tag ^ ": month quoted string"));
  run "BIB-010 clean: month = mar (bare macro)" (fun tag ->
      expect
        (does_not_fire "BIB-010" {|@article{key1,
  month = mar
}|})
        (tag ^ ": bare macro ok"));
  run "BIB-010 clean: no month field" (fun tag ->
      expect
        (does_not_fire "BIB-010" {|@article{key1,
  author = {Smith, John}
}|})
        (tag ^ ": no month field"));

  (* ══════════════════════════════════════════════════════════════════════
     BIB-011: Legacy note URL
     ══════════════════════════════════════════════════════════════════════ *)
  run "BIB-011 fires: note = {URL: http...}" (fun tag ->
      expect
        (fires "BIB-011" {|@article{key1,
  note = {URL: http://example.com}
}|})
        (tag ^ ": note URL: prefix"));
  run "BIB-011 fires: note = {http://...}" (fun tag ->
      expect
        (fires "BIB-011"
           {|@article{key1,
  note = {http://example.com/paper}
}|})
        (tag ^ ": note bare http"));
  run "BIB-011 clean: url in url field" (fun tag ->
      expect
        (does_not_fire "BIB-011"
           {|@article{key1,
  url = {http://example.com},
  note = {Some general note}
}|})
        (tag ^ ": url in url field ok"));
  run "BIB-011 clean: note without URL" (fun tag ->
      expect
        (does_not_fire "BIB-011"
           {|@article{key1,
  note = {Published in print edition}
}|})
        (tag ^ ": note no URL"));

  (* ══════════════════════════════════════════════════════════════════════
     BIB-012: et al. hard-coded in author
     ══════════════════════════════════════════════════════════════════════ *)
  run "BIB-012 fires: et al. in author" (fun tag ->
      expect
        (fires "BIB-012"
           {|@article{key1,
  author = {Smith, John and others et al.}
}|})
        (tag ^ ": et al. hardcoded"));
  run "BIB-012 fires: et al. trailing" (fun tag ->
      expect
        (fires "BIB-012" {|@article{key1,
  author = {Doe, Jane et al.}
}|})
        (tag ^ ": et al. trailing"));
  run "BIB-012 clean: no et al." (fun tag ->
      expect
        (does_not_fire "BIB-012"
           {|@article{key1,
  author = {Smith, John and Others}
}|})
        (tag ^ ": and Others ok"));
  run "BIB-012 clean: no author field" (fun tag ->
      expect
        (does_not_fire "BIB-012" {|@article{key1,
  title = {A Paper}
}|})
        (tag ^ ": no author"));

  (* ══════════════════════════════════════════════════════════════════════
     BIB-015: Trailing period in title/note
     ══════════════════════════════════════════════════════════════════════ *)
  run "BIB-015 fires: title with trailing period" (fun tag ->
      expect
        (fires "BIB-015" {|@article{key1,
  title = {My Title.}
}|})
        (tag ^ ": title trailing period"));
  run "BIB-015 fires: note with trailing period" (fun tag ->
      expect
        (fires "BIB-015" {|@article{key1,
  note = {Some note text.}
}|})
        (tag ^ ": note trailing period"));
  run "BIB-015 clean: title without trailing period" (fun tag ->
      expect
        (does_not_fire "BIB-015" {|@article{key1,
  title = {My Title}
}|})
        (tag ^ ": no trailing period"));
  run "BIB-015 clean: no title or note" (fun tag ->
      expect
        (does_not_fire "BIB-015" {|@article{key1,
  author = {Smith, John}
}|})
        (tag ^ ": no title/note"));

  (* ══════════════════════════════════════════════════════════════════════
     BIB-016: Both DOI and URL present
     ══════════════════════════════════════════════════════════════════════ *)
  run "BIB-016 fires: doi + url in same entry" (fun tag ->
      expect
        (fires "BIB-016"
           {|@article{key1,
  doi = {10.1234/foo},
  url = {http://example.com}
}|})
        (tag ^ ": both doi and url"));
  run "BIB-016 fires: doi + url with https" (fun tag ->
      expect
        (fires "BIB-016"
           {|@article{key1,
  doi = {https://doi.org/10.1234/foo},
  url = {https://example.com/paper}
}|})
        (tag ^ ": doi + https url"));
  run "BIB-016 clean: doi only" (fun tag ->
      expect
        (does_not_fire "BIB-016" {|@article{key1,
  doi = {10.1234/foo}
}|})
        (tag ^ ": doi only ok"));
  run "BIB-016 clean: url only" (fun tag ->
      expect
        (does_not_fire "BIB-016"
           {|@article{key1,
  url = {http://example.com}
}|})
        (tag ^ ": url only ok"));
  run "BIB-016 clean: doi + urldate (no bare url)" (fun tag ->
      expect
        (does_not_fire "BIB-016"
           {|@article{key1,
  doi = {10.1234/foo},
  urldate = {2024-01-15}
}|})
        (tag ^ ": doi + urldate, no url"));

  (* ══════════════════════════════════════════════════════════════════════
     PKG-018: hyperref draft left enabled
     ══════════════════════════════════════════════════════════════════════ *)
  run "PKG-018 fires: usepackage[draft]{hyperref}" (fun tag ->
      expect
        (fires "PKG-018"
           {|\documentclass{article}
\usepackage[draft]{hyperref}
\begin{document}\end{document}|})
        (tag ^ ": draft option in usepackage"));
  run "PKG-018 fires: hypersetup{draft=true}" (fun tag ->
      expect
        (fires "PKG-018"
           {|\documentclass{article}
\usepackage{hyperref}
\hypersetup{draft=true}
\begin{document}\end{document}|})
        (tag ^ ": draft=true in hypersetup"));
  run "PKG-018 clean: usepackage{hyperref} no draft" (fun tag ->
      expect
        (does_not_fire "PKG-018"
           {|\documentclass{article}
\usepackage{hyperref}
\begin{document}\end{document}|})
        (tag ^ ": no draft option"));
  run "PKG-018 clean: no hyperref" (fun tag ->
      expect
        (does_not_fire "PKG-018"
           {|\documentclass{article}
\begin{document}\end{document}|})
        (tag ^ ": no hyperref"));

  (* ══════════════════════════════════════════════════════════════════════
     PKG-019: geometry margin < 1 cm
     ══════════════════════════════════════════════════════════════════════ *)
  run "PKG-019 fires: geometry margin=0.5cm" (fun tag ->
      expect
        (fires "PKG-019"
           {|\documentclass{article}
\geometry{margin=0.5cm}
\begin{document}\end{document}|})
        (tag ^ ": margin 0.5cm"));
  run "PKG-019 fires: geometry left=0.2cm" (fun tag ->
      expect
        (fires "PKG-019"
           {|\documentclass{article}
\geometry{left=0.2cm}
\begin{document}\end{document}|})
        (tag ^ ": left 0.2cm"));
  run "PKG-019 fires: geometry bottom=0cm" (fun tag ->
      expect
        (fires "PKG-019"
           {|\documentclass{article}
\geometry{bottom=0cm}
\begin{document}\end{document}|})
        (tag ^ ": bottom 0cm"));
  run "PKG-019 clean: geometry margin=2cm" (fun tag ->
      expect
        (does_not_fire "PKG-019"
           {|\documentclass{article}
\geometry{margin=2cm}
\begin{document}\end{document}|})
        (tag ^ ": margin 2cm ok"));
  run "PKG-019 clean: no geometry" (fun tag ->
      expect
        (does_not_fire "PKG-019"
           {|\documentclass{article}
\begin{document}\end{document}|})
        (tag ^ ": no geometry"));

  (* ══════════════════════════════════════════════════════════════════════
     FONT-005: fontspec fallback to Latin Modern
     ══════════════════════════════════════════════════════════════════════ *)
  run "FONT-005 fires: fontspec without setmainfont" (fun tag ->
      expect
        (fires "FONT-005"
           {|\documentclass{article}
\usepackage{fontspec}
\begin{document}\end{document}|})
        (tag ^ ": fontspec no setmainfont"));
  run "FONT-005 fires: fontspec + setmainfont{Latin Modern Roman}" (fun tag ->
      expect
        (fires "FONT-005"
           {|\documentclass{article}
\usepackage{fontspec}
\setmainfont{Latin Modern Roman}
\begin{document}\end{document}|})
        (tag ^ ": explicit Latin Modern"));
  run "FONT-005 clean: fontspec + setmainfont{TeX Gyre Termes}" (fun tag ->
      expect
        (does_not_fire "FONT-005"
           {|\documentclass{article}
\usepackage{fontspec}
\setmainfont{TeX Gyre Termes}
\begin{document}\end{document}|})
        (tag ^ ": non-LM font ok"));
  run "FONT-005 clean: no fontspec" (fun tag ->
      expect
        (does_not_fire "FONT-005"
           {|\documentclass{article}
\begin{document}\end{document}|})
        (tag ^ ": no fontspec"));

  (* ══════════════════════════════════════════════════════════════════════
     LAY-015: Line spacing < 1 or > 2
     ══════════════════════════════════════════════════════════════════════ *)
  run "LAY-015 fires: linespread{0.8}" (fun tag ->
      expect
        (fires "LAY-015"
           {|\documentclass{article}
\linespread{0.8}
\begin{document}\end{document}|})
        (tag ^ ": linespread 0.8"));
  run "LAY-015 fires: setstretch{3.0}" (fun tag ->
      expect
        (fires "LAY-015"
           {|\documentclass{article}
\usepackage{setspace}
\setstretch{3.0}
\begin{document}\end{document}|})
        (tag ^ ": setstretch 3.0"));
  run "LAY-015 fires: linespread{0.5}" (fun tag ->
      expect
        (fires "LAY-015"
           {|\documentclass{article}
\linespread{0.5}
\begin{document}\end{document}|})
        (tag ^ ": linespread 0.5"));
  run "LAY-015 clean: linespread{1.5}" (fun tag ->
      expect
        (does_not_fire "LAY-015"
           {|\documentclass{article}
\linespread{1.5}
\begin{document}\end{document}|})
        (tag ^ ": linespread 1.5 ok"));
  run "LAY-015 clean: no spacing commands" (fun tag ->
      expect
        (does_not_fire "LAY-015"
           {|\documentclass{article}
\begin{document}\end{document}|})
        (tag ^ ": no spacing commands"));

  (* ══════════════════════════════════════════════════════════════════════
     LAY-020: Float placement params modified
     ══════════════════════════════════════════════════════════════════════ *)
  run "LAY-020 fires: setcounter{topnumber}" (fun tag ->
      expect
        (fires "LAY-020"
           {|\documentclass{article}
\setcounter{topnumber}{2}
\begin{document}\end{document}|})
        (tag ^ ": setcounter topnumber"));
  run "LAY-020 fires: renewcommand topfraction" (fun tag ->
      expect
        (fires "LAY-020"
           {|\documentclass{article}
\renewcommand{\topfraction}{0.9}
\begin{document}\end{document}|})
        (tag ^ ": renewcommand topfraction"));
  run "LAY-020 fires: setcounter{bottomnumber}" (fun tag ->
      expect
        (fires "LAY-020"
           {|\documentclass{article}
\setcounter{bottomnumber}{1}
\begin{document}\end{document}|})
        (tag ^ ": setcounter bottomnumber"));
  run "LAY-020 clean: no float params" (fun tag ->
      expect
        (does_not_fire "LAY-020"
           {|\documentclass{article}
\begin{document}\end{document}|})
        (tag ^ ": no float params"));

  (* ══════════════════════════════════════════════════════════════════════
     LAY-022: Global negative parskip
     ══════════════════════════════════════════════════════════════════════ *)
  run "LAY-022 fires: negative parskip" (fun tag ->
      expect
        (fires "LAY-022"
           {|\documentclass{article}
\setlength{\parskip}{-3pt}
\begin{document}\end{document}|})
        (tag ^ ": negative parskip"));
  run "LAY-022 fires: negative parskip small" (fun tag ->
      expect
        (fires "LAY-022"
           {|\documentclass{article}
\setlength{\parskip}{-1mm}
\begin{document}\end{document}|})
        (tag ^ ": negative parskip -1mm"));
  run "LAY-022 clean: positive parskip" (fun tag ->
      expect
        (does_not_fire "LAY-022"
           {|\documentclass{article}
\setlength{\parskip}{6pt}
\begin{document}\end{document}|})
        (tag ^ ": positive parskip ok"));
  run "LAY-022 clean: no parskip" (fun tag ->
      expect
        (does_not_fire "LAY-022"
           {|\documentclass{article}
\begin{document}\end{document}|})
        (tag ^ ": no parskip"));

  (* ══════════════════════════════════════════════════════════════════════
     REF-008: Duplicate cite key in .bib file
     ══════════════════════════════════════════════════════════════════════ *)
  run "REF-008 fires: duplicate key" (fun tag ->
      expect
        (fires "REF-008"
           {|@article{samekey,
  author = {Smith, John}
}
@article{samekey,
  author = {Doe, Jane}
}|})
        (tag ^ ": duplicate samekey"));
  run "REF-008 fires: duplicate across types" (fun tag ->
      expect
        (fires "REF-008"
           {|@article{mykey,
  title = {Paper A}
}
@inproceedings{mykey,
  title = {Paper B}
}|})
        (tag ^ ": duplicate mykey across types"));
  run "REF-008 clean: unique keys" (fun tag ->
      expect
        (does_not_fire "REF-008"
           {|@article{key1,
  author = {Smith, John}
}
@article{key2,
  author = {Doe, Jane}
}|})
        (tag ^ ": unique keys ok"));
  run "REF-008 clean: single entry" (fun tag ->
      expect
        (does_not_fire "REF-008"
           {|@article{onlykey,
  author = {Smith, John}
}|})
        (tag ^ ": single entry ok"));

  (* ══════════════════════════════════════════════════════════════════════
     META-001: PDF /Producer not set
     ══════════════════════════════════════════════════════════════════════ *)
  run "META-001 fires: hyperref without pdfproducer" (fun tag ->
      expect
        (fires "META-001"
           {|\documentclass{article}
\usepackage{hyperref}
\begin{document}\end{document}|})
        (tag ^ ": hyperref no pdfproducer"));
  run "META-001 fires: hyperref with options, no pdfproducer" (fun tag ->
      expect
        (fires "META-001"
           {|\documentclass{article}
\usepackage[colorlinks=true]{hyperref}
\begin{document}\end{document}|})
        (tag ^ ": hyperref opts no pdfproducer"));
  run "META-001 clean: hyperref + pdfproducer" (fun tag ->
      expect
        (does_not_fire "META-001"
           {|\documentclass{article}
\usepackage{hyperref}
\hypersetup{pdfproducer=MyTool}
\begin{document}\end{document}|})
        (tag ^ ": hyperref + pdfproducer"));
  run "META-001 clean: no hyperref" (fun tag ->
      expect
        (does_not_fire "META-001"
           {|\documentclass{article}
\begin{document}\end{document}|})
        (tag ^ ": no hyperref"));

  (* ══════════════════════════════════════════════════════════════════════
     PDF-010: Bookmark text contains _ or # without texorpdfstring
     ══════════════════════════════════════════════════════════════════════ *)
  run "PDF-010 fires: section with underscore" (fun tag ->
      expect
        (fires "PDF-010"
           {|\documentclass{article}
\begin{document}
\section{A_B}
\end{document}|})
        (tag ^ ": section with _"));
  run "PDF-010 fires: subsection with hash" (fun tag ->
      expect
        (fires "PDF-010"
           {|\documentclass{article}
\begin{document}
\subsection{Item #1}
\end{document}|})
        (tag ^ ": subsection with #"));
  run "PDF-010 clean: section no special chars" (fun tag ->
      expect
        (does_not_fire "PDF-010"
           {|\documentclass{article}
\begin{document}
\section{Introduction}
\end{document}|})
        (tag ^ ": section clean text"));
  run "PDF-010 clean: texorpdfstring used" (fun tag ->
      expect
        (does_not_fire "PDF-010"
           {|\documentclass{article}
\begin{document}
\section{\texorpdfstring{A_B}{AB}}
\end{document}|})
        (tag ^ ": texorpdfstring used"));
  run "PDF-010 clean: no section commands" (fun tag ->
      expect
        (does_not_fire "PDF-010" {|Just plain text with _ and # chars.|})
        (tag ^ ": no section commands"));

  (* ══════════════════════════════════════════════════════════════════════
     TIKZ-005: TikZ externalisation not enabled
     ══════════════════════════════════════════════════════════════════════ *)
  run "TIKZ-005 fires: tikzpicture without external" (fun tag ->
      expect
        (fires "TIKZ-005"
           {|\documentclass{article}
\begin{document}
\begin{tikzpicture}
\draw (0,0) -- (1,1);
\end{tikzpicture}
\end{document}|})
        (tag ^ ": tikzpicture no external"));
  run "TIKZ-005 fires: multiple tikzpicture no external" (fun tag ->
      expect
        (fires "TIKZ-005"
           {|\begin{tikzpicture}
\draw (0,0) circle (1);
\end{tikzpicture}
\begin{tikzpicture}
\fill (0,0) rectangle (2,2);
\end{tikzpicture}|})
        (tag ^ ": two tikzpictures no external"));
  run "TIKZ-005 clean: usetikzlibrary{external}" (fun tag ->
      expect
        (does_not_fire "TIKZ-005"
           {|\usetikzlibrary{external}
\begin{tikzpicture}
\draw (0,0) -- (1,1);
\end{tikzpicture}|})
        (tag ^ ": external library loaded"));
  run "TIKZ-005 clean: tikzexternalize" (fun tag ->
      expect
        (does_not_fire "TIKZ-005"
           {|\tikzexternalize
\begin{tikzpicture}
\draw (0,0) -- (1,1);
\end{tikzpicture}|})
        (tag ^ ": tikzexternalize command"));
  run "TIKZ-005 clean: no tikzpicture" (fun tag ->
      expect
        (does_not_fire "TIKZ-005"
           {|\documentclass{article}
\begin{document}
Hello world.
\end{document}|})
        (tag ^ ": no tikzpicture"))

let () = finalise "l3-text-approx"
