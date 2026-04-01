(** Unit tests for Phase 3-5 L2-approximable rules: 28 rules.
    BIB-001/007/013/014/017, FONT-002/003/009/010/011/012/013, RTL-001/002,
    META-003/004, DOC-005, REF-012, PDF-005, CJK-009/011/013,
    LANG-005/008/009/010, CHEM-010. ~84 total test cases. *)

open Test_helpers

let () =
  Unix.putenv "L0_VALIDATORS" "pilot";

  (* ══════════════════════════════════════════════════════════════════════
     BIB-001: Entry missing DOI or ISBN/ISSN
     ══════════════════════════════════════════════════════════════════════ *)
  run "BIB-001 fires: no doi/isbn" (fun tag ->
      expect
        (fires "BIB-001"
           {|@article{key1,
  author = {Smith, John},
  title = {A Paper},
  year = {2020}
}|})
        (tag ^ ": missing doi/isbn"));
  run "BIB-001 clean: has doi" (fun tag ->
      expect
        (does_not_fire "BIB-001"
           {|@article{key1,
  author = {Smith, John},
  doi = {10.1234/foo}
}|})
        (tag ^ ": has doi"));
  run "BIB-001 clean: has isbn" (fun tag ->
      expect
        (does_not_fire "BIB-001"
           {|@book{key1,
  author = {Smith, John},
  isbn = {978-0-123-45678-9}
}|})
        (tag ^ ": has isbn"));

  (* ══════════════════════════════════════════════════════════════════════
     BIB-007: Duplicate DOI across entries
     ══════════════════════════════════════════════════════════════════════ *)
  run "BIB-007 fires: dup doi" (fun tag ->
      expect
        (fires "BIB-007"
           {|@article{key1,
  doi = {10.1234/foo}
}
@article{key2,
  doi = {10.1234/foo}
}|})
        (tag ^ ": duplicate doi"));
  run "BIB-007 clean: unique dois" (fun tag ->
      expect
        (does_not_fire "BIB-007"
           {|@article{key1,
  doi = {10.1234/foo}
}
@article{key2,
  doi = {10.5678/bar}
}|})
        (tag ^ ": unique dois"));

  (* ══════════════════════════════════════════════════════════════════════
     BIB-013: Title capitalisation incorrect
     ══════════════════════════════════════════════════════════════════════ *)
  run "BIB-013 fires: over-capitalised title" (fun tag ->
      expect
        (fires "BIB-013"
           {|@article{key1,
  title = {A Study Of The Impact Of Machine Learning On Natural Language}
}|})
        (tag ^ ": over-capitalised"));
  run "BIB-013 clean: sentence case" (fun tag ->
      expect
        (does_not_fire "BIB-013"
           {|@article{key1,
  title = {A study of machine learning}
}|})
        (tag ^ ": sentence case"));

  (* ══════════════════════════════════════════════════════════════════════
     BIB-014: Duplicate author-year key
     ══════════════════════════════════════════════════════════════════════ *)
  run "BIB-014 fires: dup author+year" (fun tag ->
      expect
        (fires "BIB-014"
           {|@article{key1,
  author = {Smith, John},
  year = {2020}
}
@article{key2,
  author = {Smith, John},
  year = {2020}
}|})
        (tag ^ ": dup author+year"));
  run "BIB-014 clean: different years" (fun tag ->
      expect
        (does_not_fire "BIB-014"
           {|@article{key1,
  author = {Smith, John},
  year = {2020}
}
@article{key2,
  author = {Smith, John},
  year = {2021}
}|})
        (tag ^ ": different years"));

  (* ══════════════════════════════════════════════════════════════════════
     BIB-017: Title ends with punctuation
     ══════════════════════════════════════════════════════════════════════ *)
  run "BIB-017 fires: title with period" (fun tag ->
      expect
        (fires "BIB-017" {|@article{key1,
  title = {A study of effects.}
}|})
        (tag ^ ": title ending period"));
  run "BIB-017 clean: no trailing punct" (fun tag ->
      expect
        (does_not_fire "BIB-017"
           {|@article{key1,
  title = {A study of effects}
}|})
        (tag ^ ": no trailing punct"));

  (* ══════════════════════════════════════════════════════════════════════
     FONT-002: Mixed optical sizes
     ══════════════════════════════════════════════════════════════════════ *)
  run "FONT-002 fires: many sizes" (fun tag ->
      expect
        (fires "FONT-002"
           {|\fontsize{8}{10}\selectfont Small
\fontsize{12}{14}\selectfont Normal
\fontsize{20}{24}\selectfont Large|})
        (tag ^ ": 3 font sizes"));
  run "FONT-002 clean: no fontsize" (fun tag ->
      expect
        (does_not_fire "FONT-002" "Normal text without fontsize commands.")
        (tag ^ ": no fontsize"));

  (* ══════════════════════════════════════════════════════════════════════
     FONT-003: Microtype protrusion disabled
     ══════════════════════════════════════════════════════════════════════ *)
  run "FONT-003 fires: protrusion=false" (fun tag ->
      expect
        (fires "FONT-003" {|\usepackage[protrusion=false]{microtype}|})
        (tag ^ ": protrusion disabled"));
  run "FONT-003 clean: default microtype" (fun tag ->
      expect
        (does_not_fire "FONT-003" {|\usepackage{microtype}|})
        (tag ^ ": default microtype"));

  (* ══════════════════════════════════════════════════════════════════════
     FONT-009: Small-caps with non-ASCII
     ══════════════════════════════════════════════════════════════════════ *)
  run "FONT-009 fires: textsc with UTF-8" (fun tag ->
      expect
        (fires "FONT-009" "\\textsc{caf\xc3\xa9}")
        (tag ^ ": textsc with e-acute"));
  run "FONT-009 clean: ASCII textsc" (fun tag ->
      expect (does_not_fire "FONT-009" {|\textsc{hello}|}) (tag ^ ": ASCII only"));

  (* ══════════════════════════════════════════════════════════════════════
     FONT-010: Digits in \textsc
     ══════════════════════════════════════════════════════════════════════ *)
  run "FONT-010 fires: digits in textsc" (fun tag ->
      expect (fires "FONT-010" {|\textsc{ABC123}|}) (tag ^ ": digits in textsc"));
  run "FONT-010 clean: letters only" (fun tag ->
      expect (does_not_fire "FONT-010" {|\textsc{ABC}|}) (tag ^ ": letters only"));

  (* ══════════════════════════════════════════════════════════════════════
     FONT-011: Microtype + math font mismatch
     ══════════════════════════════════════════════════════════════════════ *)
  run "FONT-011 fires: microtype + setmathfont" (fun tag ->
      expect
        (fires "FONT-011" {|\usepackage{microtype}
\setmathfont{XITS Math}|})
        (tag ^ ": microtype + setmathfont"));
  run "FONT-011 clean: no math font" (fun tag ->
      expect
        (does_not_fire "FONT-011" {|\usepackage{microtype}|})
        (tag ^ ": no math font"));

  (* ══════════════════════════════════════════════════════════════════════
     FONT-012: Ligature adjacent to \texttt
     ══════════════════════════════════════════════════════════════════════ *)
  run "FONT-012 fires: ff after texttt" (fun tag ->
      expect (fires "FONT-012" {|\texttt{code}ff|}) (tag ^ ": ff after texttt"));
  run "FONT-012 clean: no ligature" (fun tag ->
      expect
        (does_not_fire "FONT-012" {|\texttt{code} and text|})
        (tag ^ ": no ligature"));

  (* ══════════════════════════════════════════════════════════════════════
     FONT-013: Mixed proportional/tabular figures
     ══════════════════════════════════════════════════════════════════════ *)
  run "FONT-013 fires: mixed figures" (fun tag ->
      expect
        (fires "FONT-013"
           {|\begin{tabular}{ll}
\proportional 123 & \tabularfigures 456
\end{tabular}|})
        (tag ^ ": mixed figure types"));
  run "FONT-013 clean: no tabular" (fun tag ->
      expect
        (does_not_fire "FONT-013" "Normal text without tables.")
        (tag ^ ": no tabular"));

  (* ══════════════════════════════════════════════════════════════════════
     RTL-001: Mixed RTL/LTR digits
     ══════════════════════════════════════════════════════════════════════ *)
  run "RTL-001 fires: mixed digits" (fun tag ->
      (* Arabic-Indic digit 0 = U+0660 = D9 A0, followed by ASCII 5 *)
      expect
        (fires "RTL-001" ("Price: \xd9\xa0" ^ "5 items"))
        (tag ^ ": Arabic-Indic + ASCII digits"));
  run "RTL-001 clean: ASCII only" (fun tag ->
      expect (does_not_fire "RTL-001" "Price: 50 items") (tag ^ ": ASCII only"));

  (* ══════════════════════════════════════════════════════════════════════
     RTL-002: Missing \textLR around Latin in Arabic
     ══════════════════════════════════════════════════════════════════════ *)
  run "RTL-002 fires: Latin after Arabic" (fun tag ->
      (* Arabic letter ba = U+0628 = D8 A8, space, ASCII uppercase *)
      expect (fires "RTL-002" "\xd8\xa8 A test") (tag ^ ": Latin after Arabic"));
  run "RTL-002 clean: with textLR" (fun tag ->
      expect
        (does_not_fire "RTL-002" "\xd8\xa8 \\textLR{A test}")
        (tag ^ ": with textLR"));

  (* ══════════════════════════════════════════════════════════════════════
     META-003: Build timestamp not reproducible
     ══════════════════════════════════════════════════════════════════════ *)
  run "META-003 fires: date today" (fun tag ->
      expect (fires "META-003" {|\date{\today}|}) (tag ^ ": date today"));
  run "META-003 clean: fixed date" (fun tag ->
      expect
        (does_not_fire "META-003" {|\date{2026-04-01}|})
        (tag ^ ": fixed date"));

  (* ══════════════════════════════════════════════════════════════════════
     META-004: PDF CreationDate not stripped
     ══════════════════════════════════════════════════════════════════════ *)
  run "META-004 fires: CreationDate in pdfinfo" (fun tag ->
      expect
        (fires "META-004" {|\pdfinfo{/CreationDate (D:20260401)}|})
        (tag ^ ": CreationDate present"));
  run "META-004 clean: no pdfinfo" (fun tag ->
      expect (does_not_fire "META-004" "Normal document.") (tag ^ ": no pdfinfo"));

  (* ══════════════════════════════════════════════════════════════════════
     DOC-005: \keywords present but no pdfkeywords
     ══════════════════════════════════════════════════════════════════════ *)
  run "DOC-005 fires: keywords without pdf" (fun tag ->
      expect
        (fires "DOC-005"
           {|\keywords{machine learning, NLP}
\hypersetup{pdftitle={Paper}}|})
        (tag ^ ": keywords no pdfkeywords"));
  run "DOC-005 clean: has pdfkeywords" (fun tag ->
      expect
        (does_not_fire "DOC-005" {|\keywords{ML}
\hypersetup{pdfkeywords={ML}}|})
        (tag ^ ": has pdfkeywords"));

  (* ══════════════════════════════════════════════════════════════════════
     REF-012: above/below contradicts float
     ══════════════════════════════════════════════════════════════════════ *)
  run "REF-012 fires: above ref" (fun tag ->
      expect
        (fires "REF-012" "As shown above \\ref{fig:1} we see this.")
        (tag ^ ": above + ref"));
  run "REF-012 clean: no above/below" (fun tag ->
      expect
        (does_not_fire "REF-012" "As shown in \\ref{fig:1} we see this.")
        (tag ^ ": no above/below"));

  (* ══════════════════════════════════════════════════════════════════════
     PDF-005: PDF/A compliance flag missing
     ══════════════════════════════════════════════════════════════════════ *)
  run "PDF-005 fires: hyperref no pdfa" (fun tag ->
      expect
        (fires "PDF-005" {|\usepackage{hyperref}|})
        (tag ^ ": hyperref no pdfa"));
  run "PDF-005 clean: has DocumentMetadata" (fun tag ->
      expect
        (does_not_fire "PDF-005"
           {|\DocumentMetadata{pdfstandard=a-2b}
\usepackage{hyperref}|})
        (tag ^ ": has DocumentMetadata"));

  (* ══════════════════════════════════════════════════════════════════════
     CJK-009: Western space between CJK glyphs
     ══════════════════════════════════════════════════════════════════════ *)
  run "CJK-009 fires: space between CJK" (fun tag ->
      (* Two CJK chars with space: U+4E2D = E4 B8 AD, space, U+6587 = E6 96
         87 *)
      expect
        (fires "CJK-009" "\xe4\xb8\xad \xe6\x96\x87")
        (tag ^ ": space between CJK"));
  run "CJK-009 clean: no CJK" (fun tag ->
      expect (does_not_fire "CJK-009" "Normal English text.") (tag ^ ": no CJK"));

  (* ══════════════════════════════════════════════════════════════════════
     CJK-011: Prolonged-sound mark at line start
     ══════════════════════════════════════════════════════════════════════ *)
  run "CJK-011 fires: prolonged at start" (fun tag ->
      (* U+30FC = E3 83 BC *)
      expect
        (fires "CJK-011" "\xe3\x83\xbc\xe3\x82\xa2")
        (tag ^ ": prolonged mark at line start"));
  run "CJK-011 clean: no prolonged" (fun tag ->
      expect
        (does_not_fire "CJK-011" "Normal text")
        (tag ^ ": no prolonged mark"));

  (* ══════════════════════════════════════════════════════════════════════
     CJK-013: Full stop at line start
     ══════════════════════════════════════════════════════════════════════ *)
  run "CJK-013 fires: full stop at start" (fun tag ->
      (* U+3002 = E3 80 82 *)
      expect
        (fires "CJK-013" "\xe3\x80\x82\xe4\xb8\xad")
        (tag ^ ": full stop at line start"));
  run "CJK-013 clean: no full stop" (fun tag ->
      expect
        (does_not_fire "CJK-013" "Normal text")
        (tag ^ ": no full stop at start"));

  (* ══════════════════════════════════════════════════════════════════════
     LANG-005: Hyphen-penalty too low
     ══════════════════════════════════════════════════════════════════════ *)
  run "LANG-005 fires: penalty 10" (fun tag ->
      expect (fires "LANG-005" {|\hyphenpenalty=10|}) (tag ^ ": penalty 10"));
  run "LANG-005 clean: penalty 200" (fun tag ->
      expect
        (does_not_fire "LANG-005" {|\hyphenpenalty=200|})
        (tag ^ ": penalty 200"));

  (* ══════════════════════════════════════════════════════════════════════
     LANG-008: Spell-checker mismatch
     ══════════════════════════════════════════════════════════════════════ *)
  run "LANG-008 fires: babel/spelling mismatch" (fun tag ->
      expect
        (fires "LANG-008" {|\usepackage[english]{babel}
\setspelling{french}|})
        (tag ^ ": babel english, spelling french"));
  run "LANG-008 clean: matching" (fun tag ->
      expect
        (does_not_fire "LANG-008"
           {|\usepackage[english]{babel}
\setspelling{english}|})
        (tag ^ ": matching"));

  (* ══════════════════════════════════════════════════════════════════════
     LANG-009: Ragged-right in non-Latin
     ══════════════════════════════════════════════════════════════════════ *)
  run "LANG-009 fires: raggedright with CJK" (fun tag ->
      expect
        (fires "LANG-009" {|\usepackage{xeCJK}
\raggedright|})
        (tag ^ ": raggedright + CJK"));
  run "LANG-009 clean: no raggedright" (fun tag ->
      expect
        (does_not_fire "LANG-009" {|\usepackage{xeCJK}|})
        (tag ^ ": no raggedright"));

  (* ══════════════════════════════════════════════════════════════════════
     LANG-010: Arabic digits not localised
     ══════════════════════════════════════════════════════════════════════ *)
  run "LANG-010 fires: arabic with ASCII digits" (fun tag ->
      expect
        (fires "LANG-010"
           {|\setdefaultlanguage{arabic}
The year 2026 is important.|})
        (tag ^ ": arabic + ASCII digits"));
  run "LANG-010 clean: no arabic" (fun tag ->
      expect
        (does_not_fire "LANG-010" "English text with 2026.")
        (tag ^ ": no arabic lang"));

  (* ══════════════════════════════════════════════════════════════════════
     CHEM-010: Reaction scheme line > 120 chars
     ══════════════════════════════════════════════════════════════════════ *)
  run "CHEM-010 fires: long reaction" (fun tag ->
      let long_line = String.make 130 'A' in
      expect
        (fires "CHEM-010"
           ("\\begin{reaction}\n" ^ long_line ^ "\n\\end{reaction}"))
        (tag ^ ": long reaction line"));
  run "CHEM-010 clean: short reaction" (fun tag ->
      expect
        (does_not_fire "CHEM-010"
           "\\begin{reaction}\nH2O -> H+ + OH-\n\\end{reaction}")
        (tag ^ ": short reaction"));

  finalise "phase3"
