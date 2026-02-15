(** Unit tests for L1 validator rules: MOD-001..013, MOD-020..024, and EXP-001. *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[l1] FAIL: %s\n%!" msg;
    incr fails)

let run msg f =
  incr cases;
  f msg

(* Helper: run all validators and find result for a specific rule ID *)
let find_result id src =
  let results = Validators.run_all src in
  List.find_opt (fun (r : Validators.result) -> r.id = id) results

let fires id src = find_result id src <> None
let does_not_fire id src = find_result id src = None

let () =
  (* ══════════════════════════════════════════════════════════════════════
     MOD-001: Legacy font commands (bf, it, tt, rm, sl, sf)
     ══════════════════════════════════════════════════════════════════════ *)
  run "MOD-001 fires on \\bf" (fun tag ->
      expect (fires "MOD-001" "{\\bf bold}") (tag ^ ": legacy bf"));
  run "MOD-001 fires on \\it" (fun tag ->
      expect (fires "MOD-001" "{\\it italic}") (tag ^ ": legacy it"));
  run "MOD-001 fires on \\tt" (fun tag ->
      expect (fires "MOD-001" "{\\tt mono}") (tag ^ ": legacy tt"));
  run "MOD-001 fires on \\rm" (fun tag ->
      expect (fires "MOD-001" "{\\rm roman}") (tag ^ ": legacy rm"));
  run "MOD-001 fires on \\sl" (fun tag ->
      expect (fires "MOD-001" "{\\sl slanted}") (tag ^ ": legacy sl"));
  run "MOD-001 fires on \\sf" (fun tag ->
      expect (fires "MOD-001" "{\\sf sans}") (tag ^ ": legacy sf"));
  run "MOD-001 clean" (fun tag ->
      expect
        (does_not_fire "MOD-001" "\\textbf{bold} \\emph{italic} \\texttt{mono}")
        (tag ^ ": modern commands ok"));

  (* ══════════════════════════════════════════════════════════════════════
     EXP-001: Incomplete expansion — catalogue commands still present (textbf,
     emph, section)
     ══════════════════════════════════════════════════════════════════════ *)
  run "EXP-001 fires on \\textbf" (fun tag ->
      expect (fires "EXP-001" "\\textbf{hello}") (tag ^ ": unexpanded textbf"));
  run "EXP-001 fires on \\emph" (fun tag ->
      expect (fires "EXP-001" "\\emph{world}") (tag ^ ": unexpanded emph"));
  run "EXP-001 fires on \\section" (fun tag ->
      expect (fires "EXP-001" "\\section{Title}") (tag ^ ": unexpanded section"));
  run "EXP-001 clean" (fun tag ->
      expect
        (does_not_fire "EXP-001" "Just plain text with no macros")
        (tag ^ ": no unexpanded commands"));

  (* ══════════════════════════════════════════════════════════════════════
     MOD-002: Mixed legacy (\bf) and modern (\textbf) in same paragraph
     ══════════════════════════════════════════════════════════════════════ *)
  run "MOD-002 fires on mixed bold" (fun tag ->
      expect
        (fires "MOD-002" "{\\bf part1} and \\textbf{part2}")
        (tag ^ ": mixed in paragraph"));
  run "MOD-002 clean only modern" (fun tag ->
      expect
        (does_not_fire "MOD-002" "\\textbf{x} and \\textbf{y}")
        (tag ^ ": consistent modern"));
  run "MOD-002 clean only legacy" (fun tag ->
      expect
        (does_not_fire "MOD-002" "{\\bf x} and {\\bf y}")
        (tag ^ ": consistent legacy"));

  (* ══════════════════════════════════════════════════════════════════════
     MOD-003: Mixed legacy (\it) and modern (\emph/\textit)
     ══════════════════════════════════════════════════════════════════════ *)
  run "MOD-003 fires on mixed italic" (fun tag ->
      expect
        (fires "MOD-003" "{\\it part1} and \\emph{part2}")
        (tag ^ ": mixed in paragraph"));
  run "MOD-003 fires with textit" (fun tag ->
      expect
        (fires "MOD-003" "{\\it part1} and \\textit{part2}")
        (tag ^ ": textit variant"));
  run "MOD-003 clean" (fun tag ->
      expect
        (does_not_fire "MOD-003" "\\emph{x} and \\emph{y}")
        (tag ^ ": consistent modern"));

  (* ══════════════════════════════════════════════════════════════════════
     MOD-004: Mixed legacy (\rm) and modern (\textrm)
     ══════════════════════════════════════════════════════════════════════ *)
  run "MOD-004 fires on mixed roman" (fun tag ->
      expect
        (fires "MOD-004" "{\\rm part1} and \\textrm{part2}")
        (tag ^ ": mixed in paragraph"));
  run "MOD-004 clean" (fun tag ->
      expect
        (does_not_fire "MOD-004" "\\textrm{x} and \\textrm{y}")
        (tag ^ ": consistent modern"));

  (* ══════════════════════════════════════════════════════════════════════
     MOD-005: Mixed legacy (\tt) and modern (\texttt)
     ══════════════════════════════════════════════════════════════════════ *)
  run "MOD-005 fires on mixed typewriter" (fun tag ->
      expect
        (fires "MOD-005" "{\\tt code} and \\texttt{code2}")
        (tag ^ ": mixed in paragraph"));
  run "MOD-005 clean" (fun tag ->
      expect
        (does_not_fire "MOD-005" "\\texttt{x} and \\texttt{y}")
        (tag ^ ": consistent modern"));

  (* ══════════════════════════════════════════════════════════════════════
     MOD-006: Mixed legacy (\sf) and modern (\textsf)
     ══════════════════════════════════════════════════════════════════════ *)
  run "MOD-006 fires on mixed sans" (fun tag ->
      expect
        (fires "MOD-006" "{\\sf sans} and \\textsf{sans2}")
        (tag ^ ": mixed in paragraph"));
  run "MOD-006 clean" (fun tag ->
      expect
        (does_not_fire "MOD-006" "\\textsf{x} and \\textsf{y}")
        (tag ^ ": consistent modern"));

  (* ══════════════════════════════════════════════════════════════════════
     MOD-007: Mixed legacy (\sc) and modern (\textsc)
     ══════════════════════════════════════════════════════════════════════ *)
  run "MOD-007 fires on mixed small-caps" (fun tag ->
      expect
        (fires "MOD-007" "{\\sc caps} and \\textsc{caps2}")
        (tag ^ ": mixed in paragraph"));
  run "MOD-007 clean" (fun tag ->
      expect
        (does_not_fire "MOD-007" "\\textsc{x} and \\textsc{y}")
        (tag ^ ": consistent modern"));

  (* ══════════════════════════════════════════════════════════════════════
     MOD-008: Mixed NFSS \bfseries and inline \textbf
     ══════════════════════════════════════════════════════════════════════ *)
  run "MOD-008 fires on mixed bfseries/textbf" (fun tag ->
      expect
        (fires "MOD-008" "{\\bfseries bold} and \\textbf{bold2}")
        (tag ^ ": mixed in paragraph"));
  run "MOD-008 clean" (fun tag ->
      expect
        (does_not_fire "MOD-008" "\\textbf{x} and \\textbf{y}")
        (tag ^ ": consistent inline"));

  (* ══════════════════════════════════════════════════════════════════════
     MOD-009: Mixed NFSS \itshape and inline \textit/\emph
     ══════════════════════════════════════════════════════════════════════ *)
  run "MOD-009 fires on mixed itshape/emph" (fun tag ->
      expect
        (fires "MOD-009" "{\\itshape italic} and \\emph{italic2}")
        (tag ^ ": mixed in paragraph"));
  run "MOD-009 fires on itshape/textit" (fun tag ->
      expect
        (fires "MOD-009" "{\\itshape italic} and \\textit{italic2}")
        (tag ^ ": textit variant"));
  run "MOD-009 clean" (fun tag ->
      expect
        (does_not_fire "MOD-009" "\\emph{x} and \\emph{y}")
        (tag ^ ": consistent inline"));

  (* ══════════════════════════════════════════════════════════════════════
     MOD-010: Mixed NFSS \sffamily and inline \textsf
     ══════════════════════════════════════════════════════════════════════ *)
  run "MOD-010 fires on mixed sffamily/textsf" (fun tag ->
      expect
        (fires "MOD-010" "{\\sffamily sans} and \\textsf{sans2}")
        (tag ^ ": mixed in paragraph"));
  run "MOD-010 clean" (fun tag ->
      expect
        (does_not_fire "MOD-010" "\\textsf{x} and \\textsf{y}")
        (tag ^ ": consistent inline"));

  (* ══════════════════════════════════════════════════════════════════════
     MOD-011: Mixed NFSS \ttfamily and inline \texttt
     ══════════════════════════════════════════════════════════════════════ *)
  run "MOD-011 fires on mixed ttfamily/texttt" (fun tag ->
      expect
        (fires "MOD-011" "{\\ttfamily mono} and \\texttt{mono2}")
        (tag ^ ": mixed in paragraph"));
  run "MOD-011 clean" (fun tag ->
      expect
        (does_not_fire "MOD-011" "\\texttt{x} and \\texttt{y}")
        (tag ^ ": consistent inline"));

  (* ══════════════════════════════════════════════════════════════════════
     MOD-012: Mixed NFSS \rmfamily and inline \textrm
     ══════════════════════════════════════════════════════════════════════ *)
  run "MOD-012 fires on mixed rmfamily/textrm" (fun tag ->
      expect
        (fires "MOD-012" "{\\rmfamily roman} and \\textrm{roman2}")
        (tag ^ ": mixed in paragraph"));
  run "MOD-012 clean" (fun tag ->
      expect
        (does_not_fire "MOD-012" "\\textrm{x} and \\textrm{y}")
        (tag ^ ": consistent inline"));

  (* ══════════════════════════════════════════════════════════════════════
     MOD-013: Mixed NFSS \scshape and inline \textsc
     ══════════════════════════════════════════════════════════════════════ *)
  run "MOD-013 fires on mixed scshape/textsc" (fun tag ->
      expect
        (fires "MOD-013" "{\\scshape caps} and \\textsc{caps2}")
        (tag ^ ": mixed in paragraph"));
  run "MOD-013 clean" (fun tag ->
      expect
        (does_not_fire "MOD-013" "\\textsc{x} and \\textsc{y}")
        (tag ^ ": consistent inline"));

  (* ══════════════════════════════════════════════════════════════════════
     MOD-020: Global mix of bfseries and textbf across paragraphs
     ══════════════════════════════════════════════════════════════════════ *)
  run "MOD-020 fires on global mix" (fun tag ->
      expect
        (fires "MOD-020"
           "{\\bfseries bold here}\n\nAnother paragraph with \\textbf{bold}")
        (tag ^ ": cross-paragraph mix"));
  run "MOD-020 clean consistent" (fun tag ->
      expect
        (does_not_fire "MOD-020" "\\textbf{x}\n\n\\textbf{y}")
        (tag ^ ": consistent textbf"));

  (* ══════════════════════════════════════════════════════════════════════
     MOD-021: Global mix of itshape and textit/emph across paragraphs
     ══════════════════════════════════════════════════════════════════════ *)
  run "MOD-021 fires on global mix" (fun tag ->
      expect
        (fires "MOD-021" "{\\itshape italic}\n\n\\emph{emphasis}")
        (tag ^ ": cross-paragraph mix"));
  run "MOD-021 clean consistent" (fun tag ->
      expect
        (does_not_fire "MOD-021" "\\emph{x}\n\n\\emph{y}")
        (tag ^ ": consistent emph"));

  (* ══════════════════════════════════════════════════════════════════════
     MOD-022: Global mix of rmfamily and textrm across paragraphs
     ══════════════════════════════════════════════════════════════════════ *)
  run "MOD-022 fires on global mix" (fun tag ->
      expect
        (fires "MOD-022" "{\\rmfamily roman}\n\n\\textrm{roman2}")
        (tag ^ ": cross-paragraph mix"));
  run "MOD-022 clean consistent" (fun tag ->
      expect
        (does_not_fire "MOD-022" "\\textrm{x}\n\n\\textrm{y}")
        (tag ^ ": consistent textrm"));

  (* ══════════════════════════════════════════════════════════════════════
     MOD-023: Global mix of sffamily and textsf across paragraphs
     ══════════════════════════════════════════════════════════════════════ *)
  run "MOD-023 fires on global mix" (fun tag ->
      expect
        (fires "MOD-023" "{\\sffamily sans}\n\n\\textsf{sans2}")
        (tag ^ ": cross-paragraph mix"));
  run "MOD-023 clean consistent" (fun tag ->
      expect
        (does_not_fire "MOD-023" "\\textsf{x}\n\n\\textsf{y}")
        (tag ^ ": consistent textsf"));

  (* ══════════════════════════════════════════════════════════════════════
     MOD-024: Global mix of ttfamily and texttt across paragraphs
     ══════════════════════════════════════════════════════════════════════ *)
  run "MOD-024 fires on global mix" (fun tag ->
      expect
        (fires "MOD-024" "{\\ttfamily mono}\n\n\\texttt{mono2}")
        (tag ^ ": cross-paragraph mix"));
  run "MOD-024 clean consistent" (fun tag ->
      expect
        (does_not_fire "MOD-024" "\\texttt{x}\n\n\\texttt{y}")
        (tag ^ ": consistent texttt"));

  (* ══════════════════════════════════════════════════════════════════════ MOD
     paragraph edge cases — single paragraph should not trigger cross-paragraph
     rules (MOD-020..024), but should trigger in-paragraph rules (MOD-002..013).
     ══════════════════════════════════════════════════════════════════════ *)

  (* MOD-020: has_global_mixing is document-wide (not paragraph-aware), so it
     fires even when both styles are in the same paragraph *)
  run "MOD-020 fires even in single paragraph" (fun tag ->
      expect
        (fires "MOD-020" "{\\bfseries bold} and \\textbf{bold2}")
        (tag ^ ": global check fires on any co-occurrence"));
  (* MOD-020 does NOT fire when only one style is present *)
  run "MOD-020 does not fire on bfseries-only" (fun tag ->
      expect
        (does_not_fire "MOD-020" "{\\bfseries bold} and {\\bfseries more}")
        (tag ^ ": no mixing"));

  (* MOD-021: same global behavior *)
  run "MOD-021 fires even in single paragraph" (fun tag ->
      expect
        (fires "MOD-021" "{\\itshape italic} and \\emph{italic2}")
        (tag ^ ": global check fires on any co-occurrence"));
  run "MOD-021 does not fire on itshape-only" (fun tag ->
      expect
        (does_not_fire "MOD-021" "{\\itshape x} and {\\itshape y}")
        (tag ^ ": no mixing"));

  (* MOD-002 does NOT fire across paragraphs with clean paragraphs *)
  run "MOD-002 does not fire when each paragraph is consistent" (fun tag ->
      expect
        (does_not_fire "MOD-002" "{\\bf bold only}\n\n\\textbf{modern only}")
        (tag ^ ": separate paragraphs, each consistent"));

  (* MOD-008 does NOT fire when bfseries only (no textbf) in paragraph *)
  run "MOD-008 does not fire on bfseries-only paragraph" (fun tag ->
      expect
        (does_not_fire "MOD-008" "{\\bfseries this} and {\\bfseries that}")
        (tag ^ ": consistent bfseries only"));

  (* MOD-009 does NOT fire when itshape-only paragraph *)
  run "MOD-009 does not fire on itshape-only paragraph" (fun tag ->
      expect
        (does_not_fire "MOD-009" "{\\itshape this} and {\\itshape that}")
        (tag ^ ": consistent itshape only"));

  (* Three-paragraph scenario: first legacy, second clean, third modern *)
  run "MOD-020 fires across non-adjacent paragraphs" (fun tag ->
      expect
        (fires "MOD-020"
           "{\\bfseries bold}\n\nClean paragraph here\n\n\\textbf{modern}")
        (tag ^ ": non-adjacent paragraphs still fire"));

  (* EXP-001 does not fire when only bfseries (not textbf) *)
  run "EXP-001 does not fire on bfseries" (fun tag ->
      expect
        (does_not_fire "EXP-001" "{\\bfseries bold}")
        (tag ^ ": bfseries is not textbf"));

  (* EXP-001 fires when both textbf and emph are present *)
  run "EXP-001 fires with both textbf and emph" (fun tag ->
      expect
        (fires "EXP-001" "\\textbf{hello} and \\emph{world}")
        (tag ^ ": both unexpanded"));

  (* ══════════════════════════════════════════════════════════════════════
     Multi-paragraph MOD rules — edge cases with blank-line paragraphs
     ══════════════════════════════════════════════════════════════════════ *)

  (* Empty paragraphs separate content — MOD-002 checks per-paragraph mixing, so
     legacy in one paragraph and modern in another does NOT fire MOD-002 *)
  run "MOD-002 does not fire when styles are in separate paragraphs" (fun tag ->
      expect
        (does_not_fire "MOD-002" "{\\bf bold}\n\n\n\\textbf{modern}")
        (tag ^ ": separate paragraphs, no per-paragraph mixing"));

  (* MOD-001 fires even when legacy command is deeply nested *)
  run "MOD-001 fires on nested legacy" (fun tag ->
      expect
        (fires "MOD-001" "\\begin{quote}{\\sf nested sans}\\end{quote}")
        (tag ^ ": nested legacy"));

  (* ══════════════════════════════════════════════════════════════════════
     Integration: realistic LaTeX with L1 issues
     ══════════════════════════════════════════════════════════════════════ *)
  run "Integration: realistic LaTeX with L1 issues" (fun tag ->
      let doc =
        "\\documentclass{article}\n\
         \\begin{document}\n\n\
         {\\bf Introduction}\n\n\
         This is \\textbf{important} text. See \\emph{details} below.\n\n\
         \\subsubsection{Deep Section}\n\n\
         More \\textbf{content} here.\n\n\
         \\end{document}\n"
      in
      let results = Validators.run_all doc in
      let has id =
        List.exists (fun (r : Validators.result) -> r.id = id) results
      in
      (* MOD-001: \bf is a legacy font command *)
      expect (has "MOD-001") (tag ^ ": MOD-001 fires on \\bf");
      (* EXP-001: \textbf and \emph still present *)
      expect (has "EXP-001") (tag ^ ": EXP-001 fires on unexpanded"));

  run "Integration: clean modern LaTeX — no L1 issues" (fun tag ->
      let doc =
        "\\documentclass{article}\n\
         \\begin{document}\n\n\
         \\section{Introduction}\n\n\
         This is well-formatted text with no issues.\n\n\
         \\subsection{Details}\n\n\
         More content here.\n\n\
         \\end{document}\n"
      in
      let results = Validators.run_all doc in
      let l1_issues =
        List.filter
          (fun (r : Validators.result) ->
            let id = r.id in
            (String.length id >= 4 && String.sub id 0 4 = "CMD-")
            || (String.length id >= 4 && String.sub id 0 4 = "MOD-"))
          results
      in
      expect (l1_issues = []) (tag ^ ": clean modern LaTeX, no CMD/MOD"));

  (* ══════════════════════════════════════════════════════════════════════
     Layer dispatch for L1 rules
     ══════════════════════════════════════════════════════════════════════ *)
  run "MOD layer is L1" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "MOD-001" = L1)
        (tag ^ ": MOD -> L1"));
  run "EXP layer is L1" (fun tag ->
      expect
        (Validators.precondition_of_rule_id "EXP-001" = L1)
        (tag ^ ": EXP -> L1"));

  (* ══════════════════════════════════════════════════════════════════════ Edge
     cases
     ══════════════════════════════════════════════════════════════════════ *)
  run "Empty input — no L1 fires" (fun tag ->
      let results = Validators.run_all "" in
      let l1_results =
        List.filter
          (fun (r : Validators.result) ->
            let id = r.id in
            (String.length id >= 4 && String.sub id 0 4 = "CMD-")
            || (String.length id >= 4 && String.sub id 0 4 = "MOD-")
            || (String.length id >= 4 && String.sub id 0 4 = "EXP-"))
          results
      in
      expect (l1_results = []) (tag ^ ": empty input, no L1"));

  run "Clean LaTeX — only EXP-001 may fire" (fun tag ->
      let clean =
        "\\documentclass{article}\n\
         \\begin{document}\n\
         Hello world.\n\
         \\end{document}\n"
      in
      let results = Validators.run_all clean in
      let cmd_mod =
        List.filter
          (fun (r : Validators.result) ->
            let id = r.id in
            (String.length id >= 4 && String.sub id 0 4 = "CMD-")
            || (String.length id >= 4 && String.sub id 0 4 = "MOD-"))
          results
      in
      expect (cmd_mod = []) (tag ^ ": clean LaTeX, no CMD/MOD"));

  (* ══════════════════════════════════════════════════════════════════════ Done
     ══════════════════════════════════════════════════════════════════════ *)
  if !fails > 0 then (
    Printf.eprintf "[l1] %d FAILURES in %d cases\n%!" !fails !cases;
    exit 1)
  else Printf.printf "[l1] PASS %d cases\n%!" !cases
