(** Unit tests for the Bucket-C CANDIDATE fix infrastructure.

    Candidate fixes are intent-dependent suggestions surfaced for author review
    (via [--list-candidate-fixes]) and NEVER auto-applied by [--apply-fixes].
    These tests assert that:
    - REF-006 and PKG-022 attach candidate fixes with the right labels/edits;
    - the same candidates are what the CLI's [--list-candidate-fixes] prints (it
      reads [candidate_fixes] off [run_all_with_class_d]);
    - attaching candidates does NOT change the run_all diagnostics (count);
    - candidate fixes are absent from the [fix] field, so [--apply-fixes] (which
      only applies [fix]) leaves them alone. *)

open Latex_parse_lib
open Test_helpers

(* [candidates_of id src] returns the candidate_fixes attached to rule [id] on
   [src], via the SAME entry point the CLI uses ([run_all_with_class_d]). *)
let candidates_of id src =
  let results = Validators.run_all_with_class_d src in
  match List.find_opt (fun (r : Validators.result) -> r.id = id) results with
  | Some r -> r.candidate_fixes
  | None -> []

let has_label id src label =
  List.exists
    (fun (c : Validators.candidate_fix) -> c.c_label = label)
    (candidates_of id src)

let edit_of_label id src label =
  match
    List.find_opt
      (fun (c : Validators.candidate_fix) -> c.c_label = label)
      (candidates_of id src)
  with
  | Some { c_edits = [ e ]; _ } ->
      Some
        (e.Cst_edit.start_offset, e.Cst_edit.end_offset, e.Cst_edit.replacement)
  | _ -> None

let () =
  (* ══════════════════════════════════════════════════════════════════════
     REF-006: \ref used where \pageref (page number) is intended
     ══════════════════════════════════════════════════════════════════════ *)
  let ref_src = "See page \\ref{sec:intro} for details." in
  run "REF-006 still fires (diagnostic unchanged)" (fun tag ->
      expect (fires_with_count "REF-006" ref_src 1) (tag ^ ": count=1"));
  run "REF-006 emits a candidate" (fun tag ->
      expect
        (has_label "REF-006" ref_src
           "Use \\pageref (page number) instead of \\ref")
        (tag ^ ": candidate label"));
  run "REF-006 candidate edit replaces \\ref{ with \\pageref{" (fun tag ->
      (* "See page " = 9 bytes, then "\ref{" spans [9,14). *)
      expect
        (edit_of_label "REF-006" ref_src
           "Use \\pageref (page number) instead of \\ref"
        = Some (9, 14, "\\pageref{"))
        (tag ^ ": edit"));
  run "REF-006 candidate NOT in fix field (no auto-apply)" (fun tag ->
      expect (not (fires_with_fix "REF-006" ref_src)) (tag ^ ": fix=None"));
  run "REF-006 --apply-fixes leaves \\ref untouched" (fun tag ->
      expect (apply_fix "REF-006" ref_src = ref_src) (tag ^ ": no rewrite"));
  run "REF-006 candidate dropped inside verbatim" (fun tag ->
      (* A page \ref inside verbatim must not get a candidate (exempt range). *)
      let v = "\\begin{verbatim}\npage \\ref{x}\n\\end{verbatim}" in
      expect (candidates_of "REF-006" v = []) (tag ^ ": exempt"));

  (* ══════════════════════════════════════════════════════════════════════
     PKG-022: obsolete package with a modern successor
     ══════════════════════════════════════════════════════════════════════ *)
  let pkg_src = "\\usepackage{subfigure}\n\\usepackage{epsfig}\n" in
  run "PKG-022 still fires (diagnostic unchanged)" (fun tag ->
      expect (fires_with_count "PKG-022" pkg_src 2) (tag ^ ": count=2"));
  run "PKG-022 emits subfigure->subcaption candidate" (fun tag ->
      expect
        (has_label "PKG-022" pkg_src
           "Replace obsolete package subfigure with subcaption")
        (tag ^ ": subfigure"));
  run "PKG-022 emits epsfig->graphicx candidate" (fun tag ->
      expect
        (has_label "PKG-022" pkg_src
           "Replace obsolete package epsfig with graphicx")
        (tag ^ ": epsfig"));
  run "PKG-022 subfigure candidate edit replaces just the name" (fun tag ->
      (* "\usepackage{" = 12 bytes; "subfigure" spans [12,21). *)
      expect
        (edit_of_label "PKG-022" pkg_src
           "Replace obsolete package subfigure with subcaption"
        = Some (12, 21, "subcaption"))
        (tag ^ ": edit"));
  run "PKG-022 natbib->biblatex candidate" (fun tag ->
      expect
        (has_label "PKG-022" "\\usepackage{natbib}"
           "Replace obsolete package natbib with biblatex")
        (tag ^ ": natbib"));
  run "PKG-022 candidate NOT in fix field (no auto-apply)" (fun tag ->
      expect (not (fires_with_fix "PKG-022" pkg_src)) (tag ^ ": fix=None"));
  run "PKG-022 --apply-fixes leaves package name untouched" (fun tag ->
      expect (apply_fix "PKG-022" pkg_src = pkg_src) (tag ^ ": no rewrite"));
  run "PKG-022 obsolete pkg without successor => no candidate" (fun tag ->
      (* t1enc is obsolete (counts) but has no modern mapping => no
         candidate. *)
      let s = "\\usepackage{t1enc}" in
      expect
        (fires "PKG-022" s && candidates_of "PKG-022" s = [])
        (tag ^ ": no candidate but still fires"));

  (* ══════════════════════════════════════════════════════════════════════
     CMD-002: \def used where \renewcommand is intended (TEXT rule, exempt)
     ══════════════════════════════════════════════════════════════════════ *)
  let cmd_src = "\\def\\foo{bar}" in
  run "CMD-002 still fires (diagnostic unchanged)" (fun tag ->
      expect (fires_with_count "CMD-002" cmd_src 1) (tag ^ ": count=1"));
  run "CMD-002 emits a \\renewcommand candidate" (fun tag ->
      expect
        (has_label "CMD-002" cmd_src
           "Redefine with \\renewcommand instead of \\def")
        (tag ^ ": candidate label"));
  run "CMD-002 candidate edit rewrites \\def\\foo -> \\renewcommand{\\foo}"
    (fun tag ->
      (* "\def\foo" spans [0,8); becomes "\renewcommand{\foo}". *)
      expect
        (edit_of_label "CMD-002" cmd_src
           "Redefine with \\renewcommand instead of \\def"
        = Some (0, 8, "\\renewcommand{\\foo}"))
        (tag ^ ": edit"));
  run "CMD-002 candidate NOT in fix field (no auto-apply)" (fun tag ->
      expect (not (fires_with_fix "CMD-002" cmd_src)) (tag ^ ": fix=None"));
  run "CMD-002 --apply-fixes leaves \\def byte-identical" (fun tag ->
      expect (apply_fix "CMD-002" cmd_src = cmd_src) (tag ^ ": no rewrite"));
  run "CMD-002 candidate dropped inside a comment" (fun tag ->
      let s = "% \\def\\foo{bar}\n" in
      expect
        (fires "CMD-002" s && candidates_of "CMD-002" s = [])
        (tag ^ ": exempt (comment) but still fires"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-025: one-column align -> equation (MATH rule, vcu-exempt)
     ══════════════════════════════════════════════════════════════════════ *)
  let m25_src = "\\begin{align}\nx = 1\n\\end{align}" in
  run "MATH-025 still fires (diagnostic unchanged)" (fun tag ->
      expect (fires_with_count "MATH-025" m25_src 1) (tag ^ ": count=1"));
  run "MATH-025 emits an equation candidate" (fun tag ->
      expect
        (has_label "MATH-025" m25_src "Use equation instead of one-column align")
        (tag ^ ": candidate label"));
  run "MATH-025 candidate carries two rename edits" (fun tag ->
      match candidates_of "MATH-025" m25_src with
      | [ { c_edits = [ e1; e2 ]; _ } ] ->
          expect
            (e1.Cst_edit.replacement = "equation"
            && e2.Cst_edit.replacement = "equation")
            (tag ^ ": 2 edits both rename to equation")
      | _ -> expect false (tag ^ ": expected one candidate with 2 edits"));
  run "MATH-025 candidate NOT in fix field (no auto-apply)" (fun tag ->
      expect (not (fires_with_fix "MATH-025" m25_src)) (tag ^ ": fix=None"));
  run "MATH-025 --apply-fixes leaves align byte-identical" (fun tag ->
      expect (apply_fix "MATH-025" m25_src = m25_src) (tag ^ ": no rewrite"));
  run "MATH-025 candidate dropped inside verbatim" (fun tag ->
      let v =
        "\\begin{verbatim}\n\\begin{align}\nx\n\\end{align}\n\\end{verbatim}"
      in
      expect
        (fires "MATH-025" v && candidates_of "MATH-025" v = [])
        (tag ^ ": vcu-exempt but still fires"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-032: square-bracketed smallmatrix -> bsmallmatrix (vcu-exempt)
     ══════════════════════════════════════════════════════════════════════ *)
  let m32_src = "[\\begin{smallmatrix}a\\end{smallmatrix}]" in
  run "MATH-032 still fires (diagnostic unchanged)" (fun tag ->
      expect (fires_with_count "MATH-032" m32_src 1) (tag ^ ": count=1"));
  run "MATH-032 emits a bmatrix candidate" (fun tag ->
      expect
        (has_label "MATH-032" m32_src
           "Use bsmallmatrix for a bracketed small matrix")
        (tag ^ ": candidate label"));
  run "MATH-032 candidate NOT in fix field (no auto-apply)" (fun tag ->
      expect (not (fires_with_fix "MATH-032" m32_src)) (tag ^ ": fix=None"));
  run "MATH-032 --apply-fixes leaves matrix byte-identical" (fun tag ->
      expect (apply_fix "MATH-032" m32_src = m32_src) (tag ^ ": no rewrite"));
  run "MATH-032 candidate dropped inside verbatim" (fun tag ->
      let v =
        "\\begin{verbatim}\n\
         [\\begin{smallmatrix}a\\end{smallmatrix}]\n\
         \\end{verbatim}"
      in
      expect
        (fires "MATH-032" v && candidates_of "MATH-032" v = [])
        (tag ^ ": vcu-exempt but still fires"));

  (* ══════════════════════════════════════════════════════════════════════
     VERB-006: inline \verb over a newline -> verbatim env (LABEL-ONLY)
     ══════════════════════════════════════════════════════════════════════ *)
  let v6_src = "See \\verb|a\nb| here" in
  run "VERB-006 still fires (diagnostic unchanged)" (fun tag ->
      expect (fires_with_count "VERB-006" v6_src 1) (tag ^ ": count=1"));
  run "VERB-006 emits a label-only verbatim candidate" (fun tag ->
      expect
        (has_label "VERB-006" v6_src
           "Convert inline \\verb to a verbatim environment")
        (tag ^ ": candidate label"));
  run "VERB-006 candidate has EMPTY edits (span ambiguous)" (fun tag ->
      match candidates_of "VERB-006" v6_src with
      | [ { c_edits = []; c_label } ] ->
          expect
            (c_label = "Convert inline \\verb to a verbatim environment")
            (tag ^ ": label-only candidate with the expected label")
      | _ -> expect false (tag ^ ": expected one label-only candidate"));
  run "VERB-006 candidate NOT in fix field (no auto-apply)" (fun tag ->
      expect (not (fires_with_fix "VERB-006" v6_src)) (tag ^ ": fix=None"));
  run "VERB-006 --apply-fixes leaves \\verb byte-identical" (fun tag ->
      expect (apply_fix "VERB-006" v6_src = v6_src) (tag ^ ": no rewrite"));
  run "VERB-006 label-only candidate dropped inside a comment" (fun tag ->
      (* The helpers cannot locate an empty-edit candidate, so VERB-006 must
         gate the \verb opener offset itself: a commented-out \verb yields NO
         candidate even though the diagnostic still fires. *)
      let s = "% \\verb|a\nb|" in
      expect
        (fires "VERB-006" s && candidates_of "VERB-006" s = [])
        (tag ^ ": exempt (comment) but still fires"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-052 / MATH-101: \over primitive -> \frac (vcu-exempt, group-bounded)
     ══════════════════════════════════════════════════════════════════════ *)
  let over_src = "${a \\over b}$" in
  let over_label = "Use \\frac{...}{...} instead of \\over" in
  run "MATH-052 still fires (diagnostic unchanged)" (fun tag ->
      expect (fires_with_count "MATH-052" over_src 1) (tag ^ ": count=1"));
  run "MATH-052 emits an \\over->\\frac candidate" (fun tag ->
      expect (has_label "MATH-052" over_src over_label) (tag ^ ": label"));
  run "MATH-052 candidate rewrites the group to {\\frac{a}{b}}" (fun tag ->
      (* `${` then group `{a \over b}` spans [1,12); becomes {\frac{a}{b}}. *)
      expect
        (edit_of_label "MATH-052" over_src over_label
        = Some (1, 12, "{\\frac{a}{b}}"))
        (tag ^ ": edit"));
  run "MATH-052 --apply-fixes leaves \\over byte-identical" (fun tag ->
      expect (apply_fix "MATH-052" over_src = over_src) (tag ^ ": no rewrite"));
  run "MATH-101 shares the same \\over->\\frac candidate" (fun tag ->
      expect
        (fires_with_count "MATH-101" over_src 1
        && edit_of_label "MATH-101" over_src over_label
           = Some (1, 12, "{\\frac{a}{b}}"))
        (tag ^ ": count + edit"));
  run "MATH-101 candidate dropped inside verbatim" (fun tag ->
      let v = "\\begin{verbatim}\n${a \\over b}$\n\\end{verbatim}" in
      expect
        (fires "MATH-101" v && candidates_of "MATH-101" v = [])
        (tag ^ ": vcu-exempt but still fires"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-012: multi-letter function -> \operatorname (vcu-exempt)
     ══════════════════════════════════════════════════════════════════════ *)
  let m12_src = "$foobar = 1$" in
  let m12_label = "Wrap multi-letter function in \\operatorname" in
  run "MATH-012 still fires (diagnostic unchanged)" (fun tag ->
      expect (fires_with_count "MATH-012" m12_src 1) (tag ^ ": count=1"));
  run "MATH-012 candidate wraps the token in \\operatorname{...}" (fun tag ->
      (* "foobar" spans [1,7); becomes \operatorname{foobar}. *)
      expect
        (edit_of_label "MATH-012" m12_src m12_label
        = Some (1, 7, "\\operatorname{foobar}"))
        (tag ^ ": edit"));
  run "MATH-012 --apply-fixes leaves the token byte-identical" (fun tag ->
      expect (apply_fix "MATH-012" m12_src = m12_src) (tag ^ ": no rewrite"));
  run "MATH-012 candidate dropped inside verbatim" (fun tag ->
      let v = "\\begin{verbatim}\n$foobar = 1$\n\\end{verbatim}" in
      expect
        (fires "MATH-012" v && candidates_of "MATH-012" v = [])
        (tag ^ ": vcu-exempt but still fires"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-102: eqnarray -> align (vcu-exempt, two rename edits)
     ══════════════════════════════════════════════════════════════════════ *)
  let m102_src = "\\begin{eqnarray}a &=& b\\end{eqnarray}" in
  run "MATH-102 still fires (diagnostic unchanged)" (fun tag ->
      expect (fires_with_count "MATH-102" m102_src 1) (tag ^ ": count=1"));
  run "MATH-102 emits an align candidate with two rename edits" (fun tag ->
      match candidates_of "MATH-102" m102_src with
      | [ { c_edits = [ e1; e2 ]; c_label } ] ->
          expect
            (c_label = "Use align instead of eqnarray"
            && e1.Cst_edit.replacement = "align"
            && e2.Cst_edit.replacement = "align"
            && e1.Cst_edit.start_offset = 7 (* "\begin{" then name *)
            && e1.Cst_edit.end_offset = 15)
            (tag ^ ": two align renames")
      | _ -> expect false (tag ^ ": expected one candidate with 2 edits"));
  run "MATH-102 --apply-fixes leaves eqnarray byte-identical" (fun tag ->
      expect (apply_fix "MATH-102" m102_src = m102_src) (tag ^ ": no rewrite"));
  run "MATH-102 candidate dropped inside verbatim" (fun tag ->
      let v =
        "\\begin{verbatim}\n\
         \\begin{eqnarray}a&=&b\\end{eqnarray}\n\
         \\end{verbatim}"
      in
      expect
        (fires "MATH-102" v && candidates_of "MATH-102" v = [])
        (tag ^ ": vcu-exempt but still fires"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-064: \eqalign -> align (REAL EDITS, brace-matched, vcu-exempt)
     ══════════════════════════════════════════════════════════════════════ *)
  let m64_src = "$$\\eqalign{a &= b}$$" in
  let m64_label = "Use the align environment instead of obsolete \\eqalign" in
  run "MATH-064 still fires (diagnostic unchanged)" (fun tag ->
      expect (fires_with_count "MATH-064" m64_src 1) (tag ^ ": count=1"));
  run
    "MATH-064 candidate rewrites \\eqalign{ -> \\begin{align} and matching } \
     -> \\end{align}" (fun tag ->
      (* "$$" = 2 bytes; "\eqalign{" spans [2,11); matching "}" at [17,18). *)
      match candidates_of "MATH-064" m64_src with
      | [ { c_edits = [ e1; e2 ]; c_label } ] ->
          expect
            (c_label = m64_label
            && e1.Cst_edit.start_offset = 2
            && e1.Cst_edit.end_offset = 11
            && e1.Cst_edit.replacement = "\\begin{align}"
            && e2.Cst_edit.start_offset = 17
            && e2.Cst_edit.end_offset = 18
            && e2.Cst_edit.replacement = "\\end{align}")
            (tag ^ ": two rewrite edits")
      | _ -> expect false (tag ^ ": expected one candidate with 2 edits"));
  run "MATH-064 candidate NOT in fix field (no auto-apply)" (fun tag ->
      expect (not (fires_with_fix "MATH-064" m64_src)) (tag ^ ": fix=None"));
  run "MATH-064 --apply-fixes leaves \\eqalign byte-identical" (fun tag ->
      expect (apply_fix "MATH-064" m64_src = m64_src) (tag ^ ": no rewrite"));
  run "MATH-064 unbraced \\eqalign degrades to a label-only candidate"
    (fun tag ->
      (* No opening brace to bound the body -> empty-edit (span unbounded). *)
      let s = "$$\\eqalign x$$" in
      match candidates_of "MATH-064" s with
      | [ { c_edits = []; c_label } ] ->
          expect (c_label = m64_label) (tag ^ ": label-only fallback")
      | _ -> expect false (tag ^ ": expected one label-only candidate"));
  run "MATH-064 candidate dropped inside a comment" (fun tag ->
      let s = "% \\eqalign{a}\n" in
      expect
        (fires "MATH-064" s && candidates_of "MATH-064" s = [])
        (tag ^ ": exempt (comment) but still fires"));

  (* ══════════════════════════════════════════════════════════════════════
     CMD-011: unguarded \def in preamble -> \makeatletter (REAL EDITS, exempt)
     ══════════════════════════════════════════════════════════════════════ *)
  let c11_src = "\\def\\mycmd{x}\n\\begin{document}\ntext\n\\end{document}" in
  let c11_label =
    "Wrap \\def/\\edef definitions in \\makeatletter/\\makeatother"
  in
  run "CMD-011 still fires (diagnostic unchanged)" (fun tag ->
      expect (fires_with_count "CMD-011" c11_src 1) (tag ^ ": count=1"));
  run "CMD-011 candidate wraps the \\def line in \\makeatletter/\\makeatother"
    (fun tag ->
      (* "\def\mycmd{x}" spans [0,13); the line-start insert is at 0 and the
         line-end insert is at the newline offset 13. *)
      match candidates_of "CMD-011" c11_src with
      | [ { c_edits = [ before; after ]; c_label } ] ->
          expect
            (c_label = c11_label
            && before.Cst_edit.start_offset = 0
            && before.Cst_edit.end_offset = 0
            && before.Cst_edit.replacement = "\\makeatletter\n"
            && after.Cst_edit.start_offset = 13
            && after.Cst_edit.end_offset = 13
            && after.Cst_edit.replacement = "\n\\makeatother")
            (tag ^ ": two wrapping inserts")
      | _ -> expect false (tag ^ ": expected one candidate with 2 edits"));
  run "CMD-011 candidate would wrap correctly if applied" (fun tag ->
      (* Sanity: applying the two inserts brackets exactly the \def line. *)
      match candidates_of "CMD-011" c11_src with
      | [ { c_edits; _ } ] -> (
          match Cst_edit.apply_all c11_src c_edits with
          | Ok out ->
              expect
                (out
                = "\\makeatletter\n\
                   \\def\\mycmd{x}\n\
                   \\makeatother\n\
                   \\begin{document}\n\
                   text\n\
                   \\end{document}")
                (tag ^ ": wrapped output")
          | Error _ -> expect false (tag ^ ": edits should apply cleanly"))
      | _ -> expect false (tag ^ ": expected one candidate"));
  run "CMD-011 candidate NOT in fix field (no auto-apply)" (fun tag ->
      expect (not (fires_with_fix "CMD-011" c11_src)) (tag ^ ": fix=None"));
  run "CMD-011 --apply-fixes leaves \\def byte-identical" (fun tag ->
      expect (apply_fix "CMD-011" c11_src = c11_src) (tag ^ ": no rewrite"));
  run "CMD-011 candidate dropped when \\def is commented" (fun tag ->
      let s = "% \\def\\mycmd{x}\n\\begin{document}\n\\end{document}" in
      expect
        (fires "CMD-011" s && candidates_of "CMD-011" s = [])
        (tag ^ ": exempt (comment) but still fires"));

  (* ══════════════════════════════════════════════════════════════════════
     VERB-010: back-ticks for inline code -> \verb (drop_exempt)
     ══════════════════════════════════════════════════════════════════════ *)
  let v10_src = "See `code` here" in
  let v10_label = "Use \\verb for inline code" in
  run "VERB-010 still fires (diagnostic unchanged)" (fun tag ->
      expect (fires_with_count "VERB-010" v10_src 1) (tag ^ ": count=1"));
  run "VERB-010 candidate rewrites `code` -> \\verb|code|" (fun tag ->
      (* "See " = 4 bytes; `code` spans [4,10). *)
      expect
        (edit_of_label "VERB-010" v10_src v10_label
        = Some (4, 10, "\\verb|code|"))
        (tag ^ ": edit"));
  run "VERB-010 --apply-fixes leaves back-ticks byte-identical" (fun tag ->
      expect (apply_fix "VERB-010" v10_src = v10_src) (tag ^ ": no rewrite"));
  run "VERB-010 candidate dropped inside a comment" (fun tag ->
      let s = "% see `code` here\n" in
      expect
        (fires "VERB-010" s && candidates_of "VERB-010" s = [])
        (tag ^ ": exempt (comment) but still fires"));

  (* ══════════════════════════════════════════════════════════════════════
     BIB-011: note={URL:...} -> url field (drop_exempt, two edits)
     ══════════════════════════════════════════════════════════════════════ *)
  let b11_src = "note = {URL: http://example.com}" in
  run "BIB-011 still fires (diagnostic unchanged)" (fun tag ->
      expect (fires_with_count "BIB-011" b11_src 1) (tag ^ ": count=1"));
  run "BIB-011 candidate renames note->url and strips the URL: prefix"
    (fun tag ->
      match candidates_of "BIB-011" b11_src with
      | [ { c_edits = [ rename; strip ]; c_label } ] ->
          expect
            (c_label = "Move the URL to a url field"
            && rename.Cst_edit.start_offset = 0
            && rename.Cst_edit.end_offset = 4
            && rename.Cst_edit.replacement = "url"
            && strip.Cst_edit.replacement = ""
            && strip.Cst_edit.end_offset - strip.Cst_edit.start_offset = 4)
            (tag ^ ": rename + strip URL:")
      | _ -> expect false (tag ^ ": expected one candidate with 2 edits"));
  run "BIB-011 --apply-fixes leaves the note field byte-identical" (fun tag ->
      expect (apply_fix "BIB-011" b11_src = b11_src) (tag ^ ": no rewrite"));
  run "BIB-011 candidate dropped inside a comment" (fun tag ->
      let s = "% note = {URL: http://x}\n" in
      expect
        (fires "BIB-011" s && candidates_of "BIB-011" s = [])
        (tag ^ ": exempt (comment) but still fires"));

  (* ══════════════════════════════════════════════════════════════════════
     CHEM-001: chemical formula -> \ce{} (REAL EDITS, span-bracketing,
     vcu-exempt)
     ══════════════════════════════════════════════════════════════════════ *)
  let ch_src = "$H_2O$" in
  let ch_label = "Wrap the chemical formula in \\ce{} (mhchem)" in
  run "CHEM-001 still fires (diagnostic unchanged)" (fun tag ->
      expect (fires "CHEM-001" ch_src) (tag ^ ": fires"));
  run "CHEM-001 candidate brackets the formula span with \\ce{ ... }"
    (fun tag ->
      (* "$" at 0; formula "H_2" spans [1,4); insert \ce{ at 1 and } at 4. *)
      match candidates_of "CHEM-001" ch_src with
      | { c_edits = [ open_ins; close_ins ]; c_label } :: _ ->
          expect
            (c_label = ch_label
            && open_ins.Cst_edit.start_offset = 1
            && open_ins.Cst_edit.end_offset = 1
            && open_ins.Cst_edit.replacement = "\\ce{"
            && close_ins.Cst_edit.start_offset = 4
            && close_ins.Cst_edit.end_offset = 4
            && close_ins.Cst_edit.replacement = "}")
            (tag ^ ": two bracketing inserts")
      | _ -> expect false (tag ^ ": expected a candidate with 2 inserts"));
  run "CHEM-001 candidate would wrap correctly if applied" (fun tag ->
      match candidates_of "CHEM-001" ch_src with
      | { c_edits; _ } :: _ -> (
          match Cst_edit.apply_all ch_src c_edits with
          | Ok out -> expect (out = "$\\ce{H_2}O$") (tag ^ ": bracketed formula")
          | Error _ -> expect false (tag ^ ": edits should apply cleanly"))
      | _ -> expect false (tag ^ ": expected a candidate"));
  run "CHEM-001 candidate NOT in fix field (no auto-apply)" (fun tag ->
      expect (not (fires_with_fix "CHEM-001" ch_src)) (tag ^ ": fix=None"));
  run "CHEM-001 --apply-fixes leaves the formula byte-identical" (fun tag ->
      expect (apply_fix "CHEM-001" ch_src = ch_src) (tag ^ ": no rewrite"));
  run "CHEM-001 candidate dropped inside verbatim" (fun tag ->
      let v = "\\begin{verbatim}\n$H_2O$\n\\end{verbatim}" in
      expect
        (fires "CHEM-001" v && candidates_of "CHEM-001" v = [])
        (tag ^ ": vcu-exempt but still fires"));

  (* ══════════════════════════════════════════════════════════════════════
     ZH-001: western '.' after CJK -> 。 (drop_exempt)
     ══════════════════════════════════════════════════════════════════════ *)
  let zh_src = "\xe4\xb8\xad." (* 中. *) in
  let zh_label = "Use the Chinese period 。 (U+3002)" in
  run "ZH-001 still fires (diagnostic unchanged)" (fun tag ->
      expect (fires_with_count "ZH-001" zh_src 1) (tag ^ ": count=1"));
  run "ZH-001 candidate replaces '.' with 。 (U+3002)" (fun tag ->
      (* 中 = 3 bytes [0,3); '.' at offset 3 -> \xe3\x80\x82. *)
      expect
        (edit_of_label "ZH-001" zh_src zh_label = Some (3, 4, "\xe3\x80\x82"))
        (tag ^ ": edit"));
  run "ZH-001 --apply-fixes leaves '.' byte-identical" (fun tag ->
      expect (apply_fix "ZH-001" zh_src = zh_src) (tag ^ ": no rewrite"));
  run "ZH-001 candidate dropped inside a comment" (fun tag ->
      let s = "% \xe4\xb8\xad.\n" in
      expect
        (fires "ZH-001" s && candidates_of "ZH-001" s = [])
        (tag ^ ": exempt (comment) but still fires"));

  (* ══════════════════════════════════════════════════════════════════════
     FR-008: "oe" digraph -> œ/Œ ligature (drop_exempt)
     ══════════════════════════════════════════════════════════════════════ *)
  let fr_src = "coeur" in
  let fr_label = "Use the œ/Œ ligature" in
  run "FR-008 still fires (diagnostic unchanged)" (fun tag ->
      expect (fires_with_count "FR-008" fr_src 1) (tag ^ ": count=1"));
  run "FR-008 candidate replaces 'oe' with œ (U+0153)" (fun tag ->
      (* "c" then "oe" spans [1,3) -> \xc5\x93. *)
      expect
        (edit_of_label "FR-008" fr_src fr_label = Some (1, 3, "\xc5\x93"))
        (tag ^ ": edit"));
  run "FR-008 uppercase OEUVRE gets the Œ ligature (U+0152)" (fun tag ->
      expect
        (edit_of_label "FR-008" "OEUVRE" fr_label = Some (0, 2, "\xc5\x92"))
        (tag ^ ": uppercase edit"));
  run "FR-008 --apply-fixes leaves 'oe' byte-identical" (fun tag ->
      expect (apply_fix "FR-008" fr_src = fr_src) (tag ^ ": no rewrite"));
  run "FR-008 candidate dropped inside a comment" (fun tag ->
      let s = "% coeur\n" in
      expect
        (fires "FR-008" s && candidates_of "FR-008" s = [])
        (tag ^ ": exempt (comment) but still fires"));

  let m36 = "$\\mathrm{x}$" in
  run "MATH-036 lists an unwrap candidate" (fun tag ->
      expect
        (has_label "MATH-036" m36
           "Drop superfluous \\mathrm around a single letter")
        (tag ^ ": label"));
  run "MATH-036 candidate edit unwraps to the bare letter" (fun tag ->
      match
        edit_of_label "MATH-036" m36
          "Drop superfluous \\mathrm around a single letter"
      with
      | Some (b, e, r) ->
          expect (b = 1 && e = 11 && r = "x") (tag ^ ": edit [1,11)->x")
      | None -> expect false (tag ^ ": expected one edit"));
  run "MATH-036 candidate dropped inside verbatim" (fun tag ->
      expect
        (candidates_of "MATH-036" "\\verb|$\\mathrm{x}$|" = [])
        (tag ^ ": vcu-dropped"));
  let m50 = "$\\hat{abc}$" in
  run "MATH-050 lists a widehat candidate" (fun tag ->
      expect
        (has_label "MATH-050" m50 "Use \\widehat for a multi-letter accent")
        (tag ^ ": label"));
  run "MATH-050 candidate edit rewrites the accent prefix" (fun tag ->
      match
        edit_of_label "MATH-050" m50 "Use \\widehat for a multi-letter accent"
      with
      | Some (b, e, r) ->
          expect
            (b = 1 && e = 5 && r = "\\widehat")
            (tag ^ ": edit [1,5)->\\widehat")
      | None -> expect false (tag ^ ": expected one edit"));
  let mbf = "$\\mathbf{42}$" in
  run "MATH-048 lists an unwrap-digits candidate" (fun tag ->
      match edit_of_label "MATH-048" mbf "Drop \\mathbf boldface on digits" with
      | Some (b, e, r) ->
          expect (b = 1 && e = 12 && r = "42") (tag ^ ": edit [1,12)->42")
      | None -> expect false (tag ^ ": expected one edit"));
  run "MATH-087 also lists the unwrap-digits candidate" (fun tag ->
      expect
        (has_label "MATH-087" mbf "Drop \\mathbf boldface on digits")
        (tag ^ ": label"));
  run "MATH-048 candidate dropped inside verbatim" (fun tag ->
      expect
        (candidates_of "MATH-048" "\\verb|$\\mathbf{42}$|" = [])
        (tag ^ ": vcu-dropped"));

  (* ══════════════════════════════════════════════════════════════════════
     Bucket-C batch (v27.1.22): MATH-096/019/016/035/047/059/045/058 + DELIM-008
     ══════════════════════════════════════════════════════════════════════ *)
  let m96 = "$\\mathbf{\\alpha}$" in
  run "MATH-096 lists a \\boldsymbol candidate" (fun tag ->
      expect
        (edit_of_label "MATH-096" m96
           "Use \\boldsymbol for bold Greek instead of \\mathbf"
        = Some (1, 8, "\\boldsymbol"))
        (tag ^ ": edit [1,8)->\\boldsymbol"));
  run "MATH-096 candidate dropped inside verbatim" (fun tag ->
      expect
        (candidates_of "MATH-096" "\\verb|$\\mathbf{\\alpha}$|" = [])
        (tag ^ ": vcu-dropped"));

  let m19 = "$x^2_i$" in
  run "MATH-019 lists a reorder candidate" (fun tag ->
      expect
        (edit_of_label "MATH-019" m19
           "Reorder scripts to subscript-before-superscript"
        = Some (2, 6, "_i^2"))
        (tag ^ ": edit [2,6)->_i^2"));

  let m16 = "$x_i_j$" in
  run "MATH-016 lists a brace-nesting candidate" (fun tag ->
      expect
        (edit_of_label "MATH-016" m16 "Brace nested subscripts as _{...}"
        = Some (2, 6, "_{i_{j}}"))
        (tag ^ ": edit [2,6)->_{i_{j}}"));

  let m35 = "$x_{i}_{j}$" in
  run "MATH-035 lists a combine-subscripts candidate" (fun tag ->
      expect
        (edit_of_label "MATH-035" m35 "Combine stacked subscripts into _{i,j}"
        = Some (2, 10, "_{i,j}"))
        (tag ^ ": edit [2,10)->_{i,j}"));

  let m47 = "$x^i^j$" in
  run "MATH-047 lists a brace-superscript candidate" (fun tag ->
      expect
        (edit_of_label "MATH-047" m47 "Brace double superscript as ^{...}"
        = Some (2, 6, "^{i^{j}}"))
        (tag ^ ": edit [2,6)->^{i^{j}}"));

  let m59 = "$\\bar{a+b}$" in
  run "MATH-059 lists an \\overline candidate" (fun tag ->
      expect
        (edit_of_label "MATH-059" m59
           "Use \\overline for a bar over a group expression"
        = Some (1, 5, "\\overline"))
        (tag ^ ": edit [1,5)->\\overline"));

  let m45 = "$\\mathrm{\\Gamma}+\\Delta$" in
  run "MATH-045 wraps the BARE capital Greek only" (fun tag ->
      expect
        (edit_of_label "MATH-045" m45
           "Wrap capital Greek in \\mathrm to match upright"
        = Some (17, 23, "\\mathrm{\\Delta}"))
        (tag ^ ": edit [17,23)->\\mathrm{\\Delta}"));

  let m58 = "$\\text{\\text{hi}}$" in
  run "MATH-058 unwraps the inner nested \\text" (fun tag ->
      match candidates_of "MATH-058" m58 with
      | [ { c_edits; c_label } ] -> (
          match Cst_edit.apply_all m58 c_edits with
          | Ok out ->
              expect
                (c_label = "Unwrap redundant nested \\text"
                && out = "$\\text{hi}$")
                (tag ^ ": unwrapped to $\\text{hi}$")
          | Error _ -> expect false (tag ^ ": edits should apply cleanly"))
      | _ -> expect false (tag ^ ": expected one candidate"));

  let d8 = "$\\left. \\right.$" in
  run "DELIM-008 lists a remove-invisible-pair candidate" (fun tag ->
      expect
        (edit_of_label "DELIM-008" d8
           "Remove redundant \\left. … \\right. invisible pair"
        = Some (1, 15, " "))
        (tag ^ ": edit [1,15)-> space"));
  run "DELIM-008 candidate dropped inside verbatim" (fun tag ->
      expect
        (candidates_of "DELIM-008" "\\verb|$\\left. \\right.$|" = [])
        (tag ^ ": vcu-dropped"));

  (* ══════════════════════════════════════════════════════════════════════
     Bucket-C batch (v27.1.24): math spacing / differential candidates MATH-034
     / TYPO-011 / MATH-042 / MATH-031 / MATH-068 / MATH-013 / MATH-060 TYPO-011
     is a pilot rule, so enable the pilot set for the rest of the file.
     ══════════════════════════════════════════════════════════════════════ *)
  Unix.putenv "L0_VALIDATORS" "pilot";

  let m34 = "$\\int f(x)dx$" in
  run "MATH-034 lists a thin-space-before-differential candidate" (fun tag ->
      expect
        (edit_of_label "MATH-034" m34
           "Insert a thin space \\, before the differential"
        = Some (10, 10, "\\,"))
        (tag ^ ": insert \\, at 10"));
  run "MATH-034 candidate dropped inside verbatim" (fun tag ->
      expect
        (candidates_of "MATH-034" "\\verb|$\\int f(x)dx$|" = [])
        (tag ^ ": vcu-dropped"));

  run "TYPO-011 lists a thin-space-before-differential candidate" (fun tag ->
      expect
        (edit_of_label "TYPO-011" m34
           "Insert a thin space \\, before the differential"
        = Some (10, 10, "\\,"))
        (tag ^ ": insert \\, at 10"));

  let m42 = "$5\\mathrm{kg}$" in
  run "MATH-042 lists a number-unit thin-space candidate" (fun tag ->
      expect
        (edit_of_label "MATH-042" m42
           "Insert a thin space \\, between the number and unit"
        = Some (2, 2, "\\,"))
        (tag ^ ": insert \\, at 2"));

  let m31 = "$x\\text{if}$" in
  run "MATH-031 lists a medium-space-before-\\text candidate" (fun tag ->
      expect
        (edit_of_label "MATH-031" m31 "Insert a medium space \\; before \\text"
        = Some (2, 2, "\\;"))
        (tag ^ ": insert \\; at 2"));

  let m68 = "$a\\mid b$" in
  run "MATH-068 wraps \\mid in thin spaces (two edits)" (fun tag ->
      match candidates_of "MATH-068" m68 with
      | [ { c_edits; c_label } ] -> (
          match Cst_edit.apply_all m68 c_edits with
          | Ok out ->
              expect
                (c_label = "Add thin spaces \\, around \\mid"
                && out = "$a\\,\\mid\\,b$")
                (tag ^ ": -> $a\\,\\mid\\,b$")
          | Error _ -> expect false (tag ^ ": edits should apply cleanly"))
      | _ -> expect false (tag ^ ": expected one candidate with 2 edits"));

  let m13 = "$\\int f(x) dx$" in
  run "MATH-013 lists an upright-differential candidate" (fun tag ->
      expect
        (edit_of_label "MATH-013" m13
           "Typeset the differential d upright with \\mathrm{d}"
        = Some (11, 12, "\\mathrm{d}"))
        (tag ^ ": [11,12)->\\mathrm{d}"));

  run "MATH-060 lists an upright-differential candidate" (fun tag ->
      expect
        (edit_of_label "MATH-060" m34
           "Typeset the differential d upright with \\mathrm{d}"
        = Some (10, 11, "\\mathrm{d}"))
        (tag ^ ": [10,11)->\\mathrm{d}"));

  (* ══════════════════════════════════════════════════════════════════════
     Bucket-C batch (structural/misc): TAB-006 / TAB-005 / DOC-001 / TIKZ-009 /
     SPC-017 / SPC-023
     ══════════════════════════════════════════════════════════════════════ *)
  let tab6 = "\\hline \\hline" in
  run "TAB-006 collapses duplicated \\hline to a single \\hline" (fun tag ->
      (* `\hline \hline` spans [0,13); collapses to a single `\hline`. *)
      expect
        (fires_with_count "TAB-006" tab6 1
        && edit_of_label "TAB-006" tab6
             "Collapse duplicated \\hline into a single \\hline"
           = Some (0, 13, "\\hline"))
        (tag ^ ": edit [0,13)->\\hline"));

  let tab5 = "\\begin{tabular}{|c|c|}a\\end{tabular}" in
  run "TAB-005 removes a vertical rule from the column spec" (fun tag ->
      (* "\begin{tabular}{" = 16 bytes; first `|` at offset 16. *)
      expect
        (fires_with_count "TAB-005" tab5 1
        && edit_of_label "TAB-005" tab5
             "Remove vertical rule (|) from tabular column spec (booktabs \
              style)"
           = Some (16, 17, ""))
        (tag ^ ": delete `|` at 16"));

  let doc1 =
    "\\documentclass{article}\n\\begin{document}\ntext\n\\end{document}"
  in
  run "DOC-001 inserts \\maketitle after \\begin{document}" (fun tag ->
      (* "\documentclass{article}\n" = 24 bytes; "\begin{document}" ends at
         40. *)
      expect
        (edit_of_label "DOC-001" doc1
           "Insert \\maketitle after \\begin{document}"
        = Some (40, 40, "\n\\maketitle"))
        (tag ^ ": insert at 40"));

  let tikz9 =
    "\\usepackage{tikz}\n\
     \\begin{tikzpicture}\n\
     \\draw (0,0) -> (1,1);\n\
     \\end{tikzpicture}"
  in
  run "TIKZ-009 loads arrows.meta after \\usepackage{tikz}" (fun tag ->
      (* "\usepackage{tikz}" — the `}` is at 16, so insert at 17. *)
      expect
        (edit_of_label "TIKZ-009" tikz9
           "Load \\usetikzlibrary{arrows.meta} for arrow tips"
        = Some (17, 17, "\n\\usetikzlibrary{arrows.meta}"))
        (tag ^ ": insert at 17"));

  let spc17 = "5cm" in
  run "SPC-017 inserts a thin space between number and unit" (fun tag ->
      (* digit `5` at 0, unit starts at 1; insert \, at offset 1. *)
      expect
        (fires_with_count "SPC-017" spc17 1
        && edit_of_label "SPC-017" spc17
             "Insert a thin space \\, between the number and unit"
           = Some (1, 1, "\\,"))
        (tag ^ ": insert \\, at 1"));

  let spc23 = "a\xc2\xa0b" (* a<U+00A0>b *) in
  run "SPC-023 replaces the hard space U+00A0 with a plain space" (fun tag ->
      (* `a` at 0; U+00A0 = C2 A0 spans [1,3) -> " ". *)
      expect
        (fires_with_count "SPC-023" spc23 1
        && edit_of_label "SPC-023" spc23
             "Replace hard space U+00A0 with an ordinary space"
           = Some (1, 3, " "))
        (tag ^ ": replace [1,3)-> space"));
  run "SPC-023 candidate dropped inside a comment" (fun tag ->
      let s = "% a\xc2\xa0b\n" in
      expect
        (fires "SPC-023" s && candidates_of "SPC-023" s = [])
        (tag ^ ": exempt (comment) but still fires"));

  finalise "candidate_fixes"
