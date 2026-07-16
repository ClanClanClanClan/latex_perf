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

(* [edits_of c] — the (start, end, replacement) triples of a candidate. *)
let edits_of (c : Validators.candidate_fix) =
  List.map
    (fun (e : Cst_edit.t) ->
      (e.Cst_edit.start_offset, e.Cst_edit.end_offset, e.Cst_edit.replacement))
    c.c_edits

(* [has_edit_set id src edits] — some candidate on [id]/[src] carries exactly
   [edits] (as (start,end,replacement) triples, in order). *)
let has_edit_set id src edits =
  List.exists (fun c -> edits_of c = edits) (candidates_of id src)

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

  let s010 = "$\\sum\\limits_i x$" in
  run "SCRIPT-010 lists a drop-\\limits candidate (inline)" (fun tag ->
      match
        edit_of_label "SCRIPT-010" s010 "Drop \\limits on an inline operator"
      with
      | Some (b, e, r) ->
          expect (b = 5 && e = 12 && r = "") (tag ^ ": edit [5,12)->''")
      | None -> expect false (tag ^ ": expected one edit"));
  run "SCRIPT-010 excludes display math \\limits" (fun tag ->
      expect
        (candidates_of "SCRIPT-010" "$$\\sum\\limits_j y$$" = [])
        (tag ^ ": display excluded"));

  (* ══════════════════════════════════════════════════════════════════════
     DE-006: Swiss German ß — ß→ss is lossy/locale-dependent → CANDIDATE
     ══════════════════════════════════════════════════════════════════════ *)
  let de6 = "Stra\xc3\x9fe" (* Straße: ß = C3 9F at [4,6) *) in
  run "DE-006 still fires (diagnostic count unchanged)" (fun tag ->
      expect (fires_with_count "DE-006" de6 1) (tag ^ ": count=1"));
  run "DE-006 emits a ss candidate at the right span" (fun tag ->
      expect
        (edit_of_label "DE-006" de6
           "Replace \xc3\x9f with \xe2\x80\x9css\xe2\x80\x9d (Swiss German \
            orthography)"
        = Some (4, 6, "ss"))
        (tag ^ ": edit [4,6)->ss"));
  run "DE-006 candidate is NOT an auto-fix (no fix field)" (fun tag ->
      expect (not (fires_with_fix "DE-006" de6)) (tag ^ ": fix=None"));
  run "DE-006 candidate dropped inside a comment (still fires)" (fun tag ->
      let s = "% Stra\xc3\x9fe\n" in
      expect
        (fires "DE-006" s && candidates_of "DE-006" s = [])
        (tag ^ ": exempt (comment)"));

  (* ══════════════════════════════════════════════════════════════════════
     ENC-006: overlong UTF-8 — re-encode can yield control bytes → CANDIDATE
     ══════════════════════════════════════════════════════════════════════ *)
  let enc6 = "ab\xc1\x80cd" (* C1 80 overlong = U+0040 '@' at [2,4) *) in
  run "ENC-006 still fires (diagnostic count unchanged)" (fun tag ->
      expect (fires_with_count "ENC-006" enc6 1) (tag ^ ": count=1"));
  run "ENC-006 emits a minimal re-encode candidate (C1 80 -> @)" (fun tag ->
      expect
        (edit_of_label "ENC-006" enc6
           "Re-encode overlong UTF-8 sequence in minimal form"
        = Some (2, 4, "@"))
        (tag ^ ": edit [2,4)->@"));
  run "ENC-006 candidate is NOT an auto-fix (no fix field)" (fun tag ->
      expect (not (fires_with_fix "ENC-006" enc6)) (tag ^ ": fix=None"));
  run "ENC-006 candidate dropped inside a comment (still fires)" (fun tag ->
      let s = "% ab\xc1\x80cd\n" in
      expect
        (fires "ENC-006" s && candidates_of "ENC-006" s = [])
        (tag ^ ": exempt (comment)"));

  (* ══════════════════════════════════════════════════════════════════════
     DELIM-010: \big-family sizing in display math -> \Big (CANDIDATE)
     ══════════════════════════════════════════════════════════════════════ *)
  let d10 = "\\[ x \\big| y \\]" in
  run "DELIM-010 lists a \\big->\\Big candidate in display math" (fun tag ->
      (* `\big` starts at 5, its `b` is at 6 -> capitalise [6,7) to `B`. *)
      expect
        (fires_with_count "DELIM-010" d10 1
        && edit_of_label "DELIM-010" d10
             "Use \\Big-family sizing (\\big -> \\Big) in display math"
           = Some (6, 7, "B"))
        (tag ^ ": edit [6,7)->B"));
  run "DELIM-010 candidate is NOT an auto-fix (no fix field)" (fun tag ->
      expect (not (fires_with_fix "DELIM-010" d10)) (tag ^ ": fix=None"));
  run "DELIM-010 candidate dropped inside verbatim (still fires)" (fun tag ->
      let s = "\\begin{verbatim}\n\\[ x \\big| y \\]\n\\end{verbatim}\n" in
      expect
        (fires "DELIM-010" s && candidates_of "DELIM-010" s = [])
        (tag ^ ": exempt (verbatim)"));

  (* ══════════════════════════════════════════════════════════════════════
     TIKZ-010: deprecated pgfplots compat=1.[0-7] -> 1.18 (CANDIDATE)
     ══════════════════════════════════════════════════════════════════════ *)
  let t10 = "\\pgfplotsset{compat=1.7}" in
  run "TIKZ-010 bumps a deprecated compat level to 1.18" (fun tag ->
      (* `\pgfplotsset{` is 13 bytes; `compat=1.7` spans [13,23). *)
      expect
        (fires_with_count "TIKZ-010" t10 1
        && edit_of_label "TIKZ-010" t10
             "Bump deprecated pgfplots compat to 1.18"
           = Some (13, 23, "compat=1.18"))
        (tag ^ ": edit [13,23)->compat=1.18"));
  run "TIKZ-010 offers no candidate for the `every axis` case" (fun tag ->
      let s = "\\pgfplotsset{every axis/.style={}}" in
      expect
        (fires "TIKZ-010" s && candidates_of "TIKZ-010" s = [])
        (tag ^ ": fires but no compat edit"));

  (* ══════════════════════════════════════════════════════════════════════
     VERB-012: add autogobble to the minted OPTION list (CANDIDATE)
     ══════════════════════════════════════════════════════════════════════ *)
  let v12 = "\\begin{minted}{python}\nx=1\n\\end{minted}\n" in
  run "VERB-012 inserts a fresh [autogobble] option block" (fun tag ->
      (* `\begin{minted}` is 14 bytes; insert `[autogobble]` at offset 14. *)
      expect
        (fires_with_count "VERB-012" v12 1
        && edit_of_label "VERB-012" v12 "Add autogobble to the minted options"
           = Some (14, 14, "[autogobble]"))
        (tag ^ ": insert [autogobble] at 14"));
  let v12b =
    "\\begin{minted}[fontsize=\\small]{python}\nx=1\n\\end{minted}\n"
  in
  run "VERB-012 adds autogobble inside an existing option block" (fun tag ->
      (* `[` is at 14; insert `autogobble, ` right after it, at 15. *)
      expect
        (edit_of_label "VERB-012" v12b "Add autogobble to the minted options"
        = Some (15, 15, "autogobble, "))
        (tag ^ ": insert autogobble, at 15"));
  run "VERB-012 candidate is NOT an auto-fix (no fix field)" (fun tag ->
      expect (not (fires_with_fix "VERB-012" v12)) (tag ^ ": fix=None"));
  run "VERB-012 candidate dropped for a commented-out minted" (fun tag ->
      let s = "% \\begin{minted}{python}\n% x=1\n% \\end{minted}\n" in
      expect
        (fires "VERB-012" s && candidates_of "VERB-012" s = [])
        (tag ^ ": nested in comment -> no candidate"));

  (* ══════════════════════════════════════════════════════════════════════
     VERB-016: escapeinside needs a content-dependent delimiter -> LABEL-ONLY
     ══════════════════════════════════════════════════════════════════════ *)
  let v16 = "\\begin{minted}{python}\nx = `echo hi`\n\\end{minted}\n" in
  run "VERB-016 surfaces a label-only escapeinside candidate" (fun tag ->
      expect
        (fires_with_count "VERB-016" v16 1
        && has_label "VERB-016" v16
             "Add escapeinside=<d1><d2> to the minted options (choose \
              delimiters absent from the code)"
        && edit_of_label "VERB-016" v16
             "Add escapeinside=<d1><d2> to the minted options (choose \
              delimiters absent from the code)"
           = None)
        (tag ^ ": label present, no edit"));
  run "VERB-016 candidate is NOT an auto-fix (no fix field)" (fun tag ->
      expect (not (fires_with_fix "VERB-016" v16)) (tag ^ ": fix=None"));

  (* ══════════════════════════════════════════════════════════════════════
     VERB-017: add linenos to the minted OPTION list (CANDIDATE)
     ══════════════════════════════════════════════════════════════════════ *)
  let v17 =
    "\\begin{minted}{python}\n"
    ^ String.concat "" (List.init 25 (fun _ -> "x\n"))
    ^ "\\end{minted}\n"
  in
  run "VERB-017 inserts a fresh [linenos] option block" (fun tag ->
      (* `\begin{minted}` is 14 bytes; insert `[linenos]` at offset 14. *)
      expect
        (fires_with_count "VERB-017" v17 1
        && edit_of_label "VERB-017" v17 "Add linenos to the minted options"
           = Some (14, 14, "[linenos]"))
        (tag ^ ": insert [linenos] at 14"));
  run "VERB-017 candidate is NOT an auto-fix (no fix field)" (fun tag ->
      expect (not (fires_with_fix "VERB-017" v17)) (tag ^ ": fix=None"));

  (* ══════════════════════════════════════════════════════════════════════
     MOD-001: legacy 2.09 font switch -> NFSS declarative form (REAL EDIT)
     ══════════════════════════════════════════════════════════════════════ *)
  let mod1_src = "{\\bf bold}" in
  let mod1_label =
    "Replace legacy 2.09 font switch with its NFSS declarative form (caveat: \
     the legacy switch resets ALL font axes; the NFSS switch sets only its own \
     — review before applying)"
  in
  run "MOD-001 still fires (diagnostic count unchanged)" (fun tag ->
      expect (fires_with_count "MOD-001" mod1_src 1) (tag ^ ": count=1"));
  run "MOD-001 emits an NFSS candidate replacing \\bf -> \\bfseries" (fun tag ->
      (* `{` = 1 byte, then `\bf` spans [1,4). *)
      expect
        (has_label "MOD-001" mod1_src mod1_label
        && edit_of_label "MOD-001" mod1_src mod1_label
           = Some (1, 4, "\\bfseries"))
        (tag ^ ": edit"));
  run "MOD-001 candidate NOT in fix field (no auto-apply)" (fun tag ->
      expect (not (fires_with_fix "MOD-001" mod1_src)) (tag ^ ": fix=None"));
  run "MOD-001 --apply-fixes leaves \\bf byte-identical" (fun tag ->
      expect (apply_fix "MOD-001" mod1_src = mod1_src) (tag ^ ": no rewrite"));
  run "MOD-001 candidate dropped inside a comment (count untouched)" (fun tag ->
      let s = "% {\\it x}" in
      expect
        (fires "MOD-001" s && candidates_of "MOD-001" s = [])
        (tag ^ ": exempt (comment) but still fires"));

  (* ══════════════════════════════════════════════════════════════════════
     CMD-008: \@ macro def outside makeatletter -> wrap (REAL EDITS)
     ══════════════════════════════════════════════════════════════════════ *)
  let c8_src = "\\def\\my@cmd{x}\n" in
  let c8_label =
    "Wrap the \\@ macro definition in \\makeatletter/\\makeatother"
  in
  run "CMD-008 still fires (diagnostic count unchanged)" (fun tag ->
      expect (fires_with_count "CMD-008" c8_src 1) (tag ^ ": count=1"));
  run "CMD-008 candidate wraps the def line in \\makeatletter/\\makeatother"
    (fun tag ->
      match candidates_of "CMD-008" c8_src with
      | [ { c_edits = [ e1; e2 ]; c_label } ] ->
          expect
            (c_label = c8_label
            && ( e1.Cst_edit.start_offset,
                 e1.Cst_edit.end_offset,
                 e1.Cst_edit.replacement )
               = (0, 0, "\\makeatletter\n")
            && ( e2.Cst_edit.start_offset,
                 e2.Cst_edit.end_offset,
                 e2.Cst_edit.replacement )
               = (14, 14, "\n\\makeatother"))
            (tag ^ ": two inserts bracketing the def line")
      | _ -> expect false (tag ^ ": expected one two-edit candidate"));
  run "CMD-008 candidate NOT in fix field (no auto-apply)" (fun tag ->
      expect (not (fires_with_fix "CMD-008" c8_src)) (tag ^ ": fix=None"));
  run "CMD-008 --apply-fixes leaves the def byte-identical" (fun tag ->
      expect (apply_fix "CMD-008" c8_src = c8_src) (tag ^ ": no rewrite"));
  run "CMD-008 candidate dropped when the def is commented" (fun tag ->
      let s = "% \\def\\my@cmd{x}\n" in
      expect
        (fires "CMD-008" s && candidates_of "CMD-008" s = [])
        (tag ^ ": exempt (comment) but still fires"));

  (* ══════════════════════════════════════════════════════════════════════
     CMD-001 / CMD-006 / CMD-013 / CMD-014: non-local moves -> LABEL-ONLY
     ══════════════════════════════════════════════════════════════════════ *)
  let c1_src = "\\newcommand{\\foo}{bar}\n" in
  let c1_label =
    "Consider removing the unused \\newcommand definition (verify it is not \
     used in another file first)"
  in
  run "CMD-001 still fires (diagnostic count unchanged)" (fun tag ->
      expect (fires_with_count "CMD-001" c1_src 1) (tag ^ ": count=1"));
  run "CMD-001 emits a label-only removal candidate" (fun tag ->
      match candidates_of "CMD-001" c1_src with
      | [ { c_edits = []; c_label } ] ->
          expect (c_label = c1_label) (tag ^ ": label-only removal suggestion")
      | _ -> expect false (tag ^ ": expected one label-only candidate"));
  run "CMD-001 candidate NOT in fix field (no auto-apply)" (fun tag ->
      expect (not (fires_with_fix "CMD-001" c1_src)) (tag ^ ": fix=None"));

  let c6_src =
    "\\begin{document}\n\\newcommand{\\foo}{bar}\n\\end{document}\n"
  in
  let c6_label =
    "Consider moving the macro definition to the preamble (before \
     \\begin{document})"
  in
  run "CMD-006 still fires (diagnostic count unchanged)" (fun tag ->
      expect (fires_with_count "CMD-006" c6_src 1) (tag ^ ": count=1"));
  run "CMD-006 emits a label-only move candidate" (fun tag ->
      match candidates_of "CMD-006" c6_src with
      | [ { c_edits = []; c_label } ] ->
          expect (c_label = c6_label) (tag ^ ": label-only move suggestion")
      | _ -> expect false (tag ^ ": expected one label-only candidate"));
  run "CMD-006 candidate NOT in fix field (no auto-apply)" (fun tag ->
      expect (not (fires_with_fix "CMD-006" c6_src)) (tag ^ ": fix=None"));

  let c13_src =
    "\\begin{document}\n\\def\\arraystretch{1.5}\n\\end{document}\n"
  in
  let c13_label =
    "Consider moving \\def\\arraystretch to the preamble, or scope it within a \
     group"
  in
  run "CMD-013 still fires (diagnostic count unchanged)" (fun tag ->
      expect (fires_with_count "CMD-013" c13_src 1) (tag ^ ": count=1"));
  run "CMD-013 emits a label-only move candidate" (fun tag ->
      match candidates_of "CMD-013" c13_src with
      | [ { c_edits = []; c_label } ] ->
          expect (c_label = c13_label) (tag ^ ": label-only move suggestion")
      | _ -> expect false (tag ^ ": expected one label-only candidate"));
  run "CMD-013 candidate NOT in fix field (no auto-apply)" (fun tag ->
      expect (not (fires_with_fix "CMD-013" c13_src)) (tag ^ ": fix=None"));

  let c14_src = "\\begin{document}\n\\AtBeginDocument{x}\n\\end{document}\n" in
  let c14_label =
    "Move \\AtBeginDocument before \\begin{document} (it has no effect \
     afterwards)"
  in
  run "CMD-014 still fires (diagnostic count unchanged)" (fun tag ->
      expect (fires_with_count "CMD-014" c14_src 1) (tag ^ ": count=1"));
  run "CMD-014 emits a label-only move candidate" (fun tag ->
      match candidates_of "CMD-014" c14_src with
      | [ { c_edits = []; c_label } ] ->
          expect (c_label = c14_label) (tag ^ ": label-only move suggestion")
      | _ -> expect false (tag ^ ": expected one label-only candidate"));
  run "CMD-014 candidate NOT in fix field (no auto-apply)" (fun tag ->
      expect (not (fires_with_fix "CMD-014" c14_src)) (tag ^ ": fix=None"));

  (* ══════════════════════════════════════════════════════════════════════
     MOD-002..007: mixed legacy+modern font commands in one paragraph. Candidate
     normalises the LEGACY switch to its NFSS form; identical in shape to the
     MOD-001 candidate for the same token (so no conflicting edits).
     ══════════════════════════════════════════════════════════════════════ *)
  let mod2_src = "Text \\bf bold and \\textbf{x} here." in
  run "MOD-002 still fires (diagnostic count unchanged)" (fun tag ->
      expect (fires_with_count "MOD-002" mod2_src 1) (tag ^ ": count=1"));
  run "MOD-002 candidate normalises \\bf -> \\bfseries" (fun tag ->
      (* "Text " = 5 bytes; "\bf" spans [5,8). *)
      expect
        (has_edit_set "MOD-002" mod2_src [ (5, 8, "\\bfseries") ])
        (tag ^ ": edit \\bf->\\bfseries"));
  run "MOD-002 candidate NOT in fix field (no auto-apply)" (fun tag ->
      expect (not (fires_with_fix "MOD-002" mod2_src)) (tag ^ ": fix=None"));
  run "MOD-002 --apply-fixes leaves source untouched" (fun tag ->
      expect (apply_fix "MOD-002" mod2_src = mod2_src) (tag ^ ": no rewrite"));
  let mod5_src = "Code \\tt mono and \\texttt{x} here." in
  run "MOD-005 candidate normalises \\tt -> \\ttfamily" (fun tag ->
      expect
        (fires_with_count "MOD-005" mod5_src 1
        && has_edit_set "MOD-005" mod5_src [ (5, 8, "\\ttfamily") ])
        (tag ^ ": edit \\tt->\\ttfamily"));

  (* ══════════════════════════════════════════════════════════════════════
     VERB-001: \verb delimiter reused inside the block. Candidate rewrites BOTH
     delimiters to a fresh char absent from the content.
     ══════════════════════════════════════════════════════════════════════ *)
  let v1_src = "verb reuse \\verb|a\\verb b| done" in
  run "VERB-001 still fires" (fun tag ->
      expect (fires "VERB-001" v1_src) (tag ^ ": fires"));
  run "VERB-001 candidate rewrites both delimiters | -> !" (fun tag ->
      (* open | at 16, close | at 25; | occurs in content so '!' is chosen. *)
      expect
        (has_edit_set "VERB-001" v1_src [ (16, 17, "!"); (25, 26, "!") ])
        (tag ^ ": two delimiter edits"));
  run "VERB-001 candidate NOT in fix field (no auto-apply)" (fun tag ->
      expect (not (fires_with_fix "VERB-001" v1_src)) (tag ^ ": fix=None"));
  run "VERB-001 --apply-fixes leaves source untouched" (fun tag ->
      expect (apply_fix "VERB-001" v1_src = v1_src) (tag ^ ": no rewrite"));

  (* ══════════════════════════════════════════════════════════════════════
     VERB-003: trailing spaces inside verbatim. Candidate deletes the run.
     ══════════════════════════════════════════════════════════════════════ *)
  let v3_src = "\\begin{verbatim}\ncode here   \nmore\t\n\\end{verbatim}\n" in
  run "VERB-003 still fires (count = #trailing lines)" (fun tag ->
      expect (fires_with_count "VERB-003" v3_src 2) (tag ^ ": count=2"));
  run "VERB-003 candidate deletes trailing spaces" (fun tag ->
      expect
        (has_edit_set "VERB-003" v3_src [ (26, 29, "") ])
        (tag ^ ": delete 3-space run"));
  run "VERB-003 candidate deletes trailing tab" (fun tag ->
      expect
        (has_edit_set "VERB-003" v3_src [ (34, 35, "") ])
        (tag ^ ": delete tab"));
  run "VERB-003 candidate NOT in fix field (verbatim gate untouched)"
    (fun tag ->
      expect (not (fires_with_fix "VERB-003" v3_src)) (tag ^ ": fix=None"));
  run "VERB-003 --apply-fixes leaves verbatim untouched" (fun tag ->
      expect (apply_fix "VERB-003" v3_src = v3_src) (tag ^ ": no rewrite"));

  (* ══════════════════════════════════════════════════════════════════════
     VERB-004: non-ASCII curly quotes inside verbatim. Candidate -> ASCII.
     ══════════════════════════════════════════════════════════════════════ *)
  let v4_src =
    "\\begin{verbatim}\nsay \xe2\x80\x9chi\xe2\x80\x9d ok\n\\end{verbatim}\n"
  in
  run "VERB-004 still fires (count = #curly quotes)" (fun tag ->
      expect (fires_with_count "VERB-004" v4_src 2) (tag ^ ": count=2"));
  run "VERB-004 candidate replaces opening curly quote with ASCII" (fun tag ->
      expect
        (has_edit_set "VERB-004" v4_src [ (21, 24, "\"") ])
        (tag ^ ": opening quote"));
  run "VERB-004 candidate replaces closing curly quote with ASCII" (fun tag ->
      expect
        (has_edit_set "VERB-004" v4_src [ (26, 29, "\"") ])
        (tag ^ ": closing quote"));
  run "VERB-004 --apply-fixes leaves verbatim untouched" (fun tag ->
      expect (apply_fix "VERB-004" v4_src = v4_src) (tag ^ ": no rewrite"));

  (* ══════════════════════════════════════════════════════════════════════
     SCRIPT-017: inconsistent sub/sup order. Candidate normalises the sub-sup
     occurrence to super-before-sub — the SAME direction as SCRIPT-021.
     ══════════════════════════════════════════════════════════════════════ *)
  let s17_src = "Math $a_1^2$ and $x^3_4$ end." in
  run "SCRIPT-017 still fires" (fun tag ->
      expect (fires "SCRIPT-017" s17_src) (tag ^ ": fires"));
  run "SCRIPT-017 candidate reorders _1^2 -> ^2_1 (matches SCRIPT-021)"
    (fun tag ->
      (* "Math $a" = 7 bytes; "_1^2" spans [7,11). *)
      expect
        (has_edit_set "SCRIPT-017" s17_src [ (7, 11, "^2_1") ])
        (tag ^ ": canonical super-before-sub"));
  run "SCRIPT-017 candidate NOT in fix field (no auto-apply)" (fun tag ->
      expect (not (fires_with_fix "SCRIPT-017" s17_src)) (tag ^ ": fix=None"));
  run "SCRIPT-017 --apply-fixes leaves source untouched" (fun tag ->
      expect (apply_fix "SCRIPT-017" s17_src = s17_src) (tag ^ ": no rewrite"));

  (* ══════════════════════════════════════════════════════════════════════
     MATH-107: mix of \le and \leqslant. Candidate normalises to the majority
     spelling (here two \le vs one \leqslant => convert \leqslant -> \le).
     ══════════════════════════════════════════════════════════════════════ *)
  let m107_src = "Math $a \\le b$ and $c \\le d$ and $e \\leqslant f$." in
  run "MATH-107 still fires (count=1)" (fun tag ->
      expect (fires_with_count "MATH-107" m107_src 1) (tag ^ ": count=1"));
  run "MATH-107 candidate normalises \\leqslant -> \\le (majority)" (fun tag ->
      (* "\leqslant" spans [36,45). *)
      expect
        (has_edit_set "MATH-107" m107_src [ (36, 45, "\\le") ])
        (tag ^ ": leqslant->le"));
  run "MATH-107 candidate NOT in fix field (no auto-apply)" (fun tag ->
      expect (not (fires_with_fix "MATH-107" m107_src)) (tag ^ ": fix=None"));
  run "MATH-107 --apply-fixes leaves source untouched" (fun tag ->
      expect (apply_fix "MATH-107" m107_src = m107_src) (tag ^ ": no rewrite"));
  (* Minority-flip: one \le vs two \leqslant => convert \le -> \leqslant. *)
  let m107b_src = "$a \\le b$, $c \\leqslant d$, $e \\leqslant f$." in
  run "MATH-107 flips direction to the other majority" (fun tag ->
      expect
        (List.exists
           (fun (c : Validators.candidate_fix) ->
             match c.c_edits with
             | [ e ] -> e.Cst_edit.replacement = "\\leqslant"
             | _ -> false)
           (candidates_of "MATH-107" m107b_src))
        (tag ^ ": \\le->\\leqslant when leqslant is majority"));

  (* backlog batch 1 (math-notation) — 5 confirmed-firing candidates *)
  run "MATH-049 lists a \\times-spacing candidate" (fun tag ->
      expect
        (has_label "MATH-049" "$a\\times b$" "Insert a space around \\times")
        (tag ^ ": fires"));
  run "MATH-081 lists a kerning candidate" (fun tag ->
      expect
        (candidates_of "MATH-081" "$\\int_0^1 f(x)dx$" <> [])
        (tag ^ ": fires"));
  run "SCRIPT-004 lists a prime-reorder candidate" (fun tag ->
      expect
        (has_label "SCRIPT-004" "$f'_i$"
           "Reorder prime after subscript (f'_i -> f_i')")
        (tag ^ ": fires"));
  run "SCRIPT-014 lists a brace-log-base candidate" (fun tag ->
      expect
        (has_label "SCRIPT-014" "$\\log_x$"
           "Brace the logarithm base subscript (\\log_x -> \\log_{x})")
        (tag ^ ": fires"));
  run "SCRIPT-020 lists a mathrm-subscript candidate" (fun tag ->
      expect
        (has_label "SCRIPT-020" "$T_{eff}$"
           "Wrap the subscript word in \\mathrm (\\mathrm{eff})")
        (tag ^ ": fires"));
  (* ══════════════════════════════════════════════════════════════════════
     TYPO-041: spacing around \ldots. Candidate inserts a space between a
     leading punctuation mark and a glued `\ldots` (`.\ldots`/`,\ldots`); the
     trailing `\ldots.` case is intentionally NOT suggested.
     ══════════════════════════════════════════════════════════════════════ *)
  let t41_src = "a,\\ldots b" in
  run "TYPO-041 still fires (count=1)" (fun tag ->
      expect (fires_with_count "TYPO-041" t41_src 1) (tag ^ ": count=1"));
  run "TYPO-041 candidate inserts a space after the comma" (fun tag ->
      (* "a" = 1 byte, "," at 1, "\ldots" starts at 2 -> insert at 2. *)
      expect
        (edit_of_label "TYPO-041" t41_src
           "Insert a space between the punctuation and \\ldots"
        = Some (2, 2, " "))
        (tag ^ ": edit"));
  run "TYPO-041 candidate NOT in fix field (no auto-apply)" (fun tag ->
      expect (not (fires_with_fix "TYPO-041" t41_src)) (tag ^ ": fix=None"));
  run "TYPO-041 --apply-fixes leaves source untouched" (fun tag ->
      expect (apply_fix "TYPO-041" t41_src = t41_src) (tag ^ ": no rewrite"));
  run "TYPO-041 gives NO candidate for the \\ldots. sub-case" (fun tag ->
      (* Trailing period after \ldots still counts but is not suggested. *)
      let src = "x\\ldots. y" in
      expect
        (fires_with_count "TYPO-041" src 1 && candidates_of "TYPO-041" src = [])
        (tag ^ ": no trailing-period candidate"));
  run "TYPO-041 candidate dropped inside verbatim" (fun tag ->
      let v = "\\begin{verbatim}\na,\\ldots b\n\\end{verbatim}" in
      expect (candidates_of "TYPO-041" v = []) (tag ^ ": exempt"));

  (* ══════════════════════════════════════════════════════════════════════
     TYPO-047: starred \section*. Candidate removes the star (numbered section).
     ══════════════════════════════════════════════════════════════════════ *)
  let t47_src = "\\section*{Intro}" in
  run "TYPO-047 still fires (count=1)" (fun tag ->
      expect (fires_with_count "TYPO-047" t47_src 1) (tag ^ ": count=1"));
  run "TYPO-047 candidate deletes the star at offset 8" (fun tag ->
      (* "\section" = 8 bytes, "*" at 8 -> delete [8,9). *)
      expect
        (edit_of_label "TYPO-047" t47_src
           "Remove the star to number the section (\\section)"
        = Some (8, 9, ""))
        (tag ^ ": edit"));
  run "TYPO-047 candidate NOT in fix field (no auto-apply)" (fun tag ->
      expect (not (fires_with_fix "TYPO-047" t47_src)) (tag ^ ": fix=None"));
  run "TYPO-047 --apply-fixes leaves source untouched" (fun tag ->
      expect (apply_fix "TYPO-047" t47_src = t47_src) (tag ^ ": no rewrite"));
  run "TYPO-047 candidate dropped inside verbatim" (fun tag ->
      let v = "\\begin{verbatim}\n\\section*{X}\n\\end{verbatim}" in
      expect (candidates_of "TYPO-047" v = []) (tag ^ ": exempt"));
  (* SCRIPT-003: brace ONLY the single already-superscript token, render
     preserving. `$x^a,b$` — `^a,b` begins at offset 2; edit [2,4) `^a` ->
     `^{a}` and leaves the baseline `,b` untouched (does NOT promote it into the
     superscript). *)
  run "SCRIPT-003 lists a single-token brace candidate" (fun tag ->
      expect
        (has_label "SCRIPT-003" "$x^a,b$"
           "Brace the single superscript token (^a,b -> ^{a},b)")
        (tag ^ ": fires"));
  run "SCRIPT-003 candidate braces ONLY the superscript token (no absorb)"
    (fun tag ->
      expect
        (edit_of_label "SCRIPT-003" "$x^a,b$"
           "Brace the single superscript token (^a,b -> ^{a},b)"
        = Some (2, 4, "^{a}"))
        (tag ^ ": edit"));

  (* ══════════════════════════════════════════════════════════════════════
     BIB-015: redundant trailing period in a `title`/`note` field. Candidate
     deletes just the period byte before the closing brace.
     ══════════════════════════════════════════════════════════════════════ *)
  let b15_src = "@article{k, title = {Foo.}}" in
  run "BIB-015 still fires (count=1)" (fun tag ->
      expect (fires_with_count "BIB-015" b15_src 1) (tag ^ ": count=1"));
  run "BIB-015 candidate deletes the trailing period at offset 24" (fun tag ->
      (* "@article{k, title = {Foo" = 24 bytes; "." at 24 -> delete [24,25). *)
      expect
        (edit_of_label "BIB-015" b15_src "Remove redundant trailing period"
        = Some (24, 25, ""))
        (tag ^ ": edit"));
  run "BIB-015 candidate NOT in fix field (no auto-apply)" (fun tag ->
      expect (not (fires_with_fix "BIB-015" b15_src)) (tag ^ ": fix=None"));
  run "BIB-015 --apply-fixes leaves source untouched" (fun tag ->
      expect (apply_fix "BIB-015" b15_src = b15_src) (tag ^ ": no rewrite"));
  run "BIB-015 candidate dropped inside verbatim" (fun tag ->
      let v = "\\begin{verbatim}\ntitle = {Foo.}\n\\end{verbatim}" in
      expect (candidates_of "BIB-015" v = []) (tag ^ ": exempt"));

  (* ══════════════════════════════════════════════════════════════════════
     BIB-017: sentence-case title ending with a punctuation mark. Candidate
     removes a trailing PERIOD only; `?`/`!` are meaningful so they count but
     get no candidate.
     ══════════════════════════════════════════════════════════════════════ *)
  let b17_src = "@article{k, title = {Foo.}}" in
  run "BIB-017 still fires (count=1)" (fun tag ->
      expect (fires_with_count "BIB-017" b17_src 1) (tag ^ ": count=1"));
  run "BIB-017 candidate deletes the trailing period at offset 24" (fun tag ->
      expect
        (edit_of_label "BIB-017" b17_src "Remove redundant trailing period"
        = Some (24, 25, ""))
        (tag ^ ": edit"));
  run "BIB-017 question mark counts but yields no candidate" (fun tag ->
      let q = "@article{k, title = {Really?}}" in
      expect
        (fires_with_count "BIB-017" q 1 && candidates_of "BIB-017" q = [])
        (tag ^ ": no ?-candidate"));
  run "BIB-017 candidate NOT in fix field (no auto-apply)" (fun tag ->
      expect (not (fires_with_fix "BIB-017" b17_src)) (tag ^ ": fix=None"));
  run "BIB-017 --apply-fixes leaves source untouched" (fun tag ->
      expect (apply_fix "BIB-017" b17_src = b17_src) (tag ^ ": no rewrite"));
  run "BIB-017 candidate dropped inside verbatim" (fun tag ->
      let v = "\\begin{verbatim}\ntitle = {Foo.}\n\\end{verbatim}" in
      expect (candidates_of "BIB-017" v = []) (tag ^ ": exempt"));

  (* ══════════════════════════════════════════════════════════════════════
     CHEM-008: bare state symbol (aq)/(s)/(l)/(g) in math. Candidate wraps it in
     \text so it typesets upright; already-wrapped ones are skipped.
     ══════════════════════════════════════════════════════════════════════ *)
  let c8_src = "$NaCl(aq)$" in
  run "CHEM-008 still fires (count=1)" (fun tag ->
      expect (fires_with_count "CHEM-008" c8_src 1) (tag ^ ": count=1"));
  run "CHEM-008 candidate wraps (aq) in \\text at offset 5" (fun tag ->
      (* "$NaCl" = 5 bytes; "(aq)" spans [5,9) -> \text{(aq)}. *)
      expect
        (edit_of_label "CHEM-008" c8_src
           "Wrap the state symbol in \\text ((aq) -> \\text{(aq)})"
        = Some (5, 9, "\\text{(aq)}"))
        (tag ^ ": edit"));
  run "CHEM-008 no candidate for already-\\text-wrapped symbol" (fun tag ->
      expect
        (candidates_of "CHEM-008" "$NaCl\\text{(s)}$" = [])
        (tag ^ ": wrapped skipped"));
  run "CHEM-008 candidate NOT in fix field (no auto-apply)" (fun tag ->
      expect (not (fires_with_fix "CHEM-008" c8_src)) (tag ^ ": fix=None"));
  run "CHEM-008 --apply-fixes leaves source untouched" (fun tag ->
      expect (apply_fix "CHEM-008" c8_src = c8_src) (tag ^ ": no rewrite"));
  run "CHEM-008 candidate dropped outside math (vcu-exempt)" (fun tag ->
      expect
        (candidates_of "CHEM-008" "NaCl(aq) dissolves" = [])
        (tag ^ ": not in math"));

  (* ══════════════════════════════════════════════════════════════════════
     DOC-005: \keywords present but no pdfkeywords in \hypersetup. Candidate
     copies the keyword text into a pdfkeywords={…} metadata key (PDF/XMP only —
     render-preserving).
     ══════════════════════════════════════════════════════════════════════ *)
  let d5_src = "\\keywords{a, b}\n\\hypersetup{pdftitle={T}}\n" in
  run "DOC-005 still fires (count=1)" (fun tag ->
      expect (fires_with_count "DOC-005" d5_src 1) (tag ^ ": count=1"));
  run "DOC-005 candidate inserts pdfkeywords after \\hypersetup{" (fun tag ->
      (* "\keywords{a, b}\n" = 16 bytes; "\hypersetup{" spans [16,28), insert
         lands at offset 28. *)
      expect
        (edit_of_label "DOC-005" d5_src
           "Add pdfkeywords={…} to \\hypersetup so the PDF/XMP metadata \
            carries the keywords"
        = Some (28, 28, "pdfkeywords={a, b}, "))
        (tag ^ ": edit"));
  run "DOC-005 no candidate when pdfkeywords already present" (fun tag ->
      expect
        (candidates_of "DOC-005"
           "\\keywords{a}\n\\hypersetup{pdfkeywords={a}}\n"
        = [])
        (tag ^ ": already set (diagnostic silent)"));
  run "DOC-005 candidate NOT in fix field (no auto-apply)" (fun tag ->
      expect (not (fires_with_fix "DOC-005" d5_src)) (tag ^ ": fix=None"));
  run "DOC-005 --apply-fixes leaves source untouched" (fun tag ->
      expect (apply_fix "DOC-005" d5_src = d5_src) (tag ^ ": no rewrite"));
  (* ══════════════════════════════════════════════════════════════════════ MATH
     C4 rendering-intent candidates (MATH-020/021/024/028/030/033/037/ 040/041).
     Each suggests the rule's intended normalisation; render-changing is
     expected (Bucket-C = review-only, never auto-applied).
     ══════════════════════════════════════════════════════════════════════ *)
  (* MATH-020: insert \cdot between a coefficient and a vector macro. *)
  let m020 = "$2\\vec{v}$" in
  run "MATH-020 still fires (count=1)" (fun tag ->
      expect (fires_with_count "MATH-020" m020 1) (tag ^ ": count=1"));
  run "MATH-020 candidate inserts \\cdot after the digit" (fun tag ->
      (* "$2" = 2 bytes; \cdot inserted at offset 2 (before \vec). *)
      expect
        (edit_of_label "MATH-020" m020
           "Insert \\cdot between coefficient and vector"
        = Some (2, 2, "\\cdot"))
        (tag ^ ": edit"));
  run "MATH-020 candidate NOT auto-applied" (fun tag ->
      expect
        ((not (fires_with_fix "MATH-020" m020))
        && apply_fix "MATH-020" m020 = m020)
        (tag ^ ": byte-identical"));

  (* MATH-021: |x| -> \lvert x \rvert (two edits). *)
  let m021 = "$|x|$" in
  run "MATH-021 still fires (count=1)" (fun tag ->
      expect (fires_with_count "MATH-021" m021 1) (tag ^ ": count=1"));
  run "MATH-021 candidate rewrites both bars" (fun tag ->
      expect
        (has_edit_set "MATH-021" m021
           [ (1, 2, "\\lvert "); (3, 4, " \\rvert") ])
        (tag ^ ": edits"));
  run "MATH-021 candidate NOT auto-applied" (fun tag ->
      expect (apply_fix "MATH-021" m021 = m021) (tag ^ ": byte-identical"));

  (* MATH-024: orphan \label{eq:...} — LABEL-ONLY candidate (cross-file
     risk). *)
  let m024 = "\\label{eq:unused}" in
  run "MATH-024 still fires (count=1)" (fun tag ->
      expect (fires_with_count "MATH-024" m024 1) (tag ^ ": count=1"));
  run "MATH-024 emits a label-only candidate naming the key" (fun tag ->
      expect
        (has_label "MATH-024" m024
           "Delete unreferenced equation label \\label{eq:unused} (confirm it \
            is not \\ref'd in another file)")
        (tag ^ ": label"));
  run "MATH-024 candidate carries no edit (label-only)" (fun tag ->
      expect
        (List.for_all
           (fun (c : Validators.candidate_fix) -> c.c_edits = [])
           (candidates_of "MATH-024" m024))
        (tag ^ ": empty c_edits"));
  run "MATH-024 clean when the label is referenced" (fun tag ->
      expect
        (candidates_of "MATH-024" "\\label{eq:u}\nSee \\ref{eq:u}" = [])
        (tag ^ ": no orphan"));

  (* MATH-028: array without a column spec — suggest a default {c}. *)
  let m028 = "$\\begin{array} a \\end{array}$" in
  run "MATH-028 still fires (count=1)" (fun tag ->
      expect (fires_with_count "MATH-028" m028 1) (tag ^ ": count=1"));
  run "MATH-028 candidate inserts {c} after \\begin{array}" (fun tag ->
      (* "$" + "\begin{array}" (13) => insertion point at offset 14. *)
      expect
        (edit_of_label "MATH-028" m028
           "Add a default column spec {c} to the array"
        = Some (14, 14, "{c}"))
        (tag ^ ": edit"));
  run "MATH-028 no candidate when a spec is already present" (fun tag ->
      expect
        (candidates_of "MATH-028" "$\\begin{array}{c} a \\end{array}$" = [])
        (tag ^ ": has spec"));

  (* MATH-030: drop \displaystyle in inline math (deletes control word +
     space). *)
  let m030 = "$\\displaystyle x$" in
  run "MATH-030 still fires (count=1)" (fun tag ->
      expect (fires_with_count "MATH-030" m030 1) (tag ^ ": count=1"));
  run "MATH-030 candidate deletes \\displaystyle and the trailing space"
    (fun tag ->
      expect
        (edit_of_label "MATH-030" m030 "Remove \\displaystyle in inline math"
        = Some (1, 15, ""))
        (tag ^ ": edit"));
  run "MATH-030 candidate NOT auto-applied" (fun tag ->
      expect (apply_fix "MATH-030" m030 = m030) (tag ^ ": byte-identical"));

  (* MATH-033: \pm in text -> $\pm$; \pmod (letter after) gets no candidate. *)
  let m033 = "We use \\pm here." in
  run "MATH-033 still fires (count=1)" (fun tag ->
      expect (fires_with_count "MATH-033" m033 1) (tag ^ ": count=1"));
  run "MATH-033 candidate wraps \\pm in inline math" (fun tag ->
      (* "We use " = 7 bytes; \pm spans [7,10). *)
      expect
        (edit_of_label "MATH-033" m033 "Wrap \\pm in inline math: $\\pm$"
        = Some (7, 10, "$\\pm$"))
        (tag ^ ": edit"));
  run "MATH-033 \\pmod counts but yields no candidate (boundary check)"
    (fun tag ->
      let q = "Use \\pmod arithmetic" in
      expect
        (fires_with_count "MATH-033" q 1 && candidates_of "MATH-033" q = [])
        (tag ^ ": no \\pmod candidate"));

  (* MATH-037: \sfrac -> \tfrac inside math. *)
  let m037 = "$\\sfrac{1}{2}$" in
  run "MATH-037 still fires (count=1)" (fun tag ->
      expect (fires_with_count "MATH-037" m037 1) (tag ^ ": count=1"));
  run "MATH-037 candidate replaces \\sfrac with \\tfrac" (fun tag ->
      expect
        (edit_of_label "MATH-037" m037 "Replace \\sfrac with \\tfrac in math"
        = Some (1, 7, "\\tfrac"))
        (tag ^ ": edit"));

  (* MATH-040: \ldots between operators -> \cdots. *)
  let m040 = "$a+\\ldots+b$" in
  run "MATH-040 still fires (count=1)" (fun tag ->
      expect (fires_with_count "MATH-040" m040 1) (tag ^ ": count=1"));
  run "MATH-040 candidate replaces \\ldots with \\cdots" (fun tag ->
      (* "$a+" = 3 bytes; \ldots spans [3,9). *)
      expect
        (edit_of_label "MATH-040" m040
           "Replace \\ldots with centred \\cdots between operators"
        = Some (3, 9, "\\cdots"))
        (tag ^ ": edit"));

  (* MATH-041: inline \int_ -> add \limits. *)
  let m041 = "$\\int_0^1$" in
  run "MATH-041 still fires (count=1)" (fun tag ->
      expect (fires_with_count "MATH-041" m041 1) (tag ^ ": count=1"));
  run "MATH-041 candidate inserts \\limits after \\int" (fun tag ->
      (* "$\int" = 5 bytes; \limits inserted before the _ at offset 5. *)
      expect
        (edit_of_label "MATH-041" m041
           "Add \\limits to stack the inline integral limits"
        = Some (5, 5, "\\limits"))
        (tag ^ ": edit"));
  run "MATH-041 candidate dropped inside verbatim" (fun tag ->
      let v = "\\begin{verbatim}\n$\\int_0^1$\n\\end{verbatim}" in
      expect (candidates_of "MATH-041" v = []) (tag ^ ": exempt"));

  (* ======================================================================
     Bucket-C batch (v27.1.48): SCRIPT / REF / SPC-026 / TIKZ rename &
     structural candidates
     ══════════════════════════════════════════════════════════════════════ *)

  (* SCRIPT-002: superscript Unicode hyphen -> ^{-} *)
  let s002 = "$x^\xe2\x80\x91$" (* U+2011 non-breaking hyphen *) in
  run "SCRIPT-002 still fires (count=1)" (fun tag ->
      expect (fires_with_count "SCRIPT-002" s002 1) (tag ^ ": count=1"));
  run "SCRIPT-002 candidate replaces the Unicode hyphen with {-}" (fun tag ->
      (* "$x^" = 3 bytes; the 3-byte hyphen spans [3,6) -> {-} *)
      expect
        (edit_of_label "SCRIPT-002" s002
           "Use a braced ASCII minus ^{-} for the superscript dash"
        = Some (3, 6, "{-}"))
        (tag ^ ": edit [3,6)->{-}"));
  run "SCRIPT-002 --apply-fixes leaves source byte-identical" (fun tag ->
      expect (apply_fix "SCRIPT-002" s002 = s002) (tag ^ ": no rewrite"));
  run "SCRIPT-002 candidate dropped in verbatim" (fun tag ->
      expect
        (candidates_of "SCRIPT-002" "\\verb|$x^\xe2\x80\x91$|" = [])
        (tag ^ ": vcu-dropped"));

  (* SCRIPT-012: >3 primes -> ^{(n)} *)
  let s012 = "$f''''$" in
  run "SCRIPT-012 still fires (count=1)" (fun tag ->
      expect (fires_with_count "SCRIPT-012" s012 1) (tag ^ ": count=1"));
  run "SCRIPT-012 candidate replaces the 4-prime run with ^{(4)}" (fun tag ->
      (* "$f" = 2 bytes; four primes span [2,6) -> ^{(4)} *)
      expect
        (edit_of_label "SCRIPT-012" s012
           "Use derivative-order ^{(n)} for a long prime run"
        = Some (2, 6, "^{(4)}"))
        (tag ^ ": edit [2,6)->^{(4)}"));
  run "SCRIPT-012 five primes -> ^{(5)}" (fun tag ->
      expect
        (edit_of_label "SCRIPT-012" "$g'''''$"
           "Use derivative-order ^{(n)} for a long prime run"
        = Some (2, 7, "^{(5)}"))
        (tag ^ ": edit [2,7)->^{(5)}"));
  run "SCRIPT-012 --apply-fixes leaves source byte-identical" (fun tag ->
      expect (apply_fix "SCRIPT-012" s012 = s012) (tag ^ ": no rewrite"));

  (* SCRIPT-013: _{+}/_{-} -> _{\pm}/_{\mp} *)
  let s013 = "$x_{+}$" in
  run "SCRIPT-013 still fires (count=1)" (fun tag ->
      expect (fires_with_count "SCRIPT-013" s013 1) (tag ^ ": count=1"));
  run "SCRIPT-013 candidate rewrites the + to \\pm" (fun tag ->
      (* "$x_{" = 4 bytes; the sign is at [4,5) -> \pm *)
      expect
        (edit_of_label "SCRIPT-013" s013 "Wrap subscript sign as \\pm/\\mp"
        = Some (4, 5, "\\pm"))
        (tag ^ ": edit [4,5)->\\pm"));
  run "SCRIPT-013 minus -> \\mp" (fun tag ->
      expect
        (edit_of_label "SCRIPT-013" "$y_{-}$" "Wrap subscript sign as \\pm/\\mp"
        = Some (4, 5, "\\mp"))
        (tag ^ ": edit [4,5)->\\mp"));

  (* SCRIPT-022: ^{'''...} stacked >3 -> ^{(n)} *)
  let s022 = "$h^{''''}$" in
  run "SCRIPT-022 still fires (count=1)" (fun tag ->
      expect (fires_with_count "SCRIPT-022" s022 1) (tag ^ ": count=1"));
  run "SCRIPT-022 candidate replaces ^{''''} with ^{(4)}" (fun tag ->
      (* "$h" = 2 bytes; "^{''''}" spans [2,9) -> ^{(4)} *)
      expect
        (edit_of_label "SCRIPT-022" s022
           "Use derivative-order ^{(n)} for a stacked prime group"
        = Some (2, 9, "^{(4)}"))
        (tag ^ ": edit [2,9)->^{(4)}"));

  (* REF-002: duplicate label -> label-only per collision (zero-width insert) *)
  let r002 = "\\label{x}\ntext\n\\label{x}" in
  run "REF-002 still fires (count=1)" (fun tag ->
      expect (fires_with_count "REF-002" r002 1) (tag ^ ": count=1"));
  run "REF-002 emits a duplicate-rename label candidate" (fun tag ->
      expect
        (has_label "REF-002" r002 "Rename one of the duplicate labels \"x\"")
        (tag ^ ": label"));
  run "REF-002 candidate is byte-safe (empty replacement, no rewrite)"
    (fun tag -> expect (apply_fix "REF-002" r002 = r002) (tag ^ ": no rewrite"));

  (* REF-003: label with spaces -> in-file rename (def + refs) *)
  let r003 = "\\label{my fig}\nSee \\ref{my fig}." in
  run "REF-003 still fires (count=1)" (fun tag ->
      expect (fires_with_count "REF-003" r003 1) (tag ^ ": count=1"));
  run "REF-003 candidate renames def + in-file ref (spaces -> hyphens)"
    (fun tag ->
      match candidates_of "REF-003" r003 with
      | [ { c_edits; c_label } ] -> (
          match Cst_edit.apply_all r003 c_edits with
          | Ok out ->
              expect
                (c_label = "Replace spaces in the label with hyphens"
                && out = "\\label{my-fig}\nSee \\ref{my-fig}.")
                (tag ^ ": def+ref both renamed")
          | Error _ -> expect false (tag ^ ": edits should apply cleanly"))
      | _ -> expect false (tag ^ ": expected one candidate"));
  run "REF-003 --apply-fixes leaves source byte-identical" (fun tag ->
      expect (apply_fix "REF-003" r003 = r003) (tag ^ ": no rewrite"));

  (* REF-004: uppercase label -> lowercase rename (def + refs) *)
  let r004 = "\\label{Fig:Intro}\n\\ref{Fig:Intro}" in
  run "REF-004 still fires (count=1)" (fun tag ->
      expect (fires_with_count "REF-004" r004 1) (tag ^ ": count=1"));
  run "REF-004 candidate lowercases def + in-file ref" (fun tag ->
      match candidates_of "REF-004" r004 with
      | [ { c_edits; c_label } ] -> (
          match Cst_edit.apply_all r004 c_edits with
          | Ok out ->
              expect
                (c_label = "Lowercase the label"
                && out = "\\label{fig:intro}\n\\ref{fig:intro}")
                (tag ^ ": lowercased def+ref")
          | Error _ -> expect false (tag ^ ": edits should apply cleanly"))
      | _ -> expect false (tag ^ ": expected one candidate"));

  (* REF-005: no prefix -> label-only (no determinate prefix) *)
  let r005 = "\\label{intro}" in
  run "REF-005 still fires (count=1)" (fun tag ->
      expect (fires_with_count "REF-005" r005 1) (tag ^ ": count=1"));
  run "REF-005 emits a label-only add-prefix candidate" (fun tag ->
      expect
        (has_label "REF-005" r005
           "Add a type prefix (fig:/tab:/eq:/sec:) to the label")
        (tag ^ ": label"));
  run "REF-005 candidate is byte-safe (no rewrite)" (fun tag ->
      expect (apply_fix "REF-005" r005 = r005) (tag ^ ": no rewrite"));

  (* REF-007: cite key whitespace -> strip whitespace from the argument *)
  let r007 = "\\cite{foo bar}" in
  run "REF-007 still fires (count=1)" (fun tag ->
      expect (fires_with_count "REF-007" r007 1) (tag ^ ": count=1"));
  run "REF-007 candidate strips whitespace from the cite argument" (fun tag ->
      (* "\cite{" = 6 bytes; "foo bar" spans [6,13) -> "foobar" *)
      expect
        (edit_of_label "REF-007" r007 "Strip whitespace from the cite key"
        = Some (6, 13, "foobar"))
        (tag ^ ": edit [6,13)->foobar"));
  run "REF-007 --apply-fixes leaves source byte-identical" (fun tag ->
      expect (apply_fix "REF-007" r007 = r007) (tag ^ ": no rewrite"));

  (* SPC-026: mixed \item indentation -> normalise to modal width *)
  let sp26 =
    "\\begin{itemize}\n  \\item a\n  \\item b\n      \\item c\n\\end{itemize}"
  in
  run "SPC-026 still fires (count=1)" (fun tag ->
      expect (fires_with_count "SPC-026" sp26 1) (tag ^ ": count=1"));
  run "SPC-026 candidate normalises the odd \\item to the modal 2-space indent"
    (fun tag ->
      match candidates_of "SPC-026" sp26 with
      | [ { c_edits; c_label } ] -> (
          match Cst_edit.apply_all sp26 c_edits with
          | Ok out ->
              expect
                (c_label = "Normalise \\item indentation to the modal width"
                && out
                   = "\\begin{itemize}\n\
                     \  \\item a\n\
                     \  \\item b\n\
                     \  \\item c\n\
                      \\end{itemize}")
                (tag ^ ": third \\item re-indented to 2 spaces")
          | Error _ -> expect false (tag ^ ": edits should apply cleanly"))
      | _ -> expect false (tag ^ ": expected one candidate"));
  run "SPC-026 --apply-fixes leaves source byte-identical" (fun tag ->
      expect (apply_fix "SPC-026" sp26 = sp26) (tag ^ ": no rewrite"));

  (* TIKZ-001: tikzpicture outside figure -> label-only wrap *)
  let t001 = "\\begin{tikzpicture}\n\\draw (0,0);\n\\end{tikzpicture}" in
  run "TIKZ-001 still fires (count=1)" (fun tag ->
      expect (fires_with_count "TIKZ-001" t001 1) (tag ^ ": count=1"));
  run "TIKZ-001 emits a label-only figure-wrap candidate" (fun tag ->
      expect
        (has_label "TIKZ-001" t001
           "Wrap the tikzpicture in a figure environment")
        (tag ^ ": label"));
  run "TIKZ-001 candidate is byte-safe (no rewrite)" (fun tag ->
      expect (apply_fix "TIKZ-001" t001 = t001) (tag ^ ": no rewrite"));

  (* TIKZ-003: non-math axis label -> $...$ wrap. The label must sit in the axis
     BODY (the rule skips the `[...]` option block, as extract_env_blocks
     does). *)
  let t003 = "\\begin{axis}\nxlabel={time}\n\\end{axis}" in
  run "TIKZ-003 still fires (count=1)" (fun tag ->
      expect (fires_with_count "TIKZ-003" t003 1) (tag ^ ": count=1"));
  run "TIKZ-003 candidate wraps the label text in $...$" (fun tag ->
      (* "\begin{axis}\nxlabel={" = 21 bytes; "time" spans [21,25) -> $time$ *)
      expect
        (edit_of_label "TIKZ-003" t003 "Wrap the axis label in math mode ($…$)"
        = Some (21, 25, "$time$"))
        (tag ^ ": edit [21,25)->$time$"));
  run "TIKZ-003 already-math label yields no candidate" (fun tag ->
      let s = "\\begin{axis}\nxlabel={$t$}\n\\end{axis}" in
      expect (candidates_of "TIKZ-003" s = []) (tag ^ ": no candidate"));

  (* TIKZ-004: hard RGB -> label-only xcolor suggestion *)
  let t004 = "\\draw[color={rgb,255:red,1}] (0,0);" in
  run "TIKZ-004 still fires (count=1)" (fun tag ->
      expect (fires_with_count "TIKZ-004" t004 1) (tag ^ ": count=1"));
  run "TIKZ-004 emits a label-only xcolor candidate" (fun tag ->
      expect
        (has_label "TIKZ-004" t004
           "Define a named xcolor instead of a hard-coded RGB value")
        (tag ^ ": label"));
  run "TIKZ-004 candidate is byte-safe (no rewrite)" (fun tag ->
      expect (apply_fix "TIKZ-004" t004 = t004) (tag ^ ": no rewrite"));

  (* ======================================================================
     STYLE candidate family (v27.1.48) — intent-dependent style suggestions.
     STYLE-* are L4 Class-D rules, so they only surface via
     [run_all_with_class_d] (which [candidates_of]/[edit_of_label] use); the
     run_all-based [fires]/[apply_fix]/[fires_with_fix] helpers do NOT see them.
     A non-empty candidate list therefore proves the rule fired; [fix = None] on
     the Class-D result proves it is never auto-applied. --apply-fixes-for
     byte-identity is verified separately at the CLI level. *)
  let style_no_fix id src =
    let results = Validators.run_all_with_class_d src in
    match List.find_opt (fun (r : Validators.result) -> r.id = id) results with
    | Some r -> r.fix = None && r.candidate_fixes <> []
    | None -> false
  in

  (* STYLE-014: contraction -> expansion *)
  let s14 = "This doesn't work." in
  run "STYLE-014 emits expansion candidate" (fun tag ->
      (* "This " = 5 bytes; "doesn't" spans [5,12). *)
      expect
        (edit_of_label "STYLE-014" s14
           "Expand contraction \"doesn't\" to \"does not\""
        = Some (5, 12, "does not"))
        (tag ^ ": edit"));
  run "STYLE-014 preserves leading capital" (fun tag ->
      expect
        (has_label "STYLE-014" "Don't stop."
           "Expand contraction \"Don't\" to \"Do not\"")
        (tag ^ ": capital"));
  run "STYLE-014 candidate not in fix field (no auto-apply)" (fun tag ->
      expect (style_no_fix "STYLE-014" s14) (tag ^ ": fix=None"));

  (* STYLE-016: Latin abbrev missing comma *)
  let s16 = "See e.g. Smith." in
  run "STYLE-016 emits insert-comma candidate" (fun tag ->
      (* "See " = 4 bytes; "e.g." spans [4,8); insert `,` at 8. *)
      expect
        (edit_of_label "STYLE-016" s16 "Insert comma after \"e.g.\""
        = Some (8, 8, ","))
        (tag ^ ": edit"));
  run "STYLE-016 candidate not in fix field (no auto-apply)" (fun tag ->
      expect (style_no_fix "STYLE-016" s16) (tag ^ ": fix=None"));

  (* STYLE-022: serial (Oxford) comma missing *)
  let s22 = "apples, oranges and pears" in
  run "STYLE-022 emits Oxford-comma candidate" (fun tag ->
      (* " and " (the space before "and") starts at offset 15. *)
      expect
        (edit_of_label "STYLE-022" s22
           "Insert serial (Oxford) comma before \"and\""
        = Some (15, 15, ","))
        (tag ^ ": edit"));
  run "STYLE-022 candidate not in fix field (no auto-apply)" (fun tag ->
      expect (style_no_fix "STYLE-022" s22) (tag ^ ": fix=None"));

  (* STYLE-026: repeated word *)
  let s26 = "the the method" in
  run "STYLE-026 emits remove-duplicate candidate" (fun tag ->
      (* first "the" = [0,3), gap+second "the" = [3,7). *)
      expect
        (edit_of_label "STYLE-026" s26 "Remove duplicated word \"the\""
        = Some (3, 7, ""))
        (tag ^ ": edit"));
  run "STYLE-026 candidate not in fix field (no auto-apply)" (fun tag ->
      expect (style_no_fix "STYLE-026" s26) (tag ^ ": fix=None"));

  (* STYLE-035: and/or -> or *)
  let s35 = "true and/or false" in
  run "STYLE-035 emits and/or->or candidate" (fun tag ->
      (* "true " = 5 bytes; "and/or" spans [5,11). *)
      expect
        (edit_of_label "STYLE-035" s35 "Replace \"and/or\" with \"or\""
        = Some (5, 11, "or"))
        (tag ^ ": edit"));
  run "STYLE-035 candidate not in fix field (no auto-apply)" (fun tag ->
      expect (style_no_fix "STYLE-035" s35) (tag ^ ": fix=None"));

  (* STYLE-036: Latin phrase italicisation *)
  let s36 = "See cf. above." in
  run "STYLE-036 emits \\emph-wrap candidate" (fun tag ->
      (* "See " = 4 bytes; "cf." spans [4,7). *)
      expect
        (edit_of_label "STYLE-036" s36
           "Italicise Latin phrase \"cf.\" with \\emph"
        = Some (4, 7, "\\emph{cf.}"))
        (tag ^ ": edit"));
  run "STYLE-036 skips an already-italicised phrase" (fun tag ->
      expect
        (candidates_of "STYLE-036" "See \\emph{cf.} above." = [])
        (tag ^ ": already emph"));
  run "STYLE-036 candidate not in fix field (no auto-apply)" (fun tag ->
      expect (style_no_fix "STYLE-036" s36) (tag ^ ": fix=None"));

  (* STYLE-040: exclamation -> period *)
  let s40 = "Great result!" in
  run "STYLE-040 emits period candidate" (fun tag ->
      (* "Great result" = 12 bytes; "!" at [12,13). *)
      expect
        (edit_of_label "STYLE-040" s40 "Replace exclamation mark with a period"
        = Some (12, 13, "."))
        (tag ^ ": edit"));
  run "STYLE-040 candidate not in fix field (no auto-apply)" (fun tag ->
      expect (style_no_fix "STYLE-040" s40) (tag ^ ": fix=None"));

  (* STYLE-041: footnote terminal period *)
  let s41 = "x\\footnote{A note}" in
  run "STYLE-041 emits add-period candidate" (fun tag ->
      (* "x\footnote{" = 11 bytes; body "A note" = [11,17); insert at 17. *)
      expect
        (edit_of_label "STYLE-041" s41 "Add terminal period to footnote"
        = Some (17, 17, "."))
        (tag ^ ": edit"));
  run "STYLE-041 candidate not in fix field (no auto-apply)" (fun tag ->
      expect (style_no_fix "STYLE-041" s41) (tag ^ ": fix=None"));

  (* STYLE-049: heading trailing colon *)
  let s49 = "\\section{Intro:}" in
  run "STYLE-049 emits remove-colon candidate" (fun tag ->
      (* "\section{Intro" = 14 bytes; ":" at [14,15). *)
      expect
        (edit_of_label "STYLE-049" s49
           "Remove the colon at the end of the heading"
        = Some (14, 15, ""))
        (tag ^ ": edit"));
  run "STYLE-049 candidate not in fix field (no auto-apply)" (fun tag ->
      expect (style_no_fix "STYLE-049" s49) (tag ^ ": fix=None"));

  finalise "candidate_fixes"
