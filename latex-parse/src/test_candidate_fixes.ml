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
           "Use bmatrix for a square-bracketed matrix")
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

  finalise "candidate_fixes"
