(** Unit tests for [Project_model]. *)

open Latex_parse_lib
open Test_helpers

let tmp_dir =
  let d = Filename.temp_file "test_project_" "" in
  Sys.remove d;
  Unix.mkdir d 0o755;
  d

let write_file name content =
  let path = Filename.concat tmp_dir name in
  let oc = open_out path in
  output_string oc content;
  close_out oc;
  path

let cleanup_dir () =
  Array.iter
    (fun f -> try Sys.remove (Filename.concat tmp_dir f) with _ -> ())
    (Sys.readdir tmp_dir);
  try Unix.rmdir tmp_dir with _ -> ()

let () =
  (* Simple root-only project *)
  run "of_root accepts a minimal tex file" (fun tag ->
      let path =
        write_file "root.tex"
          "\\documentclass{article}\n\\begin{document}\nhi\n\\end{document}\n"
      in
      match Project_model.of_root path with
      | Ok proj ->
          expect
            (List.length (Project_model.all_files proj) = 1)
            (tag ^ ": single-file project");
          expect
            ((Project_model.root_file proj).is_root = true)
            (tag ^ ": root marked is_root")
      | Error _ -> expect false (tag ^ ": should succeed"));

  (* Missing file *)
  run "of_root rejects missing file" (fun tag ->
      match Project_model.of_root "/nonexistent/ghost.tex" with
      | Error (`File_not_found _) -> expect true (tag ^ ": correct error")
      | _ -> expect false (tag ^ ": should error on missing file"));

  (* Non-.tex extension *)
  run "of_root rejects non-tex" (fun tag ->
      let path = write_file "readme.md" "# not tex\n" in
      match Project_model.of_root path with
      | Error (`Not_latex _) -> expect true (tag ^ ": correct error")
      | _ -> expect false (tag ^ ": should reject non-tex"));

  (* Multi-file with \input *)
  run "of_root scans \\input directives" (fun tag ->
      let _ = write_file "intro.tex" "intro content\n" in
      let root =
        write_file "main.tex"
          "\\documentclass{article}\n\\input{intro}\n\\end{document}\n"
      in
      match Project_model.of_root root with
      | Ok proj ->
          expect
            (List.length (Project_model.all_files proj) = 2)
            (tag ^ ": root + 1 input")
      | Error _ -> expect false (tag ^ ": should succeed"));

  (* Engine and features *)
  run "of_root passes engine + features through" (fun tag ->
      let path = write_file "e.tex" "\\documentclass{article}\n" in
      match
        Project_model.of_root ~engine:Project_model.Xelatex
          ~declared_features:[ Project_model.Opentype_fonts ]
          path
      with
      | Ok proj ->
          expect (proj.engine = Project_model.Xelatex) (tag ^ ": engine");
          expect
            (proj.declared_features = [ Project_model.Opentype_fonts ])
            (tag ^ ": features")
      | Error _ -> expect false (tag ^ ": should succeed"));

  (* engine_to_string / feature_to_string basic sanity *)
  run "string conversions" (fun tag ->
      expect
        (Project_model.engine_to_string Project_model.Pdflatex = "pdflatex")
        (tag ^ ": pdflatex");
      expect
        (Project_model.feature_to_string Project_model.Unicode_math
        = "unicode_math")
        (tag ^ ": unicode_math"));

  (* R7-4: recursive \input cycle detection. of_root is single-level, so an
     a→b→a cycle only shows up under has_include_cycle's transitive walk.
     pdflatex fatals on it ("TeX capacity exceeded [text input levels]"). *)
  run "has_include_cycle: a->b->a detected" (fun tag ->
      let a =
        write_file "cyc_a.tex"
          "\\documentclass{article}\\begin{document}x\\input{cyc_b}\\end{document}"
      in
      let _ = write_file "cyc_b.tex" "hop\\input{cyc_a}\n" in
      expect (Project_model.has_include_cycle a) (tag ^ ": cycle fires"));

  run "has_include_cycle: acyclic chain a->b->c ok" (fun tag ->
      let a =
        write_file "acy_a.tex"
          "\\documentclass{article}\\begin{document}\\input{acy_b}\\end{document}"
      in
      let _ = write_file "acy_b.tex" "\\input{acy_c}\n" in
      let _ = write_file "acy_c.tex" "leaf\n" in
      expect
        (not (Project_model.has_include_cycle a))
        (tag ^ ": acyclic stays clean"));

  (* REGRESSION (real paper 2507.08271 ph2.tex → tcilatex.tex): a COMMENTED `%
     the \input tcilatex` must NOT be read as a live edge. Include_resolver is
     comment-blind, so without comment-stripping this manufactured a FALSE
     self-cycle on a document pdflatex compiles cleanly. *)
  run "has_include_cycle: commented \\input is not a live edge" (fun tag ->
      let a =
        write_file "cmt_a.tex"
          "\\documentclass{article}\\begin{document}\\input{cmt_b}\\end{document}"
      in
      let _ = write_file "cmt_b.tex" "% the \\input cmt_a\nreal content\n" in
      expect
        (not (Project_model.has_include_cycle a))
        (tag ^ ": commented back-edge ignored"));

  run "has_include_cycle: no includes ok" (fun tag ->
      let a =
        write_file "solo.tex"
          "\\documentclass{article}\\begin{document}x\\end{document}"
      in
      expect (not (Project_model.has_include_cycle a)) (tag ^ ": solo clean"));

  (* ── OPEN-007 T2 channel (2026-09-02): only LIVE includes are edges ──── *)
  run "of_root: commented \\input is DEAD — not a project file" (fun tag ->
      let root =
        write_file "cmt.tex"
          "\\documentclass{article}\n\
           % \\input{ghost-child}\n\
           \\begin{document}\n\
           x\n\
           \\end{document}\n"
      in
      match Project_model.of_root root with
      | Ok proj ->
          expect
            (List.length (Project_model.all_files proj) = 1)
            (tag ^ ": pdflatex compiles without ghost-child; T2 must too")
      | Error _ -> expect false (tag ^ ": should succeed"));
  run "of_root: verbatim-wrapped \\input is DEAD" (fun tag ->
      let root =
        write_file "vrb.tex"
          "\\documentclass{article}\n\
           \\begin{document}\n\
           \\begin{verbatim}\n\
           \\input{ghost-child}\n\
           \\end{verbatim}\n\
           \\end{document}\n"
      in
      match Project_model.of_root root with
      | Ok proj ->
          expect
            (List.length (Project_model.all_files proj) = 1)
            (tag ^ ": verbatim shows text, executes nothing")
      | Error _ -> expect false (tag ^ ": should succeed"));
  run "of_root: LIVE \\input{missing} is still recorded (the control)"
    (fun tag ->
      let root =
        write_file "live.tex"
          "\\documentclass{article}\n\
           \\input{ghost-child}\n\
           \\begin{document}\n\
           x\n\
           \\end{document}\n"
      in
      match Project_model.of_root root with
      | Ok proj ->
          expect
            (List.length (Project_model.all_files proj) = 2)
            (tag ^ ": a live missing include must keep failing T2")
      | Error _ -> expect false (tag ^ ": should succeed"));
  run "of_root: breaker doc keeps the RAW scan (fail-closed)" (fun tag ->
      (* under catcode surgery a %-prefixed \input can EXECUTE, so the gate must
         keep the comment-blind scan: the commented directive is RECORDED again
         — today's behaviour, over-rejection at worst. *)
      let root =
        write_file "brk.tex"
          "\\documentclass{article}\n\
           \\catcode`\\%=12\n\
           % \\input{ghost-child}\n\
           \\begin{document}\n\
           x\n\
           \\end{document}\n"
      in
      match Project_model.of_root root with
      | Ok proj ->
          expect
            (List.length (Project_model.all_files proj) = 2)
            (tag ^ ": breaker present => dead edges count again")
      | Error _ -> expect false (tag ^ ": should succeed"));

  run "of_root: BREAKER IN AN \\input CHILD widens the gate (C-34)" (fun tag ->
      (* brk.tex makes % an ignored char, so the root's '%'-prefixed \input
         EXECUTES (measured pdflatex fatal). The gate must probe children:
         root-only gating blanks the live directive = false-READY. *)
      let _ = write_file "brk.tex" "\\catcode`\\%=9\n" in
      let root =
        write_file "childbrk.tex"
          "\\documentclass{article}\n\
           \\begin{document}\n\
           \\input{brk}\n\
           % \\input{ghost-child}\n\
           x\n\
           \\end{document}\n"
      in
      match Project_model.of_root root with
      | Ok proj ->
          expect
            (List.length (Project_model.all_files proj) = 3)
            (tag ^ ": brk + ghost-child both recorded (raw scan kept)")
      | Error _ -> expect false (tag ^ ": should succeed"));
  run "of_root: BREAKER IN A LOCAL .sty widens the gate (C-34)" (fun tag ->
      let sty = Filename.concat tmp_dir "pctbrk.sty" in
      let oc = open_out sty in
      output_string oc "\\catcode`\\%=9\n";
      close_out oc;
      let root =
        write_file "stybrk.tex"
          "\\documentclass{article}\n\
           \\usepackage{pctbrk}\n\
           \\begin{document}\n\
           % \\input{ghost-child}\n\
           x\n\
           \\end{document}\n"
      in
      let r =
        match Project_model.of_root root with
        | Ok proj -> List.length (Project_model.all_files proj) = 2
        | Error _ -> false
      in
      (try Sys.remove sty with _ -> ());
      expect r (tag ^ ": ghost-child recorded because pctbrk.sty is a breaker"));

  run "of_root: DIR-SHADOW resolves to the .tex, not the directory" (fun tag ->
      let d = Filename.concat tmp_dir "shadow" in
      (try Unix.mkdir d 0o755 with _ -> ());
      let _ = write_file "shadow.tex" "file content\n" in
      let root =
        write_file "dsroot.tex"
          "\\documentclass{article}\n\
           \\begin{document}\n\
           \\input{shadow}\n\
           x\n\
           \\end{document}\n"
      in
      let r =
        match Project_model.of_root root with
        | Ok proj ->
            List.exists
              (fun (f : Project_model.file_entry) ->
                Filename.check_suffix f.path "shadow.tex")
              (Project_model.all_files proj)
        | Error _ -> false
      in
      (try Unix.rmdir d with _ -> ());
      expect r (tag ^ ": kpathsea reads the FILE; T2 must too"));

  cleanup_dir ();
  finalise "project-model"
