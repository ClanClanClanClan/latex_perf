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

  cleanup_dir ();
  finalise "project-model"
