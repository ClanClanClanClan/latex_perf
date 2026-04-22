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

  cleanup_dir ();
  finalise "project-model"
