(** Integration tests for validators_cli — runs the CLI as a subprocess. *)

open Latex_parse_lib
open Test_helpers

(* Write a temp .tex file and return its path *)
let write_temp_tex content =
  let path = Filename.temp_file "test_cli_" ".tex" in
  let oc = open_out path in
  output_string oc content;
  close_out oc;
  path

(* Run validators_cli and capture stdout + exit code *)
let run_cli args =
  let exe =
    Filename.concat (Filename.dirname Sys.argv.(0)) "validators_cli.exe"
  in
  let cmd = String.concat " " (List.map Filename.quote (exe :: args)) in
  let ic = Unix.open_process_in cmd in
  let buf = Buffer.create 256 in
  (try
     while true do
       Buffer.add_string buf (input_line ic);
       Buffer.add_char buf '\n'
     done
   with End_of_file -> ());
  let status = Unix.close_process_in ic in
  let code =
    match status with
    | Unix.WEXITED c -> c
    | Unix.WSIGNALED _ -> -1
    | Unix.WSTOPPED _ -> -1
  in
  (Buffer.contents buf, code)

let () =
  (* Basic invocation: file with known issues *)
  run "CLI basic invocation produces TSV output" (fun tag ->
      let path = write_temp_tex "Hello \\textbf{world}\n" in
      let out, code = run_cli [ path ] in
      Sys.remove path;
      expect (code = 0) (tag ^ ": exit code 0");
      (* Output should be tab-separated lines *)
      let lines =
        String.split_on_char '\n' out
        |> List.filter (fun l -> String.length l > 0)
      in
      List.iter
        (fun line ->
          let tabs = String.split_on_char '\t' line in
          expect
            (List.length tabs >= 4)
            (tag ^ ": line has >= 4 tab fields: " ^ line))
        lines);

  (* Layer flag: --layer l0 only shows L0 rule IDs *)
  run "CLI --layer l0 filters to L0 rules" (fun tag ->
      let path = write_temp_tex "$x + y$ and some text\n" in
      let out, code = run_cli [ "--layer"; "l0"; path ] in
      Sys.remove path;
      expect (code = 0) (tag ^ ": exit code 0");
      let lines =
        String.split_on_char '\n' out
        |> List.filter (fun l -> String.length l > 0 && l.[0] <> '#')
      in
      List.iter
        (fun line ->
          let id =
            match String.split_on_char '\t' line with x :: _ -> x | [] -> ""
          in
          let layer = Validators.precondition_of_rule_id id in
          expect (layer = Validators.L0) (tag ^ ": " ^ id ^ " should be L0"))
        lines);

  (* Layer flag: --layer l1 shows timing header *)
  run "CLI --layer l1 shows timing header" (fun tag ->
      let path = write_temp_tex "$\\frac{1}{2}$\n" in
      let out, code = run_cli [ "--layer"; "l1"; path ] in
      Sys.remove path;
      expect (code = 0) (tag ^ ": exit code 0");
      let first_line =
        match String.split_on_char '\n' out with l :: _ -> l | [] -> ""
      in
      expect
        (String.length first_line > 0 && first_line.[0] = '#')
        (tag ^ ": first line is timing comment"));

  (* Missing file: exit non-zero *)
  run "CLI missing file exits non-zero" (fun tag ->
      let _, code = run_cli [ "/tmp/nonexistent_file_cli_test.tex" ] in
      expect (code <> 0) (tag ^ ": non-zero exit for missing file"));

  (* No args: exits with code 2 *)
  run "CLI no args exits 2" (fun tag ->
      let _, code = run_cli [] in
      expect (code = 2) (tag ^ ": exit code 2 for no args"));

  (* Output format: each result line matches ID\tSEVERITY\tCOUNT\tMESSAGE *)
  run "CLI output format is tab-separated" (fun tag ->
      let path =
        write_temp_tex "\\begin{verbatim}\n\thello\n\\end{verbatim}\n"
      in
      let out, code = run_cli [ path ] in
      Sys.remove path;
      expect (code = 0) (tag ^ ": exit code 0");
      let result_lines =
        String.split_on_char '\n' out
        |> List.filter (fun l -> String.length l > 0 && l.[0] <> '#')
      in
      (* Should have at least one result (VERB-002 for tab) *)
      expect (List.length result_lines > 0) (tag ^ ": at least one result line");
      List.iter
        (fun line ->
          let parts = String.split_on_char '\t' line in
          expect (List.length parts = 4) (tag ^ ": exactly 4 tab fields"))
        result_lines);

  (* Severity values are one of: error, warning, info *)
  run "CLI severity values are valid" (fun tag ->
      let path =
        write_temp_tex "$x + y$ and \\begin{verbatim}\n\tx\n\\end{verbatim}\n"
      in
      let out, _ = run_cli [ path ] in
      Sys.remove path;
      let result_lines =
        String.split_on_char '\n' out
        |> List.filter (fun l -> String.length l > 0 && l.[0] <> '#')
      in
      List.iter
        (fun line ->
          let parts = String.split_on_char '\t' line in
          match parts with
          | _ :: sev :: _ ->
              expect
                (sev = "error" || sev = "warning" || sev = "info")
                (tag ^ ": valid severity: " ^ sev)
          | _ -> ())
        result_lines);

  (* Empty file still produces some L0 results (e.g., require_documentclass) *)
  run "CLI empty file runs without error" (fun tag ->
      let path = write_temp_tex "" in
      let _out, code = run_cli [ path ] in
      Sys.remove path;
      expect (code = 0) (tag ^ ": exit code 0 on empty file"));

  (* PR #241 (p1.3): end-to-end --advisory gate. Without --advisory, STYLE-*
     Class D rules must not appear in CLI output. With --advisory, at least
     one STYLE-* rule should fire on a source that triggers them. *)
  let styleful_src =
    "\\documentclass{article}\n\
     \\begin{document}\n\
     This is a very long sentence that keeps going and going and going and \
     going and going and going and going and going and going until it \
     becomes utterly unreasonable and rambling.\n\n\
     One.\n\n\
     Two.\n\n\
     Three.\n\
     \\end{document}\n"
  in
  let has_style_id out =
    String.split_on_char '\n' out
    |> List.exists (fun line ->
           String.length line >= 6 && String.sub line 0 6 = "STYLE-")
  in
  run "CLI default run excludes STYLE rules" (fun tag ->
      let path = write_temp_tex styleful_src in
      let out, code = run_cli [ path ] in
      Sys.remove path;
      expect (code = 0) (tag ^ ": exit code 0");
      expect (not (has_style_id out))
        (tag ^ ": no STYLE-* line in default output"));
  run "CLI --advisory enables STYLE rules" (fun tag ->
      let path = write_temp_tex styleful_src in
      let out, code = run_cli [ "--advisory"; path ] in
      Sys.remove path;
      expect (code = 0) (tag ^ ": exit code 0");
      expect (has_style_id out)
        (tag ^ ": at least one STYLE-* line under --advisory"))

let () = finalise "cli"
