(** Integration tests for the `--apply-fixes` CLI mode (v26.2.1 PR #4).

    Runs `validators_cli` as a subprocess with either the `--apply-fixes` flag
    or `L0_APPLY_FIXES=1` and asserts that the collected fix edits are applied
    via `Cst_edit.apply_all` before stdout is written. Separate file from
    `test_validators_cli.ml` because the output format is distinct (raw source,
    not TSV). *)

open Test_helpers

let write_temp_tex content =
  let path = Filename.temp_file "test_apply_fixes_cli_" ".tex" in
  let oc = open_out path in
  output_string oc content;
  close_out oc;
  path

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
    | Unix.WSIGNALED _ | Unix.WSTOPPED _ -> -1
  in
  (Buffer.contents buf, code)

let strip_comments (out : string) : string =
  String.split_on_char '\n' out
  |> List.filter (fun l -> String.length l = 0 || l.[0] <> '#')
  |> String.concat "\n"

let () =
  (* --apply-fixes applies STRUCT-001's fix: insert \documentclass at 0. *)
  run "CLI --apply-fixes inserts \\documentclass for STRUCT-001" (fun tag ->
      let path = write_temp_tex "Body without docclass.\n" in
      let out, code = run_cli [ "--apply-fixes"; path ] in
      Sys.remove path;
      expect (code = 0) (tag ^ ": exit code 0");
      let body = strip_comments out in
      expect
        (String.length body >= 14 && String.sub body 0 14 = "\\documentclass")
        (tag ^ ": output begins with \\documentclass"));

  (* L0_APPLY_FIXES=1 env gate is equivalent to --apply-fixes. *)
  run "CLI L0_APPLY_FIXES=1 env gate equivalent to --apply-fixes" (fun tag ->
      let path = write_temp_tex "No docclass here.\n" in
      Unix.putenv "L0_APPLY_FIXES" "1";
      let out, code = run_cli [ path ] in
      Unix.putenv "L0_APPLY_FIXES" "";
      Sys.remove path;
      expect (code = 0) (tag ^ ": exit code 0");
      let body = strip_comments out in
      expect
        (String.length body >= 14 && String.sub body 0 14 = "\\documentclass")
        (tag ^ ": env-gated apply-fixes also inserts \\documentclass"));

  (* Clean source → no rule emits a fix → stdout echoes input. *)
  run "CLI --apply-fixes on clean source echoes input" (fun tag ->
      let path =
        write_temp_tex
          "\\documentclass{article}\n\\begin{document}\nOK\n\\end{document}\n"
      in
      let out, code = run_cli [ "--apply-fixes"; path ] in
      Sys.remove path;
      expect (code = 0) (tag ^ ": exit code 0");
      let body = strip_comments out in
      expect
        (String.length body > 0 && String.sub body 0 14 = "\\documentclass")
        (tag ^ ": output is the original source unchanged"));

  finalise "apply-fixes-cli"
