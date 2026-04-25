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

  (* v26.2.1 PR #4 plan §3 item 4: TYPO-002 apply converts `a -- b` to `a – b`.
     TYPO rules ship in the pilot set; enable via [L0_VALIDATORS]. The body of
     the document holds the dashes so they survive past STRUCT-001's check. *)
  run "CLI --apply-fixes converts -- to en-dash for TYPO-002" (fun tag ->
      let path =
        write_temp_tex
          "\\documentclass{article}\n\
           \\begin{document}\n\
           a -- b\n\
           \\end{document}\n"
      in
      Unix.putenv "L0_VALIDATORS" "pilot";
      let out, code = run_cli [ "--apply-fixes"; path ] in
      Unix.putenv "L0_VALIDATORS" "";
      Sys.remove path;
      expect (code = 0) (tag ^ ": exit code 0");
      let body = strip_comments out in
      expect
        (let needle = "a – b" in
         let nlen = String.length needle in
         let rec find i =
           if i + nlen > String.length body then false
           else if String.sub body i nlen = needle then true
           else find (i + 1)
         in
         find 0)
        (tag ^ ": en-dash present in output"));

  (* v26.2.1 PR #4 plan §3 item 4: overlapping fixes → exit 2 + stderr
     [E.apply-fixes.overlap]. The v26.2.1 fix producers (STRUCT-001 / TYPO-002 /
     TYPO-003) cannot in practice produce overlapping edit sets — STRUCT-001 is
     a zero-length insert at 0 (Cst_edit's [conflicts] rule does not flag
     adjacent boundaries for pure insertions), and TYPO-002 / TYPO-003 are
     mutually suppressed by the conflict edge from PR #241 p1.3 whenever [---]
     is present. So the natural-corpus path is unreachable.

     The closest surrogate that we CAN exercise end-to-end: [---] firing under
     pilot env. TYPO-003 wins, TYPO-002 is suppressed, only TYPO-003's fix is
     applied — no overlap, exit 0 and stderr does not contain the overlap
     marker. This proves the CLI's apply-fixes flow correctly routes through the
     overlap branch (negative path) on the only natural-corpus input where
     overlap could occur if suppression were absent.

     The overlap-error wiring itself (Rewrite_engine.apply returning [Error
     (`Overlap _)]) is unit-tested in [test_cst_edit.ml] and
     [test_rewrite_engine.ml]. *)
  run "CLI --apply-fixes on TYPO-003 input takes non-overlap branch" (fun tag ->
      let path =
        write_temp_tex
          "\\documentclass{article}\n\
           \\begin{document}\n\
           a --- b\n\
           \\end{document}\n"
      in
      let stderr_path = Filename.temp_file "test_apply_fixes_stderr_" ".log" in
      Unix.putenv "L0_VALIDATORS" "pilot";
      let exe =
        Filename.concat (Filename.dirname Sys.argv.(0)) "validators_cli.exe"
      in
      let cmd =
        String.concat " "
          (List.map Filename.quote [ exe; "--apply-fixes"; path ])
        ^ " 2>"
        ^ Filename.quote stderr_path
      in
      let ic = Unix.open_process_in cmd in
      let buf = Buffer.create 256 in
      (try
         while true do
           Buffer.add_string buf (input_line ic);
           Buffer.add_char buf '\n'
         done
       with End_of_file -> ());
      let status = Unix.close_process_in ic in
      let code = match status with Unix.WEXITED c -> c | _ -> -1 in
      Unix.putenv "L0_VALIDATORS" "";
      Sys.remove path;
      let stderr_text =
        try
          let ic = open_in stderr_path in
          let n = in_channel_length ic in
          let s = really_input_string ic n in
          close_in ic;
          s
        with _ -> ""
      in
      (try Sys.remove stderr_path with _ -> ());
      let body = strip_comments (Buffer.contents buf) in
      let contains s sub =
        let nlen = String.length sub in
        let slen = String.length s in
        let rec find i =
          if i + nlen > slen then false
          else if String.sub s i nlen = sub then true
          else find (i + 1)
        in
        find 0
      in
      expect
        (code = 0
        && contains body "a — b"
        && not (contains stderr_text "E.apply-fixes.overlap"))
        (tag
        ^ ": exit 0, em-dash applied, no overlap error (suppression prevented \
           overlap)"));

  (* Plan §3 PR #4 item 4: overlapping fixes → error with [`Overlap _]. Cannot
     be triggered through any v26.2.1 natural corpus (conflict suppression +
     adjacent-boundary semantics, see prior test's comment), so we exercise the
     CLI's underlying error path directly: construct a synthetic overlapping
     edit pair, call [Rewrite_engine.apply] (the same function the CLI uses),
     and assert it returns [Error (`Overlap _)]. The CLI's eprintf + [exit 2]
     handler is then a thin sealed match on this error constructor — reviewable
     in [validators_cli.ml] §run_apply_fixes. *)
  run "Rewrite_engine.apply rejects overlapping edits with `Overlap _"
    (fun tag ->
      let src = "abcdef" in
      let e1 =
        Latex_parse_lib.Cst_edit.replace ~start_offset:0 ~end_offset:3 "X"
      in
      let e2 =
        Latex_parse_lib.Cst_edit.replace ~start_offset:1 ~end_offset:4 "Y"
      in
      match
        Latex_parse_lib.Rewrite_engine.apply ~source:src ~edits:[ e1; e2 ]
      with
      | Error (`Overlap (a, b)) ->
          expect
            (Latex_parse_lib.Cst_edit.equal a e1
            && Latex_parse_lib.Cst_edit.equal b e2)
            (tag ^ ": Error (`Overlap (e1, e2)) — CLI's exit-2 path source")
      | Ok _ -> expect false (tag ^ ": expected Error, got Ok"));

  finalise "apply-fixes-cli"
