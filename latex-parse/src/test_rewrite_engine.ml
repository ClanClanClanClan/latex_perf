(** Tests for [Rewrite_engine]. *)

open Latex_parse_lib
open Test_helpers

let () =
  run "apply rewrites source" (fun tag ->
      let src = "\\documentclass{article}" in
      let e = Cst_edit.replace ~start_offset:15 ~end_offset:22 "report" in
      match Rewrite_engine.apply ~source:src ~edits:[ e ] with
      | Ok out -> expect (out = "\\documentclass{report}") (tag ^ ": report")
      | Error _ -> expect false (tag ^ ": should succeed"));

  run "apply empty edit list is identity" (fun tag ->
      let src = "Hello world" in
      match Rewrite_engine.apply ~source:src ~edits:[] with
      | Ok out -> expect (out = src) (tag ^ ": identity")
      | Error _ -> expect false (tag ^ ": should succeed"));

  run "apply rejects conflicting edits" (fun tag ->
      let src = "Hello world" in
      let a = Cst_edit.replace ~start_offset:0 ~end_offset:5 "Hi" in
      let b = Cst_edit.replace ~start_offset:3 ~end_offset:6 "Xx" in
      match Rewrite_engine.apply ~source:src ~edits:[ a; b ] with
      | Error (`Overlap (x, y)) ->
          expect
            (Cst_edit.equal x a && Cst_edit.equal y b)
            (tag ^ ": reports the conflicting pair")
      | Ok _ -> expect false (tag ^ ": should reject"));

  run "apply_and_reparse produces CST" (fun tag ->
      let src = "hello world" in
      let e = Cst_edit.replace ~start_offset:6 ~end_offset:11 "LaTeX" in
      match Rewrite_engine.apply_and_reparse ~source:src ~edits:[ e ] with
      | Ok (rewritten, cst) ->
          expect (rewritten = "hello LaTeX") (tag ^ ": rewritten");
          expect
            (Cst.serialize cst = "hello LaTeX")
            (tag ^ ": CST serializes same")
      | Error _ -> expect false (tag ^ ": should succeed"));

  run "byte-lossless preserved under rewrites" (fun tag ->
      (* For any source and any set of non-overlapping edits, the resulting CST
         must still be byte-lossless w.r.t. the rewritten source. *)
      let cases =
        [
          ("\\section{Hi}", Cst_edit.replace ~start_offset:9 ~end_offset:11 "Yo");
          ( "\\begin{itemize}\\item foo\\end{itemize}",
            Cst_edit.replace ~start_offset:20 ~end_offset:24 "bar" );
          ( "text $x+y$ more text",
            Cst_edit.replace ~start_offset:6 ~end_offset:9 "a*b" );
        ]
      in
      List.iter
        (fun (src, e) ->
          match Rewrite_engine.apply_and_reparse ~source:src ~edits:[ e ] with
          | Ok (rewritten, cst) ->
              expect
                (Cst.serialize cst = rewritten)
                (tag ^ ": roundtrip on '" ^ src ^ "'")
          | Error _ -> expect false (tag ^ ": apply failed"))
        cases);

  (* Fuzz testing lives in test_rewrite_fuzz.ml (plan §3.2 B3 parity). *)
  finalise "rewrite-engine"
