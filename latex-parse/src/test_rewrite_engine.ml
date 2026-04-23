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
      let es =
        [
          Cst_edit.replace ~start_offset:0 ~end_offset:5 "Hi";
          Cst_edit.replace ~start_offset:3 ~end_offset:6 "Xx";
        ]
      in
      match Rewrite_engine.apply ~source:src ~edits:es with
      | Error (`Overlap _) -> expect true (tag ^ ": overlap rejected")
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

  (* ── Fuzz: random edit lists on random sources ───────────────────── *)
  run "fuzz: byte-lossless under random non-overlapping edits" (fun tag ->
      Random.self_init ();
      let base_sources =
        [|
          "Hello world.\n\\section{Intro}\nLorem ipsum.";
          "\\begin{document}\n\
           paragraph 1\n\n\
           \\textbf{bold} text.\n\
           \\end{document}";
          "Math: $a+b$ and $c-d$ with \\[ x = y \\].";
          "One two three four five six seven eight nine ten.";
          "\\begin{itemize}\n\\item A\n\\item B\n\\item C\n\\end{itemize}";
        |]
      in
      let iterations = 50 in
      let failures = ref 0 in
      for _ = 1 to iterations do
        let src = base_sources.(Random.int (Array.length base_sources)) in
        let n = String.length src in
        let k = 1 + Random.int 3 in
        (* Produce k non-overlapping edits at random disjoint ranges. *)
        let chunk = max 1 (n / (k + 1)) in
        let edits = ref [] in
        for i = 0 to k - 1 do
          let lo = i * chunk in
          let hi = min (lo + Random.int chunk + 1) n in
          if hi > lo then
            let repl =
              if Random.int 3 = 0 then ""
              else String.make (1 + Random.int 4) '*'
            in
            edits :=
              Cst_edit.replace ~start_offset:lo ~end_offset:hi repl :: !edits
        done;
        match Rewrite_engine.apply_and_reparse ~source:src ~edits:!edits with
        | Error _ -> incr failures
        | Ok (rewritten, cst) ->
            if Cst.serialize cst <> rewritten then incr failures
      done;
      expect (!failures = 0)
        (Printf.sprintf "%s: %d/%d failures" tag !failures iterations));

  finalise "rewrite-engine"
