(** Fuzz test for [Rewrite_engine] (plan §3.2 PR B3 deliverable).

    Generates random non-overlapping edit lists against a rotation of base LaTeX
    sources and asserts byte-lossless round-trip on every result. If the rewrite
    engine or CST builder regresses on any randomly-chosen edit pattern, this
    test fails. *)

open Latex_parse_lib
open Test_helpers

let () =
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

  finalise "rewrite-fuzz"
