(** Unit tests for STRUCT family rules (PR #241 p1.4 / p1.7).

    STRUCT-001..005 were renamed from lowercase internal-utility IDs to the
    FAMILY-NNN convention so every runtime rule has a contract. This test
    provides mutation-test coverage and pins the expected behaviour. *)

open Test_helpers

let () =
  (* STRUCT-001: Missing \documentclass. Fires when pilot mode is OFF. *)
  Unix.putenv "L0_VALIDATORS" "";
  run "STRUCT-001 fires on missing documentclass" (fun tag ->
      expect
        (fires "STRUCT-001" "Hello world\nNo documentclass here.")
        (tag ^ ": no-docclass source"));
  run "STRUCT-001 does not fire with documentclass present" (fun tag ->
      expect
        (does_not_fire "STRUCT-001"
           "\\documentclass{article}\n\\begin{document}\n\\end{document}")
        (tag ^ ": docclass present"));
  run "STRUCT-001 emits a single insert-at-0 fix edit" (fun tag ->
      let src = "Hello world\nNo documentclass here." in
      let edits = fix_edits "STRUCT-001" src in
      let applied =
        match edits with
        | [ edit ] -> Latex_parse_lib.Cst_edit.apply_single src edit
        | _ -> ""
      in
      expect
        (List.length edits = 1
        && String.length applied - String.length src
           = String.length "\\documentclass{article}\n"
        && String.sub applied 0 14 = "\\documentclass")
        (tag ^ ": inserts \\documentclass at top"));

  (* STRUCT-002: Empty section title *)
  run "STRUCT-002 fires on empty section title" (fun tag ->
      expect
        (fires "STRUCT-002"
           "\\documentclass{article}\n\
            \\begin{document}\n\
            \\section{}\n\
            \\end{document}")
        (tag ^ ": \\section{} fires"));
  run "STRUCT-002 does not fire with non-empty title" (fun tag ->
      expect
        (does_not_fire "STRUCT-002"
           "\\documentclass{article}\n\
            \\begin{document}\n\
            \\section{Title}\n\
            \\end{document}")
        (tag ^ ": titled section clean"));

  (* STRUCT-003: Tab characters *)
  run "STRUCT-003 fires on tab" (fun tag ->
      expect (fires "STRUCT-003" "hello\tworld") (tag ^ ": tab character"));
  run "STRUCT-003 clean on spaces only" (fun tag ->
      expect (does_not_fire "STRUCT-003" "hello world") (tag ^ ": no tabs"));

  (* STRUCT-004: Unmatched braces *)
  run "STRUCT-004 fires on unbalanced opener" (fun tag ->
      expect
        (fires "STRUCT-004" "\\documentclass{article}\n{oops")
        (tag ^ ": extra opening brace"));
  run "STRUCT-004 fires on unbalanced closer" (fun tag ->
      expect
        (fires "STRUCT-004" "\\documentclass{article}\noops}")
        (tag ^ ": extra closing brace"));
  run "STRUCT-004 clean when balanced" (fun tag ->
      expect
        (does_not_fire "STRUCT-004"
           "\\documentclass{article}\n\\begin{document}\n\\end{document}")
        (tag ^ ": balanced braces"));

  (* STRUCT-005: Document-structure summary — fires when parse issues exist. *)
  run "STRUCT-005 fires on parse errors" (fun tag ->
      expect
        (fires "STRUCT-005"
           "\\documentclass{article}\n\
            \\begin{document}\n\
            \\ref{undefined-label}\n\
            \\end{document}")
        (tag ^ ": undefined ref yields struct summary"));

  finalise "validators-struct"
