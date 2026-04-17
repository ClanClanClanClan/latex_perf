(** Tests for WS2 user macro validators CMD-015, CMD-016, CMD-017. *)

open Latex_parse_lib
open Test_helpers

let with_macro_context src f =
  let reg = User_macro_registry.create src in
  User_macro_context.set reg;
  Fun.protect ~finally:User_macro_context.clear f

let find_result id results =
  List.find_opt (fun (r : Validators.result) -> r.id = id) results

let () =
  (* ── CMD-015: unsupported user macro construct ─────────────────── *)
  run "CMD-015 fires on unsupported \\def in body" (fun tag ->
      let src =
        "\\newcommand{\\bad}{\\def\\inner{x}}\n\\begin{document}\\end{document}"
      in
      with_macro_context src (fun () ->
          let results = Validators.run_all src in
          expect (find_result "CMD-015" results <> None) (tag ^ ": fires")));

  run "CMD-015 fires on \\expandafter" (fun tag ->
      let src =
        "\\newcommand{\\bad}{\\expandafter\\foo}\n\
         \\begin{document}\\end{document}"
      in
      with_macro_context src (fun () ->
          let results = Validators.run_all src in
          expect (find_result "CMD-015" results <> None) (tag ^ ": fires")));

  run "CMD-015 does not fire on supported macro" (fun tag ->
      let src =
        "\\newcommand{\\good}{hello world}\n\\begin{document}\\end{document}"
      in
      with_macro_context src (fun () ->
          let results = Validators.run_all src in
          expect (find_result "CMD-015" results = None) (tag ^ ": silent")));

  run "CMD-015 does not fire without context" (fun tag ->
      User_macro_context.clear ();
      let src = "\\newcommand{\\bad}{\\def\\x{y}}" in
      let results = Validators.run_all src in
      expect
        (find_result "CMD-015" results = None)
        (tag ^ ": silent without context"));

  (* ── CMD-016: cycle in user macro definitions ──────────────────── *)
  run "CMD-016 fires on cycle" (fun tag ->
      let src =
        "\\newcommand{\\aaa}{\\bbb}\n\
         \\newcommand{\\bbb}{\\aaa}\n\
         \\begin{document}\\end{document}"
      in
      with_macro_context src (fun () ->
          let results = Validators.run_all src in
          expect (find_result "CMD-016" results <> None) (tag ^ ": fires")));

  run "CMD-016 does not fire on acyclic" (fun tag ->
      let src =
        "\\newcommand{\\aaa}{\\bbb}\n\
         \\newcommand{\\bbb}{hello}\n\
         \\begin{document}\\end{document}"
      in
      with_macro_context src (fun () ->
          let results = Validators.run_all src in
          expect (find_result "CMD-016" results = None) (tag ^ ": silent")));

  (* ── CMD-017: user macro shadows built-in ──────────────────────── *)
  run "CMD-017 fires on \\newcommand shadowing built-in" (fun tag ->
      let src =
        "\\newcommand{\\textbf}[1]{BOLD #1}\n\\begin{document}\\end{document}"
      in
      with_macro_context src (fun () ->
          let results = Validators.run_all src in
          expect (find_result "CMD-017" results <> None) (tag ^ ": fires")));

  run "CMD-017 does not fire on \\renewcommand" (fun tag ->
      let src =
        "\\renewcommand{\\textbf}[1]{BOLD #1}\n\\begin{document}\\end{document}"
      in
      with_macro_context src (fun () ->
          let results = Validators.run_all src in
          expect
            (find_result "CMD-017" results = None)
            (tag ^ ": silent for renewcommand")));

  run "CMD-017 does not fire on non-built-in name" (fun tag ->
      let src =
        "\\newcommand{\\myfunc}{stuff}\n\\begin{document}\\end{document}"
      in
      with_macro_context src (fun () ->
          let results = Validators.run_all src in
          expect
            (find_result "CMD-017" results = None)
            (tag ^ ": silent for custom name")));

  (* ── Regression: existing CMD rules unaffected ─────────────────── *)
  run "CMD-002 still fires on \\def" (fun tag ->
      let src = "\\def\\foo{bar}" in
      let results = Validators.run_all src in
      expect (find_result "CMD-002" results <> None) (tag ^ ": CMD-002 fires"))

let () = finalise "user-macro-validators"
