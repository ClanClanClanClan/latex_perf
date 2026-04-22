(** Tests for [Cst_of_ast]. Byte-losslessness is the v26.2 guarantee. *)

open Latex_parse_lib
open Test_helpers

let roundtrip_ok src =
  let nodes = Cst_of_ast.of_source src in
  Cst.serialize nodes = src

let () =
  run "empty source" (fun tag -> expect (roundtrip_ok "") (tag ^ ": empty"));

  run "plain text" (fun tag ->
      expect (roundtrip_ok "hello world") (tag ^ ": plain text"));

  run "single command" (fun tag ->
      expect (roundtrip_ok "\\section{Intro}") (tag ^ ": section"));

  run "command with options" (fun tag ->
      expect
        (roundtrip_ok "\\includegraphics[width=5cm]{fig}")
        (tag ^ ": graphics"));

  run "inline math" (fun tag ->
      expect (roundtrip_ok "Let $x = 1$.") (tag ^ ": inline math"));

  run "display math brackets" (fun tag ->
      expect (roundtrip_ok "Hello \\[ a+b \\] world") (tag ^ ": display math"));

  run "comment preserved" (fun tag ->
      expect (roundtrip_ok "line\n% a comment\nmore") (tag ^ ": comment line"));

  run "nested braces" (fun tag ->
      expect (roundtrip_ok "\\textbf{{bold} text}") (tag ^ ": nested"));

  run "environment" (fun tag ->
      expect
        (roundtrip_ok "\\begin{itemize}\\item foo\\end{itemize}")
        (tag ^ ": itemize"));

  run "verbatim opaque" (fun tag ->
      expect
        (roundtrip_ok "\\begin{verbatim}\\ $ #{}% anything\\end{verbatim}")
        (tag ^ ": verbatim"));

  run "multiline source" (fun tag ->
      let src =
        "\\documentclass{article}\n\
         \\begin{document}\n\
         Hello \\LaTeX.\n\
         \\end{document}\n"
      in
      expect (roundtrip_ok src) (tag ^ ": doc"));

  run "whitespace trivia classified" (fun tag ->
      let src = "a   b" in
      let nodes = Cst_of_ast.of_source src in
      let has_ws =
        List.exists
          (function
            | Cst.CTrivia { kind = Cst.Whitespace; _ } -> true | _ -> false)
          nodes
      in
      expect has_ws (tag ^ ": whitespace CTrivia present"));

  run "command wrapped in CUnparsed (v26.2)" (fun tag ->
      let src = "\\foo{bar}" in
      let nodes = Cst_of_ast.of_source src in
      let has_unparsed =
        List.exists (function Cst.CUnparsed _ -> true | _ -> false) nodes
      in
      expect has_unparsed (tag ^ ": CUnparsed present"));

  run "environment emitted as CEnvironment" (fun tag ->
      let src = "\\begin{em}x\\end{em}" in
      let nodes = Cst_of_ast.of_source src in
      let has_env =
        List.exists (function Cst.CEnvironment _ -> true | _ -> false) nodes
      in
      expect has_env (tag ^ ": CEnvironment present"));

  run "unicode characters preserved" (fun tag ->
      expect (roundtrip_ok "résumé — café") (tag ^ ": unicode"));

  run "from located AST" (fun tag ->
      let src = "abc def" in
      let nodes, _ = Parser_l2.parse_located src in
      let cst = Cst_of_ast.of_located src nodes in
      expect (Cst.serialize cst = src) (tag ^ ": of_located roundtrip"));

  finalise "cst-of-ast"
