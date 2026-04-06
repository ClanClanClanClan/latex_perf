(** Tests for L2 parser: amsmath environments, TikZ, metadata extraction. *)

let fails = ref 0

let check name cond =
  if not cond then (
    Printf.eprintf "FAIL: %s\n%!" name;
    incr fails)
  else Printf.printf "  ok  %s\n%!" name

let () =
  Printf.printf "[test_parser_l2_envs]\n%!";

  (* ── Math environment tests ─────────────────────────────────── *)

  (* Test: cases environment → MathDisplay *)
  let nodes1 =
    Latex_parse_lib.Parser_l2.parse {|\begin{cases} a \\ b \end{cases}|}
  in
  check "cases → MathDisplay"
    (List.exists
       (function Latex_parse_lib.Parser_l2.MathDisplay _ -> true | _ -> false)
       nodes1);

  (* Test: matrix environment → MathDisplay *)
  let nodes2 =
    Latex_parse_lib.Parser_l2.parse
      {|\begin{pmatrix} 1 & 2 \\ 3 & 4 \end{pmatrix}|}
  in
  check "pmatrix → MathDisplay"
    (List.exists
       (function Latex_parse_lib.Parser_l2.MathDisplay _ -> true | _ -> false)
       nodes2);

  (* Test: bmatrix → MathDisplay *)
  let nodes3 =
    Latex_parse_lib.Parser_l2.parse {|\begin{bmatrix} x \end{bmatrix}|}
  in
  check "bmatrix → MathDisplay"
    (List.exists
       (function Latex_parse_lib.Parser_l2.MathDisplay _ -> true | _ -> false)
       nodes3);

  (* Test: aligned → MathDisplay *)
  let nodes4 =
    Latex_parse_lib.Parser_l2.parse {|\begin{aligned} a &= b \end{aligned}|}
  in
  check "aligned → MathDisplay"
    (List.exists
       (function Latex_parse_lib.Parser_l2.MathDisplay _ -> true | _ -> false)
       nodes4);

  (* Test: split → MathDisplay *)
  let nodes5 =
    Latex_parse_lib.Parser_l2.parse {|\begin{split} x \end{split}|}
  in
  check "split → MathDisplay"
    (List.exists
       (function Latex_parse_lib.Parser_l2.MathDisplay _ -> true | _ -> false)
       nodes5);

  (* Test: gathered → MathDisplay *)
  let nodes6 =
    Latex_parse_lib.Parser_l2.parse {|\begin{gathered} x \end{gathered}|}
  in
  check "gathered → MathDisplay"
    (List.exists
       (function Latex_parse_lib.Parser_l2.MathDisplay _ -> true | _ -> false)
       nodes6);

  (* Test: smallmatrix → MathDisplay *)
  let nodes7 =
    Latex_parse_lib.Parser_l2.parse {|\begin{smallmatrix} 1 \end{smallmatrix}|}
  in
  check "smallmatrix → MathDisplay"
    (List.exists
       (function Latex_parse_lib.Parser_l2.MathDisplay _ -> true | _ -> false)
       nodes7);

  (* Test: Vmatrix → MathDisplay *)
  let nodes8 =
    Latex_parse_lib.Parser_l2.parse {|\begin{Vmatrix} x \end{Vmatrix}|}
  in
  check "Vmatrix → MathDisplay"
    (List.exists
       (function Latex_parse_lib.Parser_l2.MathDisplay _ -> true | _ -> false)
       nodes8);

  (* Negative test: itemize → Environment (not MathDisplay) *)
  let nodes_neg =
    Latex_parse_lib.Parser_l2.parse {|\begin{itemize}\item x\end{itemize}|}
  in
  check "itemize → Environment"
    (List.exists
       (function
         | Latex_parse_lib.Parser_l2.Environment { env_name = "itemize"; _ } ->
             true
         | _ -> false)
       nodes_neg);

  (* ── TikZ environment test ─────────────────────────────────── *)
  let nodes_tikz =
    Latex_parse_lib.Parser_l2.parse
      {|\begin{tikzpicture}\draw (0,0) -- (1,1);\end{tikzpicture}|}
  in
  check "tikzpicture → Verbatim"
    (List.exists
       (function
         | Latex_parse_lib.Parser_l2.Verbatim { env_name = "tikzpicture"; _ } ->
             true
         | _ -> false)
       nodes_tikz);

  (* ── Metadata extraction tests ──────────────────────────────── *)
  let doc1 =
    Latex_parse_lib.Parser_l2.extract_document
      {|\documentclass[12pt]{article}
\usepackage{amsmath}
\usepackage[utf8]{inputenc}
\usepackage{graphicx,color}
\begin{document}
Hello \ref{fig:a} and \pageref{fig:b} and \nameref{sec:c}.
\href{http://example.com}{link}
\begin{algorithm}
\caption{My algo}
\label{alg:1}
\end{algorithm}
\end{document}|}
  in
  check "documentclass extracted"
    (doc1.documentclass = Some ("article", Some "12pt"));
  check "3 packages extracted" (List.length doc1.packages = 4);
  (* amsmath, inputenc, graphicx, color *)
  check "amsmath in packages"
    (List.exists (fun (p, _, _) -> p = "amsmath") doc1.packages);
  check "graphicx in packages"
    (List.exists (fun (p, _, _) -> p = "graphicx") doc1.packages);
  check "color in packages"
    (List.exists (fun (p, _, _) -> p = "color") doc1.packages);
  check "inputenc has options"
    (List.exists
       (fun (p, o, _) -> p = "inputenc" && o = Some "utf8")
       doc1.packages);
  check "pageref tracked" (List.exists (fun (r, _) -> r = "fig:b") doc1.refs);
  check "nameref tracked" (List.exists (fun (r, _) -> r = "sec:c") doc1.refs);
  check "href tracked"
    (List.exists (fun (r, _) -> r = "http://example.com") doc1.refs);
  check "algorithm float extracted"
    (List.exists
       (function
         | Latex_parse_lib.Parser_l2.Float { kind = "algorithm"; _ } -> true
         | _ -> false)
       doc1.body);

  (* Empty document *)
  let doc2 = Latex_parse_lib.Parser_l2.extract_document "" in
  check "empty doc: no packages" (doc2.packages = []);
  check "empty doc: no docclass" (doc2.documentclass = None);

  (* ── Starred commands ──────────────────────────────────────── *)
  let nodes_star = Latex_parse_lib.Parser_l2.parse {|\section*{Unnumbered}|} in
  check "section* name includes star"
    (List.exists
       (function
         | Latex_parse_lib.Parser_l2.Cmd { name = "section*"; _ } -> true
         | _ -> false)
       nodes_star);

  let nodes_chap = Latex_parse_lib.Parser_l2.parse {|\chapter*{Preface}|} in
  check "chapter* name includes star"
    (List.exists
       (function
         | Latex_parse_lib.Parser_l2.Cmd { name = "chapter*"; _ } -> true
         | _ -> false)
       nodes_chap);

  (* ── \verb|...| support ────────────────────────────────────── *)
  let nodes_verb = Latex_parse_lib.Parser_l2.parse {|\verb|foo_bar||} in
  check "verb → Verbatim"
    (List.exists
       (function
         | Latex_parse_lib.Parser_l2.Verbatim { env_name = "verb"; content } ->
             content = "foo_bar"
         | _ -> false)
       nodes_verb);

  let nodes_verb2 = Latex_parse_lib.Parser_l2.parse {|\verb!x + y!|} in
  check "verb with ! delimiter"
    (List.exists
       (function
         | Latex_parse_lib.Parser_l2.Verbatim
             { env_name = "verb"; content = "x + y" } ->
             true
         | _ -> false)
       nodes_verb2);

  (* ── \part and \subparagraph ────────────────────────────────── *)
  let doc_part =
    Latex_parse_lib.Parser_l2.extract_document
      {|\begin{document}\part{One}\subparagraph{Deep}\end{document}|}
  in
  check "part in body"
    (List.exists
       (function
         | Latex_parse_lib.Parser_l2.Section { level = -1; title = "One"; _ } ->
             true
         | _ -> false)
       doc_part.body);
  check "subparagraph in body"
    (List.exists
       (function
         | Latex_parse_lib.Parser_l2.Section { level = 5; title = "Deep"; _ } ->
             true
         | _ -> false)
       doc_part.body);

  (* ── \bibliography tracking ─────────────────────────────────── *)
  let doc_bib =
    Latex_parse_lib.Parser_l2.extract_document
      {|\bibliographystyle{plain}
\bibliography{refs}
\begin{document}
Hello
\end{document}|}
  in
  check "bibliography tracked"
    (List.exists
       (fun (p, o, _) -> p = "refs" && o = Some "bibliography")
       doc_bib.packages);
  check "bibliographystyle tracked"
    (List.exists
       (fun (p, o, _) -> p = "plain" && o = Some "bibliographystyle")
       doc_bib.packages);

  Printf.printf "[test_parser_l2_envs] done\n%!";
  if !fails > 0 then (
    Printf.eprintf "[test_parser_l2_envs] %d failures\n%!" !fails;
    exit 1)
