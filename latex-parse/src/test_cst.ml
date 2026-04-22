(** Tests for [Cst] (type + serialize). *)

open Latex_parse_lib
open Test_helpers

let span a b = Stable_spans.make ~start_offset:a ~end_offset:b

let () =
  run "serialize CToken" (fun tag ->
      let n = Cst.CToken { kind = Cst.Word; text = "hello"; span = span 0 5 } in
      expect (Cst.serialize [ n ] = "hello") (tag ^ ": 'hello'"));

  run "serialize CTrivia" (fun tag ->
      let n =
        Cst.CTrivia { kind = Cst.Whitespace; text = "  "; span = span 0 2 }
      in
      expect (Cst.serialize [ n ] = "  ") (tag ^ ": whitespace preserved"));

  run "serialize CUnparsed byte-lossless" (fun tag ->
      let n = Cst.CUnparsed { text = "\\foo[a]{b}"; span = span 0 10 } in
      expect (Cst.serialize [ n ] = "\\foo[a]{b}")
        (tag ^ ": unparsed roundtrip"));

  run "serialize concatenates" (fun tag ->
      let nodes =
        [
          Cst.CToken { kind = Cst.Word; text = "ab"; span = span 0 2 };
          Cst.CTrivia { kind = Cst.Whitespace; text = " "; span = span 2 3 };
          Cst.CToken { kind = Cst.Word; text = "cd"; span = span 3 5 };
        ]
      in
      expect (Cst.serialize nodes = "ab cd") (tag ^ ": concat"));

  run "serialize CGroup wraps children in braces" (fun tag ->
      let child =
        Cst.CToken { kind = Cst.Word; text = "x"; span = span 1 2 }
      in
      let g = Cst.CGroup { children = [ child ]; span = span 0 3 } in
      expect (Cst.serialize [ g ] = "{x}") (tag ^ ": '{x}'"));

  run "serialize CEnvironment wraps body in begin/end" (fun tag ->
      let e =
        Cst.CEnvironment
          {
            env_name = "itemize";
            body_text = "\\item foo";
            span = span 0 30;
          }
      in
      expect
        (Cst.serialize [ e ]
        = "\\begin{itemize}\\item foo\\end{itemize}")
        (tag ^ ": environment"));

  run "serialize CMathInline preserves delimiters" (fun tag ->
      let m = Cst.CMathInline { text = "$x^2$"; span = span 0 5 } in
      expect (Cst.serialize [ m ] = "$x^2$") (tag ^ ": '$x^2$'"));

  run "serialize CVerbatim opaque" (fun tag ->
      let v =
        Cst.CVerbatim
          {
            env_name = "verbatim";
            text = "\\begin{verbatim}abc\\end{verbatim}";
            span = span 0 33;
          }
      in
      expect
        (Cst.serialize [ v ]
        = "\\begin{verbatim}abc\\end{verbatim}")
        (tag ^ ": verbatim"));

  run "byte_length matches serialize" (fun tag ->
      let nodes =
        [
          Cst.CToken { kind = Cst.Word; text = "ab"; span = span 0 2 };
          Cst.CTrivia { kind = Cst.Whitespace; text = " "; span = span 2 3 };
        ]
      in
      expect
        (Cst.byte_length nodes = String.length (Cst.serialize nodes))
        (tag ^ ": byte_length agrees"));

  run "span_of returns node span" (fun tag ->
      let n = Cst.CToken { kind = Cst.Word; text = "hi"; span = span 7 9 } in
      let s = Cst.span_of n in
      expect (s.start_offset = 7 && s.end_offset = 9)
        (tag ^ ": span [7,9)"));

  finalise "cst"
