(** Tests for WS2 user macro registry.

    Covers parsing, classification, dependency edges, cycle detection, and
    argsafe entry conversion. *)

open Latex_parse_lib
open Test_helpers

(* ── Parsing tests ───────────────────────────────────────────────── *)

let () =
  run "parse simple \\newcommand" (fun tag ->
      let src = "\\newcommand{\\foo}{hello}" in
      let defs = User_macro_registry.parse_definitions src in
      expect (List.length defs = 1) (tag ^ ": 1 def");
      let d = List.hd defs in
      expect (d.name = "foo") (tag ^ ": name=foo");
      expect (d.arity = 0) (tag ^ ": arity=0");
      expect (d.body = "hello") (tag ^ ": body=hello");
      expect (d.kind = User_macro_registry.Newcommand) (tag ^ ": kind=New"));

  run "parse \\renewcommand" (fun tag ->
      let src = "\\renewcommand{\\bar}{world}" in
      let defs = User_macro_registry.parse_definitions src in
      expect (List.length defs = 1) (tag ^ ": 1 def");
      let d = List.hd defs in
      expect (d.name = "bar") (tag ^ ": name=bar");
      expect (d.kind = User_macro_registry.Renewcommand) (tag ^ ": kind=Renew"));

  run "parse \\providecommand" (fun tag ->
      let src = "\\providecommand{\\baz}{stuff}" in
      let defs = User_macro_registry.parse_definitions src in
      expect (List.length defs = 1) (tag ^ ": 1 def");
      let d = List.hd defs in
      expect
        (d.kind = User_macro_registry.Providecommand)
        (tag ^ ": kind=Provide"));

  run "parse with arity" (fun tag ->
      let src = "\\newcommand{\\myop}[2]{#1 + #2}" in
      let defs = User_macro_registry.parse_definitions src in
      expect (List.length defs = 1) (tag ^ ": 1 def");
      let d = List.hd defs in
      expect (d.arity = 2) (tag ^ ": arity=2");
      expect (d.body = "#1 + #2") (tag ^ ": body correct"));

  run "parse with default arg" (fun tag ->
      let src = "\\newcommand{\\greet}[1][World]{Hello #1}" in
      let defs = User_macro_registry.parse_definitions src in
      expect (List.length defs = 1) (tag ^ ": 1 def");
      let d = List.hd defs in
      expect (d.arity = 1) (tag ^ ": arity=1");
      expect (d.opt_default = Some "World") (tag ^ ": default=World"));

  run "parse star form" (fun tag ->
      let src = "\\newcommand*{\\starred}{text}" in
      let defs = User_macro_registry.parse_definitions src in
      expect (List.length defs = 1) (tag ^ ": 1 def");
      expect ((List.hd defs).name = "starred") (tag ^ ": name=starred"));

  run "parse no-brace name form" (fun tag ->
      let src = "\\newcommand\\nobrace{text}" in
      let defs = User_macro_registry.parse_definitions src in
      expect (List.length defs = 1) (tag ^ ": 1 def");
      expect ((List.hd defs).name = "nobrace") (tag ^ ": name"));

  run "parse multiple definitions" (fun tag ->
      let src =
        "\\newcommand{\\aaa}{one}\n\
         \\renewcommand{\\bbb}{two}\n\
         \\providecommand{\\ccc}{three}"
      in
      let defs = User_macro_registry.parse_definitions src in
      expect (List.length defs = 3) (tag ^ ": 3 defs"));

  run "parse nested braces in body" (fun tag ->
      let src = "\\newcommand{\\nested}{outer{inner{deep}}}" in
      let defs = User_macro_registry.parse_definitions src in
      expect (List.length defs = 1) (tag ^ ": 1 def");
      expect ((List.hd defs).body = "outer{inner{deep}}") (tag ^ ": body"));

  run "parse empty source" (fun tag ->
      let defs = User_macro_registry.parse_definitions "" in
      expect (defs = []) (tag ^ ": empty"));

  (* ── Classification tests ──────────────────────────────────────── *)
  run "classify supported macro" (fun tag ->
      let def =
        {
          User_macro_registry.kind = Newcommand;
          name = "foo";
          arity = 1;
          opt_default = None;
          body = "\\textbf{#1}";
          loc = 0;
        }
      in
      let cd = User_macro_registry.classify def in
      expect (cd.status = Supported) (tag ^ ": supported"));

  run "classify unsupported: \\def in body" (fun tag ->
      let def =
        {
          User_macro_registry.kind = Newcommand;
          name = "bad";
          arity = 0;
          opt_default = None;
          body = "\\def\\inner{x}";
          loc = 0;
        }
      in
      let cd = User_macro_registry.classify def in
      match cd.status with
      | User_macro_registry.Unsupported reason ->
          expect (String.length reason > 0) (tag ^ ": has reason: " ^ reason)
      | Supported -> expect false (tag ^ ": should be unsupported"));

  run "classify unsupported: \\catcode" (fun tag ->
      let def =
        {
          User_macro_registry.kind = Newcommand;
          name = "bad2";
          arity = 0;
          opt_default = None;
          body = "\\catcode`@=11";
          loc = 0;
        }
      in
      let cd = User_macro_registry.classify def in
      match cd.status with
      | User_macro_registry.Unsupported _ -> expect true (tag ^ ": unsupported")
      | Supported -> expect false (tag ^ ": should be unsupported"));

  run "classify unsupported: conditional \\ifx" (fun tag ->
      let def =
        {
          User_macro_registry.kind = Newcommand;
          name = "cond";
          arity = 0;
          opt_default = None;
          body = "\\ifx\\foo\\bar yes\\fi";
          loc = 0;
        }
      in
      let cd = User_macro_registry.classify def in
      match cd.status with
      | User_macro_registry.Unsupported _ -> expect true (tag ^ ": unsupported")
      | Supported -> expect false (tag ^ ": should be unsupported"));

  run "classify unsupported: \\expandafter" (fun tag ->
      let def =
        {
          User_macro_registry.kind = Newcommand;
          name = "exp";
          arity = 0;
          opt_default = None;
          body = "\\expandafter\\foo\\bar";
          loc = 0;
        }
      in
      let cd = User_macro_registry.classify def in
      match cd.status with
      | User_macro_registry.Unsupported _ -> expect true (tag ^ ": unsupported")
      | Supported -> expect false (tag ^ ": should be unsupported"));

  run "classify unsupported: arity > 9" (fun tag ->
      let def =
        {
          User_macro_registry.kind = Newcommand;
          name = "toomany";
          arity = 10;
          opt_default = None;
          body = "text";
          loc = 0;
        }
      in
      let cd = User_macro_registry.classify def in
      match cd.status with
      | User_macro_registry.Unsupported _ -> expect true (tag ^ ": unsupported")
      | Supported -> expect false (tag ^ ": should be unsupported"));

  (* ── Dependency edge tests ─────────────────────────────────────── *)
  run "dep edges: A uses B" (fun tag ->
      let defs =
        [
          {
            User_macro_registry.kind = Newcommand;
            name = "outer";
            arity = 0;
            opt_default = None;
            body = "\\inner world";
            loc = 0;
          };
          {
            User_macro_registry.kind = Newcommand;
            name = "inner";
            arity = 0;
            opt_default = None;
            body = "hello";
            loc = 30;
          };
        ]
      in
      let edges = User_macro_registry.build_dep_edges defs in
      expect (List.length edges = 1) (tag ^ ": 1 edge");
      let e = List.hd edges in
      expect
        (e.from_name = "outer" && e.to_name = "inner")
        (tag ^ ": outer->inner"));

  run "dep edges: no self-edges" (fun tag ->
      let defs =
        [
          {
            User_macro_registry.kind = Newcommand;
            name = "self";
            arity = 0;
            opt_default = None;
            body = "\\self";
            loc = 0;
          };
        ]
      in
      let edges = User_macro_registry.build_dep_edges defs in
      expect (edges = []) (tag ^ ": no self edges"));

  run "dep edges: no edges to non-user macros" (fun tag ->
      let defs =
        [
          {
            User_macro_registry.kind = Newcommand;
            name = "user";
            arity = 0;
            opt_default = None;
            body = "\\textbf{hello}";
            loc = 0;
          };
        ]
      in
      let edges = User_macro_registry.build_dep_edges defs in
      expect (edges = []) (tag ^ ": no edges to builtins"));

  (* ── Cycle detection tests ─────────────────────────────────────── *)
  run "detect_cycle: acyclic" (fun tag ->
      let edges =
        [
          { User_macro_registry.from_name = "a"; to_name = "b" };
          { from_name = "b"; to_name = "c" };
        ]
      in
      let has_cycle, _ =
        User_macro_registry.detect_cycle edges [ "a"; "b"; "c" ]
      in
      expect (not has_cycle) (tag ^ ": no cycle"));

  run "detect_cycle: simple cycle" (fun tag ->
      let edges =
        [
          { User_macro_registry.from_name = "a"; to_name = "b" };
          { from_name = "b"; to_name = "a" };
        ]
      in
      let has_cycle, path =
        User_macro_registry.detect_cycle edges [ "a"; "b" ]
      in
      expect has_cycle (tag ^ ": has cycle");
      expect (List.length path > 0) (tag ^ ": path non-empty"));

  run "detect_cycle: diamond (no cycle)" (fun tag ->
      let edges =
        [
          { User_macro_registry.from_name = "a"; to_name = "b" };
          { User_macro_registry.from_name = "a"; to_name = "c" };
          { User_macro_registry.from_name = "b"; to_name = "d" };
          { User_macro_registry.from_name = "c"; to_name = "d" };
        ]
      in
      let has_cycle, _ =
        User_macro_registry.detect_cycle edges [ "a"; "b"; "c"; "d" ]
      in
      expect (not has_cycle) (tag ^ ": diamond is acyclic"));

  (* ── Full registry (create) tests ──────────────────────────────── *)
  run "create: simple document" (fun tag ->
      let src =
        "\\documentclass{article}\n\
         \\newcommand{\\myop}{\\operatorname{myop}}\n\
         \\newcommand{\\myval}[1]{\\textbf{#1}}\n\
         \\begin{document}\n\
         $\\myop(x)$ is \\myval{good}\n\
         \\end{document}"
      in
      let reg = User_macro_registry.create src in
      expect (List.length reg.defs = 2) (tag ^ ": 2 defs");
      expect (reg.supported_count = 2) (tag ^ ": 2 supported");
      expect (reg.unsupported_count = 0) (tag ^ ": 0 unsupported");
      expect (not reg.has_cycle) (tag ^ ": no cycle"));

  run "create: mixed supported/unsupported" (fun tag ->
      let src =
        "\\newcommand{\\good}{hello}\n\\newcommand{\\bad}{\\def\\inner{x}}\n"
      in
      let reg = User_macro_registry.create src in
      expect (reg.supported_count = 1) (tag ^ ": 1 supported");
      expect (reg.unsupported_count = 1) (tag ^ ": 1 unsupported"));

  run "create: cycle detection" (fun tag ->
      let src = "\\newcommand{\\aaa}{\\bbb}\n\\newcommand{\\bbb}{\\aaa}\n" in
      let reg = User_macro_registry.create src in
      expect reg.has_cycle (tag ^ ": has cycle"));

  (* ── param_to_placeholder tests ──────────────────────────────── *)
  run "param_to_placeholder: #1 -> $1" (fun tag ->
      let result = User_macro_registry.param_to_placeholder "#1 + #2" in
      expect (result = "$1 + $2") (tag ^ ": converted"));

  run "param_to_placeholder: no params unchanged" (fun tag ->
      let result = User_macro_registry.param_to_placeholder "hello world" in
      expect (result = "hello world") (tag ^ ": unchanged"))

let () = finalise "user-macro-registry"
