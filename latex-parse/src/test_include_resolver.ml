(** Tests for include_resolver: parsing and path resolution. *)

open Latex_parse_lib
open Test_helpers

let () =
  run "extract \\input{file}" (fun tag ->
      let src = "\\input{chapter1}" in
      let entries = Include_resolver.extract_includes src in
      expect (List.length entries = 1) (tag ^ ": 1 entry");
      let e = List.hd entries in
      expect (e.command = "input") (tag ^ ": command=input");
      expect (e.raw_path = "chapter1") (tag ^ ": path=chapter1"));

  run "extract \\include{file}" (fun tag ->
      let src = "\\include{appendix}" in
      let entries = Include_resolver.extract_includes src in
      expect (List.length entries = 1) (tag ^ ": 1 entry");
      expect ((List.hd entries).command = "include") (tag ^ ": command=include"));

  run "extract multiple includes" (fun tag ->
      let src = "\\input{a}\n\\include{b}\n\\input{c}" in
      let entries = Include_resolver.extract_includes src in
      expect (List.length entries = 3) (tag ^ ": 3 entries"));

  run "extract preserves order" (fun tag ->
      let src = "\\input{first}\n\\include{second}" in
      let entries = Include_resolver.extract_includes src in
      expect ((List.hd entries).raw_path = "first") (tag ^ ": first"));

  run "extract empty source" (fun tag ->
      let entries = Include_resolver.extract_includes "" in
      expect (entries = []) (tag ^ ": empty"));

  run "extract with spaces in braces" (fun tag ->
      let src = "\\input{ chapter1 }" in
      let entries = Include_resolver.extract_includes src in
      expect (List.length entries = 1) (tag ^ ": 1 entry");
      expect ((List.hd entries).raw_path = "chapter1") (tag ^ ": trimmed"));

  run "extract_includeonly" (fun tag ->
      let src = "\\includeonly{ch1,ch2,ch3}" in
      let names = Include_resolver.extract_includeonly src in
      expect (List.length names = 3) (tag ^ ": 3 names");
      expect (List.hd names = "ch1") (tag ^ ": first=ch1"));

  run "extract_includeonly empty" (fun tag ->
      let names = Include_resolver.extract_includeonly "" in
      expect (names = []) (tag ^ ": empty"));

  run "resolve existing file" (fun tag ->
      (* Use the corpus files we just created *)
      let base = "../../corpora/multi_file" in
      let entry =
        {
          Include_resolver.command = "input";
          raw_path = "chapter1";
          position = 0;
        }
      in
      let ri = Include_resolver.resolve_include ~base_dir:base entry in
      expect (ri.resolved_path <> None) (tag ^ ": resolved"));

  run "resolve nonexistent file" (fun tag ->
      let entry =
        {
          Include_resolver.command = "input";
          raw_path = "nonexistent_xyz";
          position = 0;
        }
      in
      let ri = Include_resolver.resolve_include ~base_dir:"/tmp" entry in
      expect (ri.resolved_path = None) (tag ^ ": unresolved"));

  run "resolve with .tex extension" (fun tag ->
      let base = "../../corpora/multi_file" in
      let entry =
        {
          Include_resolver.command = "input";
          raw_path = "shared";
          position = 0;
        }
      in
      let ri = Include_resolver.resolve_include ~base_dir:base entry in
      expect (ri.resolved_path <> None) (tag ^ ": resolved via .tex"));

  run "resolve_all multiple" (fun tag ->
      let base = "../../corpora/multi_file" in
      let entries =
        [
          {
            Include_resolver.command = "input";
            raw_path = "chapter1";
            position = 0;
          };
          {
            Include_resolver.command = "include";
            raw_path = "nonexistent";
            position = 20;
          };
        ]
      in
      let resolved = Include_resolver.resolve_all ~base_dir:base entries in
      expect (List.length resolved = 2) (tag ^ ": 2 results");
      expect
        ((List.hd resolved).resolved_path <> None)
        (tag ^ ": first resolved");
      expect
        ((List.nth resolved 1).resolved_path = None)
        (tag ^ ": second unresolved"))

let () = finalise "include-resolver"
