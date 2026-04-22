(** Unit tests for [Aux_state]. *)

open Latex_parse_lib
open Test_helpers

let sample_aux =
  {|\relax
\providecommand\HyperFirstAtBeginDocument{\AtBeginDocument}
\newlabel{sec:intro}{{1}{1}{Introduction}{section.1}{}}
\newlabel{eq:main}{{2.1}{3}{Main equation}{equation.2.1}{}}
\bibstyle{plain}
\bibdata{refs,chapter1}
\bibcite{knuth1984}{1}
\bibcite{lamport1994}{2}
\@writefile{toc}{\contentsline {section}{\numberline {1}Introduction}{1}{section.1}\protected@file@percent }
|}

let () =
  run "of_string parses a minimal aux" (fun tag ->
      let t = Aux_state.of_string ~source_path:"test.aux" sample_aux in
      expect (List.length t.labels = 2) (tag ^ ": 2 labels");
      expect (List.length t.bibcites = 2) (tag ^ ": 2 bibcites");
      expect (t.bibstyle = Some "plain") (tag ^ ": bibstyle=plain");
      expect (List.length t.bibdata = 2) (tag ^ ": 2 bibdata entries"));

  run "find_label locates a known label" (fun tag ->
      let t = Aux_state.of_string ~source_path:"test.aux" sample_aux in
      match Aux_state.find_label t "sec:intro" with
      | Some l ->
          expect (l.ref_number = "1") (tag ^ ": ref=1");
          expect (l.page_number = "1") (tag ^ ": page=1")
      | None -> expect false (tag ^ ": should find sec:intro"));

  run "find_label returns None for missing" (fun tag ->
      let t = Aux_state.of_string ~source_path:"test.aux" sample_aux in
      expect
        (Aux_state.find_label t "nonexistent" = None)
        (tag ^ ": None on missing"));

  run "find_bibcite returns bib number" (fun tag ->
      let t = Aux_state.of_string ~source_path:"test.aux" sample_aux in
      match Aux_state.find_bibcite t "knuth1984" with
      | Some b -> expect (b.number = "1") (tag ^ ": number=1")
      | None -> expect false (tag ^ ": should find knuth1984"));

  run "labels_unique detects duplicates" (fun tag ->
      let dup_aux =
        {|\newlabel{a}{{1}{1}{X}{y}{}}
\newlabel{a}{{2}{2}{Y}{z}{}}
|}
      in
      let t = Aux_state.of_string ~source_path:"t.aux" dup_aux in
      expect (not (Aux_state.labels_unique t)) (tag ^ ": duplicates caught"));

  run "labels_unique true on clean" (fun tag ->
      let t = Aux_state.of_string ~source_path:"t.aux" sample_aux in
      expect (Aux_state.labels_unique t) (tag ^ ": no dupes in sample"));

  run "nested braces in label title parsed" (fun tag ->
      let nested =
        {|\newlabel{sec:foo}{{1}{1}{Title with {braces} inside}{section.1}{}}
|}
      in
      let t = Aux_state.of_string ~source_path:"t.aux" nested in
      expect (List.length t.labels = 1) (tag ^ ": parsed despite braces");
      match Aux_state.find_label t "sec:foo" with
      | Some l -> expect (l.ref_number = "1") (tag ^ ": ref=1")
      | None -> expect false (tag ^ ": found"));

  run "empty input produces empty t" (fun tag ->
      let t = Aux_state.of_string ~source_path:"" "" in
      expect (t.labels = []) (tag ^ ": no labels");
      expect (t.bibcites = []) (tag ^ ": no bibcites");
      expect (t.bibstyle = None) (tag ^ ": no bibstyle"));

  run "of_file missing returns error" (fun tag ->
      match Aux_state.of_file "/nonexistent/ghost.aux" with
      | Error (`File_not_found _) -> expect true (tag ^ ": correct error")
      | _ -> expect false (tag ^ ": should error"));

  finalise "aux-state"
