(** Tests for Section_rebalance (spec W48-49). *)

let fails = ref 0

let check name cond =
  if not cond then (
    Printf.eprintf "FAIL: %s\n%!" name;
    incr fails)
  else Printf.printf "  ok  %s\n%!" name

let () =
  Printf.printf "[test_section_rebalance]\n%!";

  (* Test 1: extract sections from simple document *)
  let src =
    {|\section{Introduction}
Some text.
\subsection{Background}
More text.
\section{Methods}
Even more.
\subsection{Data}
Data description.
\subsubsection{Collection}
Details.|}
  in
  let raw = Latex_parse_lib.Section_rebalance.extract_sections src in
  check "extract_sections count" (List.length raw = 5);
  check "first is section" ((List.nth raw 0).rs_level = 1);
  check "second is subsection" ((List.nth raw 1).rs_level = 2);
  check "third is section" ((List.nth raw 2).rs_level = 1);
  check "fourth is subsection" ((List.nth raw 3).rs_level = 2);
  check "fifth is subsubsection" ((List.nth raw 4).rs_level = 3);

  (* Test 2: build tree *)
  let tree = Latex_parse_lib.Section_rebalance.build_tree raw in
  check "tree has 2 top-level sections" (List.length tree = 2);
  let s1 = List.nth tree 0 in
  check "s1 title" (s1.title = "Introduction");
  check "s1 number" (s1.number = 1);
  let s2 = List.nth tree 1 in
  check "s2 title" (s2.title = "Methods");
  check "s2 number" (s2.number = 2);

  (* Test 3: renumber after delete *)
  let tree2 =
    Latex_parse_lib.Section_rebalance.renumber
      [List.nth tree 1]  (* keep only Methods *)
  in
  check "renumbered Methods = 1" ((List.nth tree2 0).number = 1);

  (* Test 4: validate level-skip *)
  let bad_raw : Latex_parse_lib.Section_rebalance.raw_section list =
    [
      { rs_level = 1; rs_name = "section"; rs_title = "A"; rs_label = None; rs_offset = 0 };
      { rs_level = 3; rs_name = "subsubsection"; rs_title = "B"; rs_label = None; rs_offset = 50 };
    ]
  in
  let bad_tree = Latex_parse_lib.Section_rebalance.build_tree bad_raw in
  let violations = Latex_parse_lib.Section_rebalance.validate bad_tree in
  check "level-skip detected" (List.length violations >= 1);

  (* Test 5: valid structure has no violations *)
  let good_violations = Latex_parse_lib.Section_rebalance.validate tree in
  if List.length good_violations > 0 then
    List.iter (fun (v : Latex_parse_lib.Section_rebalance.violation) ->
      Printf.eprintf "  violation: %s expected_max=%d actual=%d\n%!" v.v_title v.v_expected_max_level v.v_actual_level)
      good_violations;
  check "good tree no violations" (List.length good_violations = 0);

  (* Test 6: flatten roundtrip *)
  let flat = Latex_parse_lib.Section_rebalance.flatten tree in
  check "flatten preserves count" (List.length flat = 5);

  (* Test 7: extract_tree shortcut *)
  let tree3 = Latex_parse_lib.Section_rebalance.extract_tree src in
  check "extract_tree works" (List.length tree3 = 2);

  (* Test 8: empty document *)
  let empty_tree = Latex_parse_lib.Section_rebalance.extract_tree "" in
  check "empty document" (List.length empty_tree = 0);

  (* Test 9: document with chapters *)
  let chapter_src = {|\chapter{One}\section{A}\section{B}\chapter{Two}\section{C}|} in
  let chapter_tree = Latex_parse_lib.Section_rebalance.extract_tree chapter_src in
  check "chapters count" (List.length chapter_tree = 2);

  (* Test 10: star sections *)
  let star_src = {|\section*{Unnumbered}\subsection{Sub}|} in
  let star_raw = Latex_parse_lib.Section_rebalance.extract_sections star_src in
  check "star section extracted" (List.length star_raw >= 1);

  Printf.printf "[test_section_rebalance] done\n%!";
  if !fails > 0 then (
    Printf.eprintf "[test_section_rebalance] %d failures\n%!" !fails;
    exit 1)
