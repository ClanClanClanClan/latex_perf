(** Tests for semantic_state — label/ref tracking (spec W53-57). *)

let fails = ref 0

let check name cond =
  if not cond then (
    Printf.eprintf "FAIL: %s\n%!" name;
    incr fails)
  else Printf.printf "  ok  %s\n%!" name

let () =
  Printf.printf "[test_semantic_state]\n%!";

  (* Test 1: extract labels from document *)
  let labels =
    Latex_parse_lib.Semantic_state.extract_labels
      {|\label{eq:1} text \label{fig:a} more \label{eq:1}|}
  in
  check "extract 3 labels" (List.length labels = 3);

  (* Test 2: extract refs *)
  let refs =
    Latex_parse_lib.Semantic_state.extract_refs
      {|\ref{eq:1} and \eqref{eq:2} and \autoref{fig:a}|}
  in
  check "extract 3 refs" (List.length refs = 3);

  (* Test 3: analyze finds duplicates *)
  let state =
    Latex_parse_lib.Semantic_state.analyze
      {|\label{eq:1} \label{eq:1} \ref{fig:x}|}
  in
  check "duplicate detected" (state.duplicate_labels <> []);

  (* Test 4: analyze finds undefined refs *)
  let state2 =
    Latex_parse_lib.Semantic_state.analyze
      {|\label{eq:1} \ref{eq:1} \ref{undefined}|}
  in
  check "undefined ref detected" (state2.undefined_refs <> []);

  (* Test 5: no labels = no duplicates *)
  let state3 = Latex_parse_lib.Semantic_state.analyze "Hello world." in
  check "no labels = no duplicates" (state3.duplicate_labels = []);
  check "no refs = no undefined" (state3.undefined_refs = []);

  (* Test 6: empty input *)
  let state4 = Latex_parse_lib.Semantic_state.analyze "" in
  check "empty: no labels" (state4.labels = []);
  check "empty: no refs" (state4.refs = []);

  (* Test 7: state set/get/clear round-trip *)
  Latex_parse_lib.Semantic_state.set_state state;
  let retrieved = Latex_parse_lib.Semantic_state.get_state () in
  check "get_state after set" (retrieved <> None);
  Latex_parse_lib.Semantic_state.clear_state ();
  let cleared = Latex_parse_lib.Semantic_state.get_state () in
  check "get_state after clear = None" (cleared = None);

  (* Test 8: forward refs *)
  let state5 =
    Latex_parse_lib.Semantic_state.analyze {|\ref{later} text \label{later}|}
  in
  check "forward ref detected" (state5.forward_refs <> []);

  Printf.printf "[test_semantic_state] done\n%!";
  if !fails > 0 then (
    Printf.eprintf "[test_semantic_state] %d failures\n%!" !fails;
    exit 1)
