(** Tests for Incremental_nlp — sentence-level diff (spec W76). *)

let fails = ref 0

let check name cond =
  if not cond then (
    Printf.eprintf "FAIL: %s\n%!" name;
    incr fails)
  else Printf.printf "  ok  %s\n%!" name

let () =
  Printf.printf "[test_incremental_nlp]\n%!";

  (* Test 1: identical documents → no changes *)
  let doc = "First sentence. Second sentence. Third sentence." in
  let diff = Latex_parse_lib.Incremental_nlp.compute_diff doc doc in
  check "identical: 0 changes" (diff.changes = []);
  check "identical: all unchanged" (diff.unchanged_count = 3);
  check "identical: cache hit 100%"
    (Latex_parse_lib.Incremental_nlp.cache_hit_rate diff = 1.0);

  (* Test 2: added sentence *)
  let old_doc = "First. Second." in
  let new_doc = "First. Second. Third." in
  let diff2 = Latex_parse_lib.Incremental_nlp.compute_diff old_doc new_doc in
  check "added: has changes" (diff2.changes <> []);
  check "added: total_new > total_old" (diff2.total_new > diff2.total_old);
  let to_proc = Latex_parse_lib.Incremental_nlp.sentences_to_process diff2 in
  check "added: 1 to process" (List.length to_proc >= 1);

  (* Test 3: removed sentence *)
  let diff3 = Latex_parse_lib.Incremental_nlp.compute_diff new_doc old_doc in
  check "removed: has changes" (diff3.changes <> []);
  check "removed: total_old > total_new" (diff3.total_old > diff3.total_new);

  (* Test 4: modified sentence *)
  let old_mod = "Hello world. Goodbye world." in
  let new_mod = "Hello world. Farewell world." in
  let diff4 = Latex_parse_lib.Incremental_nlp.compute_diff old_mod new_mod in
  check "modified: has changes" (diff4.changes <> []);
  check "modified: 1 unchanged" (diff4.unchanged_count = 1);

  (* Test 5: empty documents *)
  let diff5 = Latex_parse_lib.Incremental_nlp.compute_diff "" "" in
  check "empty: 0 changes" (diff5.changes = []);
  check "empty: cache hit 100%"
    (Latex_parse_lib.Incremental_nlp.cache_hit_rate diff5 = 1.0);

  (* Test 6: empty → non-empty *)
  let diff6 = Latex_parse_lib.Incremental_nlp.compute_diff "" "New sentence." in
  check "empty→nonempty: 1 change" (List.length diff6.changes >= 1);

  Printf.printf "[test_incremental_nlp] done\n%!";
  if !fails > 0 then (
    Printf.eprintf "[test_incremental_nlp] %d failures\n%!" !fails;
    exit 1)
