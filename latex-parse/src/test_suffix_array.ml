(** Tests for suffix_array — O(n log^2 n) build + dirty region detection (spec
    W46). *)

let fails = ref 0

let check name cond =
  if not cond then (
    Printf.eprintf "FAIL: %s\n%!" name;
    incr fails)
  else Printf.printf "  ok  %s\n%!" name

let () =
  Printf.printf "[test_suffix_array]\n%!";

  (* Test 1: build doesn't crash *)
  let _sa = Latex_parse_lib.Suffix_array.build "hello world" in
  check "build succeeds" true;

  (* Test 2: build on empty string *)
  let sa_empty = Latex_parse_lib.Suffix_array.build "" in
  let r = Latex_parse_lib.Suffix_array.search sa_empty "x" in
  check "empty string: search = empty" (r = []);

  (* Test 3: build on single char *)
  let sa1 = Latex_parse_lib.Suffix_array.build "x" in
  let r1 = Latex_parse_lib.Suffix_array.search sa1 "x" in
  check "single char found" (r1 <> []);

  (* Test 4: search for empty pattern returns empty *)
  let sa2 = Latex_parse_lib.Suffix_array.build "hello" in
  let r2 = Latex_parse_lib.Suffix_array.search sa2 "" in
  check "empty pattern = empty" (r2 = []);

  (* Test 5: dirty region detection — identical strings *)
  let dr = Latex_parse_lib.Suffix_array.find_dirty_regions "hello" "hello" in
  check "identical = no dirty regions" (dr = []);

  (* Test 6: dirty region — insertion *)
  let dr2 =
    Latex_parse_lib.Suffix_array.find_dirty_regions "abcdef" "abcXdef"
  in
  check "insertion: dirty region found" (dr2 <> []);

  (* Test 7: dirty region — deletion *)
  let dr3 = Latex_parse_lib.Suffix_array.find_dirty_regions "abcdef" "abdef" in
  check "deletion: dirty region found" (dr3 <> []);

  (* Test 8: completely different strings *)
  let dr4 = Latex_parse_lib.Suffix_array.find_dirty_regions "aaa" "zzz" in
  check "completely different: dirty found" (dr4 <> []);

  (* Test 9: single char change *)
  let dr5 = Latex_parse_lib.Suffix_array.find_dirty_regions "abc" "aXc" in
  check "single char change: dirty found" (dr5 <> []);

  Printf.printf "[test_suffix_array] done\n%!";
  if !fails > 0 then (
    Printf.eprintf "[test_suffix_array] %d failures\n%!" !fails;
    exit 1)
