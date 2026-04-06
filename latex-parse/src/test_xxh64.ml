(** Tests for xxh64 — scalar xxHash64 (spec W4, W9). *)

let fails = ref 0

let check name cond =
  if not cond then (
    Printf.eprintf "FAIL: %s\n%!" name;
    incr fails)
  else Printf.printf "  ok  %s\n%!" name

let () =
  Printf.printf "[test_xxh64]\n%!";

  (* Test 1: determinism — same input → same hash *)
  let b = Bytes.of_string "hello world" in
  let h1 = Latex_parse_lib.Xxh64.hash64_bytes b in
  let h2 = Latex_parse_lib.Xxh64.hash64_bytes b in
  check "deterministic" (h1 = h2);

  (* Test 2: different inputs → different hashes *)
  let b2 = Bytes.of_string "hello worlD" in
  let h3 = Latex_parse_lib.Xxh64.hash64_bytes b2 in
  check "different input = different hash" (h1 <> h3);

  (* Test 3: empty input *)
  let h_empty = Latex_parse_lib.Xxh64.hash64_bytes (Bytes.of_string "") in
  check "empty input produces hash" (h_empty <> 0L);

  (* Test 4: single byte *)
  let h_one = Latex_parse_lib.Xxh64.hash64_bytes (Bytes.of_string "x") in
  check "single byte produces hash" (h_one <> 0L);
  check "single byte != empty hash" (h_one <> h_empty);

  (* Test 5: known test vector — xxh64 of empty with seed 0 should be
     0xEF46DB3751D8E999 per the official XXH64 spec *)
  let expected_empty = 0xEF46DB3751D8E999L in
  check "empty hash matches XXH64 spec" (h_empty = expected_empty);

  (* Test 6: 32-byte input (exercises the main accumulator loop) *)
  let b32 = Bytes.make 32 'A' in
  let h32 = Latex_parse_lib.Xxh64.hash64_bytes b32 in
  check "32-byte hash non-zero" (h32 <> 0L);

  (* Test 7: 64-byte input (two full stripes) *)
  let b64 = Bytes.make 64 'B' in
  let h64 = Latex_parse_lib.Xxh64.hash64_bytes b64 in
  check "64-byte hash non-zero" (h64 <> 0L);
  check "64-byte != 32-byte" (h64 <> h32);

  (* Test 8: seeded hash *)
  let h_seed1 = Latex_parse_lib.Xxh64.hash64_bytes ~seed:1L b in
  let h_seed2 = Latex_parse_lib.Xxh64.hash64_bytes ~seed:2L b in
  check "different seeds = different hashes" (h_seed1 <> h_seed2);

  (* Test 9: large input *)
  let big = Bytes.make 100_000 'Z' in
  let h_big = Latex_parse_lib.Xxh64.hash64_bytes big in
  check "large input produces hash" (h_big <> 0L);

  Printf.printf "[test_xxh64] done\n%!";
  if !fails > 0 then (
    Printf.eprintf "[test_xxh64] %d failures\n%!" !fails;
    exit 1)
