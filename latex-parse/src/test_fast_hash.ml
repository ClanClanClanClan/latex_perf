(** Unit tests for Fast_hash (FNV-1a 64-bit). *)

open Latex_parse_lib

let fails = ref 0
let cases = ref 0

let expect cond msg =
  if not cond then (
    Printf.eprintf "[fast-hash] FAIL: %s\n%!" msg;
    incr fails)

let run msg f =
  incr cases;
  f msg

let () =
  (* 1. Constants are well-known FNV-1a values *)
  run "fnv_offset" (fun tag ->
      expect (Fast_hash.fnv_offset = 0xCBF29CE484222325L) tag);

  run "fnv_prime" (fun tag ->
      expect (Fast_hash.fnv_prime = 0x00000100000001B3L) tag);

  (* 2. Empty bytes hashes to fnv_offset *)
  run "empty = offset" (fun tag ->
      let h = Fast_hash.hash64_bytes Bytes.empty in
      expect (h = Fast_hash.fnv_offset) (tag ^ Printf.sprintf ": got %Ld" h));

  (* 3. Deterministic: same input → same output *)
  run "deterministic" (fun tag ->
      let b = Bytes.of_string "hello" in
      let h1 = Fast_hash.hash64_bytes b in
      let h2 = Fast_hash.hash64_bytes b in
      expect (h1 = h2) tag);

  (* 4. Different inputs → different hashes *)
  run "different inputs" (fun tag ->
      let h1 = Fast_hash.hash64_bytes (Bytes.of_string "hello") in
      let h2 = Fast_hash.hash64_bytes (Bytes.of_string "world") in
      expect (h1 <> h2) tag);

  (* 5. Single byte changes hash *)
  run "single byte" (fun tag ->
      let h = Fast_hash.hash64_bytes (Bytes.of_string "a") in
      expect (h <> Fast_hash.fnv_offset) tag);

  (* 6. hash64_sub full range = hash64_bytes *)
  run "sub full = bytes" (fun tag ->
      let b = Bytes.of_string "test data here" in
      let h1 = Fast_hash.hash64_bytes b in
      let h2 = Fast_hash.hash64_sub b 0 (Bytes.length b) in
      expect (h1 = h2) tag);

  (* 7. hash64_sub with offset *)
  run "sub offset" (fun tag ->
      let b = Bytes.of_string "XXXhello" in
      let sub_h = Fast_hash.hash64_sub b 3 5 in
      let direct_h = Fast_hash.hash64_bytes (Bytes.of_string "hello") in
      expect (sub_h = direct_h) tag);

  (* 8. hash64_sub zero length = offset *)
  run "sub zero len" (fun tag ->
      let b = Bytes.of_string "anything" in
      let h = Fast_hash.hash64_sub b 3 0 in
      expect (h = Fast_hash.fnv_offset) tag);

  (* 9. Bit-flip sensitivity *)
  run "bit flip" (fun tag ->
      let b1 = Bytes.of_string "AAAA" in
      let b2 = Bytes.of_string "BAAA" in
      let h1 = Fast_hash.hash64_bytes b1 in
      let h2 = Fast_hash.hash64_bytes b2 in
      expect (h1 <> h2) tag);

  (* 10. Large input does not crash *)
  run "large input" (fun tag ->
      let b = Bytes.make 100_000 'x' in
      let h = Fast_hash.hash64_bytes b in
      expect (h <> 0L) tag);

  if !fails > 0 then (
    Printf.eprintf "[fast-hash] %d failure(s)\n%!" !fails;
    exit 1)
  else Printf.printf "[fast-hash] PASS %d cases\n%!" !cases
