(** Tests for cache_key — result cache (spec W19). *)

let fails = ref 0

let check name cond =
  if not cond then (
    Printf.eprintf "FAIL: %s\n%!" name;
    incr fails)
  else Printf.printf "  ok  %s\n%!" name

let () =
  Printf.printf "[test_cache_key]\n%!";

  (* Test 1: compute_key produces consistent results *)
  let k1 =
    Latex_parse_lib.Cache_key.compute_key ~source:"hello" ~validator_count:10
      ~language:"en"
  in
  let k2 =
    Latex_parse_lib.Cache_key.compute_key ~source:"hello" ~validator_count:10
      ~language:"en"
  in
  check "same input = same key"
    (Latex_parse_lib.Cache_key.key_to_string k1
    = Latex_parse_lib.Cache_key.key_to_string k2);

  (* Test 2: different source = different key *)
  let k3 =
    Latex_parse_lib.Cache_key.compute_key ~source:"world" ~validator_count:10
      ~language:"en"
  in
  check "diff source = diff key"
    (Latex_parse_lib.Cache_key.key_to_string k1
    <> Latex_parse_lib.Cache_key.key_to_string k3);

  (* Test 3: store + lookup round-trip *)
  let c = Latex_parse_lib.Cache_key.create () in
  Latex_parse_lib.Cache_key.store c k1 [ "result1" ];
  let v = Latex_parse_lib.Cache_key.lookup c k1 in
  check "lookup after store" (v = Some [ "result1" ]);

  (* Test 4: lookup miss *)
  let v2 = Latex_parse_lib.Cache_key.lookup c k3 in
  check "lookup miss = None" (v2 = None);

  (* Test 5: invalidate *)
  Latex_parse_lib.Cache_key.invalidate c k1;
  let v3 = Latex_parse_lib.Cache_key.lookup c k1 in
  check "invalidate removes entry" (v3 = None);

  (* Test 6: clear *)
  Latex_parse_lib.Cache_key.store c k1 [ "a" ];
  Latex_parse_lib.Cache_key.store c k3 [ "b" ];
  Latex_parse_lib.Cache_key.clear c;
  check "clear: k1 gone" (Latex_parse_lib.Cache_key.lookup c k1 = None);
  check "clear: k3 gone" (Latex_parse_lib.Cache_key.lookup c k3 = None);

  (* Test 7: hit_rate *)
  let c2 = Latex_parse_lib.Cache_key.create () in
  check "empty hit_rate = 0" (Latex_parse_lib.Cache_key.hit_rate c2 = 0.0);
  Latex_parse_lib.Cache_key.store c2 k1 [ "x" ];
  ignore (Latex_parse_lib.Cache_key.lookup c2 k1);
  (* hit *)
  ignore (Latex_parse_lib.Cache_key.lookup c2 k3);
  (* miss *)
  let hr = Latex_parse_lib.Cache_key.hit_rate c2 in
  check "hit_rate > 0 after hit" (hr > 0.0);

  (* Test 8: empty source *)
  let k_empty =
    Latex_parse_lib.Cache_key.compute_key ~source:"" ~validator_count:0
      ~language:""
  in
  check "empty source produces key"
    (String.length (Latex_parse_lib.Cache_key.key_to_string k_empty) > 0);

  (* Test 9: overwrite *)
  let c3 = Latex_parse_lib.Cache_key.create () in
  Latex_parse_lib.Cache_key.store c3 k1 [ "old" ];
  Latex_parse_lib.Cache_key.store c3 k1 [ "new" ];
  check "overwrite stores new value"
    (Latex_parse_lib.Cache_key.lookup c3 k1 = Some [ "new" ]);

  (* Test 10: stats string *)
  let s = Latex_parse_lib.Cache_key.stats c3 in
  check "stats non-empty" (String.length s > 0);

  Printf.printf "[test_cache_key] done\n%!";
  if !fails > 0 then (
    Printf.eprintf "[test_cache_key] %d failures\n%!" !fails;
    exit 1)
