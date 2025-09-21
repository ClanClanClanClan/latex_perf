open Latex_parse_lib

let gen_bytes n =
  let b = Bytes.create n in
  for i=0 to n-1 do Bytes.set b i (Char.chr (Random.int 256)) done; b

let () =
  Random.self_init ();
  let iters = try int_of_string Sys.argv.(1) with _ -> 1000 in
  let sz = try int_of_string Sys.argv.(2) with _ -> 1024 in
  let mism = ref 0 in
  for _=1 to iters do
    let b = gen_bytes sz in
    let a = Xxh64.hash64_bytes b in
    let s =
      try Xxh64.hash64_bytes_simd b with _ -> a
    in
    if a <> s then incr mism
  done;
  Printf.printf "[xxh-selfcheck] iters=%d size=%d mismatches=%d\n%!" iters sz !mism;
  if !mism > 0 then exit 1 else exit 0

