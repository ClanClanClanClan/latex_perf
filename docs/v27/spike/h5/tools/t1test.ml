(* spike H.5 stage 1: the O(1) conversion realizers against the extracted Coq definitions,
   on every boundary value +-0..64 around +-2^k (k = 0..70) and 10^6 random values *)
let n = ref 0 and bad = ref 0
let chk_u i = incr n; if not (Zr.eq (Uint0.to_Z i) (Uint0.to_Z_coq i)) then incr bad;
  incr n; if not (Zr.eq (Sint0.to_Z i) (Sint0.to_Z_coq i)) then incr bad
let chk_z z = incr n; if not (Uint63.equal (Uint0.of_Z z) (Uint0.of_Z_coq z)) then incr bad
let () =
  for k = 0 to 70 do
    for d = -64 to 64 do
      Stdlib.List.iter (fun s -> chk_z Z.(s * (shift_left one k) + of_int d)) [Z.one; Z.minus_one]
    done
  done;
  for d = -1000 to 1000 do chk_u (Uint63.of_int d); chk_u (Uint63.of_int (max_int - d)); chk_u (Uint63.of_int (min_int + d)) done;
  for k = 0 to 62 do for d = -3 to 3 do chk_u (Uint63.of_int ((1 lsl k) + d)); chk_u (Uint63.of_int (- (1 lsl k) + d)) done done;
  Random.init 20261005;
  for _ = 1 to 1_000_000 do
    chk_u (Uint63.of_int (Random.bits () lor (Random.bits () lsl 30) lor (Random.bits () lsl 60)));
    chk_z Z.(shift_left (of_int (Random.bits ())) (Random.int 100) - of_int (Random.bits ()))
  done;
  Printf.printf "t1test: %d comparisons, %d mismatches\n" !n !bad;
  exit (if !bad = 0 then 0 else 1)
