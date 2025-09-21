(* Bit-exact scalar XXH64 (seeded, default seed 0). *)

let prime1 = 0x9E3779B185EBCA87L  (* 11400714785074694791 *)
let prime2 = 0xC2B2AE3D27D4EB4FL  (* 14029467366897019727 *)
let prime3 = 0x165667B19E3779F9L  (*  1609587929392839161 *)
let prime4 = 0x85EBCA77C2B2AE63L  (*  9650029242287828579 *)
let prime5 = 0x27D4EB2F165667C5L  (*  2870177450012600261 *)

let rotl64 x r =
  Int64.(logor (shift_left x r) (shift_right_logical x (64 - r)))

let get32_le (b:bytes) off =
  let open Int64 in
  let c i = of_int (Char.code (Bytes.unsafe_get b (off + i))) in
  logor (c 0)
    (logor (shift_left (c 1) 8)
      (logor (shift_left (c 2) 16)
        (shift_left (c 3) 24)))

let get64_le (b:bytes) off =
  let open Int64 in
  let c i = of_int (Char.code (Bytes.unsafe_get b (off + i))) in
  logor (c 0)
    (logor (shift_left (c 1) 8)
      (logor (shift_left (c 2) 16)
        (logor (shift_left (c 3) 24)
          (logor (shift_left (c 4) 32)
            (logor (shift_left (c 5) 40)
              (logor (shift_left (c 6) 48)
                (shift_left (c 7) 56)))))))

let round acc input =
  let open Int64 in
  let acc = add acc (mul input prime2) in
  let acc = rotl64 acc 31 in
  mul acc prime1

let merge_round acc v =
  let open Int64 in
  let acc = logxor acc (round 0L v) in
  add (mul acc prime1) prime4

let avalanche h =
  let open Int64 in
  let h = logxor h (shift_right_logical h 33) in
  let h = mul h prime2 in
  let h = logxor h (shift_right_logical h 29) in
  let h = mul h prime3 in
  logxor h (shift_right_logical h 32)

let hash64_bytes ?(seed=0L) (b:bytes) : int64 =
  let len = Bytes.length b in
  let (h0, start) =
    if len >= 32 then begin
      let v1 = ref (Int64.add seed (Int64.add prime1 prime2)) in
      let v2 = ref (Int64.add seed prime2) in
      let v3 = ref seed in
      let v4 = ref (Int64.sub seed prime1) in
      let i = ref 0 in
      while !i <= len - 32 do
        v1 := round !v1 (get64_le b !i);
        v2 := round !v2 (get64_le b (!i + 8));
        v3 := round !v3 (get64_le b (!i + 16));
        v4 := round !v4 (get64_le b (!i + 24));
        i := !i + 32
      done;
      let h = Int64.(logxor (logxor (logxor (rotl64 !v1 1) (rotl64 !v2 7)) (rotl64 !v3 12)) (rotl64 !v4 18)) in
      let h = merge_round h !v1 in
      let h = merge_round h !v2 in
      let h = merge_round h !v3 in
      let h = merge_round h !v4 in
      (h, !i)
    end else (Int64.add seed prime5, 0)
  in
  let h = Int64.add h0 (Int64.of_int len) in
  let i = ref start in
  (* 8-byte chunks *)
  let h = ref h in
  while !i <= len - 8 do
    let k1 = get64_le b !i in
    let k1 = Int64.mul (rotl64 (Int64.mul k1 prime2) 31) prime1 in
    h := Int64.logxor !h k1;
    h := Int64.add (Int64.mul (rotl64 !h 27) prime1) prime4;
    i := !i + 8
  done;
  (* 4-byte chunk *)
  if !i <= len - 4 then begin
    let k1 = get32_le b !i in
    h := Int64.logxor !h (Int64.mul k1 prime1);
    h := Int64.add (Int64.mul (rotl64 !h 23) prime2) prime3;
    i := !i + 4
  end;
  (* remain bytes *)
  while !i < len do
    let k1 = Int64.of_int (Char.code (Bytes.unsafe_get b !i)) in
    h := Int64.logxor !h (Int64.mul k1 prime5);
    h := Int64.mul (rotl64 !h 11) prime1;
    i := !i + 1
  done;
  avalanche !h

external xxh64_simd : bytes -> int64 -> int64 = "ocaml_xxh64_simd"

let hash64_bytes_simd ?(seed=0L) b = xxh64_simd b seed

let hash64 ?seed b =
  match Sys.getenv_opt "L0_USE_SIMD_XXH" with
  | Some "1" -> (try hash64_bytes_simd ?seed b with _ -> hash64_bytes ?seed b)
  | _ -> hash64_bytes ?seed b
