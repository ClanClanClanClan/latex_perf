(* Scalar 64-bit FNV-1a placeholder (future Week-9 SIMD xxHash lane).
   Provides a stable 64-bit hash and a throughput target for benchmarking. *)

let fnv_offset = 0xCBF29CE484222325L  (* 1469598103934665605 *)
let fnv_prime  = 0x00000100000001B3L  (* 1099511628211 *)

let hash64_bytes (b:bytes) : int64 =
  let h = ref fnv_offset in
  for i = 0 to Bytes.length b - 1 do
    let x = Int64.of_int (Char.code (Bytes.unsafe_get b i)) in
    h := Int64.mul (Int64.logxor !h x) fnv_prime
  done; !h

let hash64_sub (b:bytes) off len : int64 =
  let h = ref fnv_offset in
  let stop = off + len in
  for i = off to stop - 1 do
    let x = Int64.of_int (Char.code (Bytes.unsafe_get b i)) in
    h := Int64.mul (Int64.logxor !h x) fnv_prime
  done; !h

