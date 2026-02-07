let fnv_offset = 0xCBF29CE484222325L
let fnv_prime = 0x00000100000001B3L

let hash64_bytes (b : bytes) : int64 =
  let h = ref fnv_offset in
  for i = 0 to Bytes.length b - 1 do
    let x = Int64.of_int (Char.code (Bytes.unsafe_get b i)) in
    h := Int64.mul (Int64.logxor !h x) fnv_prime
  done;
  !h
