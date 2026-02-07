external now_ns : unit -> int64 = "ocaml_clock_monotonic_ns"

let now () = now_ns ()
let ns_of_ms ms = Int64.mul 1_000_000L (Int64.of_int ms)
let ms_of_ns ns = Int64.to_float ns /. 1.0e6
