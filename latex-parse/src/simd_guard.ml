external simd_available : unit -> int = "ocaml_simd_available"
external require_simd : unit -> unit = "ocaml_require_simd"

let available () = simd_available () <> 0
let require () = require_simd ()

(* Call Simd_guard.require () early in main_service to fail-fast *)
