external ht_create  : unit -> Unix.file_descr = "ocaml_ht_create"
external ht_arm_ns  : Unix.file_descr -> int64 -> unit = "ocaml_ht_arm_ns"
external ht_wait2   : Unix.file_descr -> int -> int -> (int * int) = "ocaml_ht_wait2"

type t = { k: Unix.file_descr }
let create () = { k = ht_create () }
let arm t ~ns = ht_arm_ns t.k ns
let wait_two t ~fd1 ~fd2 =
  let (tf, which) = ht_wait2 t.k fd1 fd2 in
  (tf, which)