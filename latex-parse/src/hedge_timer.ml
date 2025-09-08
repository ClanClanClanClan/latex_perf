external ht_create  : unit -> Unix.file_descr = "ocaml_ht_create"
external ht_arm_ns  : Unix.file_descr -> int64 -> unit = "ocaml_ht_arm_ns"
external ht_wait2   : Unix.file_descr -> int -> int -> (int * int) = "ocaml_ht_wait2"

type t = { k: Unix.file_descr }
let create () = { k = ht_create () }
let arm t ~ns = ht_arm_ns t.k ns
(* returns (timer_fired, ready_fd or -1) *)
let wait_two (t : t) ~(fd1 : Unix.file_descr) ~(fd2 : Unix.file_descr) : (int * int) =
  ht_wait2 t.k (Obj.magic fd1 : int) (Obj.magic fd2 : int)