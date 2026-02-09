(** Pre-touch memory pages to force physical allocation and reduce latency
    spikes. *)

val pre_touch_bytes : bytes -> page:int -> unit
(** Touch every [page]-th byte of a [bytes] buffer. *)

val pre_touch_ba_1 :
  ('a, 'b, Bigarray.c_layout) Bigarray.Array1.t ->
  elem_bytes:int ->
  elems:int ->
  page:int ->
  unit
(** Touch elements of a Bigarray at page-stride intervals. *)
