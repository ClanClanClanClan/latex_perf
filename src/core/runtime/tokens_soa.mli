(* Interface for off-heap Structure of Arrays token storage *)

open Bigarray

type tokens_soa = {
  kind   : (int32, int32_elt, c_layout) Array1.t;
  data   : (int32, int32_elt, c_layout) Array1.t;
  start_pos : (int32, int32_elt, c_layout) Array1.t;
  end_pos   : (int32, int32_elt, c_layout) Array1.t;
  line   : (int32, int32_elt, c_layout) Array1.t;
  col    : (int32, int32_elt, c_layout) Array1.t;
  mutable n : int;
  capacity : int;
}

type soa_stats = {
  total_tokens: int;
  capacity: int;
  memory_mb: float;
  utilization: float;
}

val make_tokens_soa : capacity:int -> tokens_soa
val clear_tokens_soa : tokens_soa -> unit
val push_token_soa : tokens_soa -> kind:int -> data:int -> start_pos:int -> end_pos:int -> line:int -> col:int -> bool
val get_token_soa : tokens_soa -> int -> (int * int * int * int * int * int) option
val unsafe_get_kind : tokens_soa -> int -> int
val unsafe_get_data : tokens_soa -> int -> int
val unsafe_get_line : tokens_soa -> int -> int
val unsafe_get_col : tokens_soa -> int -> int
val memory_usage_bytes : tokens_soa -> int
val get_stats : tokens_soa -> soa_stats