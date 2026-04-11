(** L3 semantic reducer — label/ref tracking and consistency (spec W53-57). *)

type label_entry = { key : string; position : int; prefix : string }
type ref_entry = { key : string; position : int; command : string }

type semantic_state = {
  labels : label_entry list;
  refs : ref_entry list;
  duplicate_labels : string list;
  undefined_refs : string list;
  forward_refs : string list;
}

val extract_labels : string -> label_entry list
val extract_refs : string -> ref_entry list
val analyze : string -> semantic_state

val build_state : string -> semantic_state
(** Alias for {!analyze}. Matches spec B-5 interface name. *)

val set_state : semantic_state -> unit
val get_state : unit -> semantic_state option
val clear_state : unit -> unit
