(** Cross-layer consistency & synchronisation protocol (spec §5). *)

type layer_id = L0 | L1 | L2 | L3 | L4
type version_vector = { gen : int; parent_gen : int }
type 'a layer_state = { layer : layer_id; version : version_vector; data : 'a }
type 'a snapshot = { generation : int; states : 'a layer_state list }
type rollback_result = Rolled_back | No_rollback_needed

val initial_version : version_vector
val mk_version : gen:int -> parent_gen:int -> version_vector
val next_gen : unit -> int
val current_gen : unit -> int
val accepts_delta : version_vector -> version_vector -> bool
val advance : version_vector -> version_vector
val create_snapshot : 'a layer_state list -> 'a snapshot
val layer_of_snapshot : 'a snapshot -> layer_id -> 'a layer_state option
val rollback_child : 'a snapshot -> layer_id -> 'a snapshot * rollback_result
val is_consistent : 'a snapshot -> bool
