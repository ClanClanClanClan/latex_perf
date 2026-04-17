(** Error recovery: boundary detection and repair predicates. *)

type recovery_point = { position : int; kind : string }

val find_recovery_points : string -> int -> recovery_point list
(** [find_recovery_points source error_pos] returns recovery boundaries
    (paragraph breaks, environment boundaries, section commands) near the error,
    sorted by proximity. *)

val is_repaired :
  old_errors:(string * Parser_l2.loc) list ->
  new_errors:(string * Parser_l2.loc) list ->
  bool
(** Monotonic repair: [true] iff [new_errors] is a strict subset of [old_errors]
    (fewer errors = repaired). *)
