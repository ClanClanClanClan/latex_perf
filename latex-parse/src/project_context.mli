(** Thread-local project state context. *)

val set : Project_state.project_state -> unit
val get : unit -> Project_state.project_state option
val clear : unit -> unit
