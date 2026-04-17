(** Thread-local partial document state. *)

val set : Partial_cst.partial_document -> unit
val get : unit -> Partial_cst.partial_document option
val clear : unit -> unit
