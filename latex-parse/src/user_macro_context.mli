(** Thread-local user macro registry context.

    Set once per validation run so that validators and the expansion pipeline
    can access the parsed user macro registry without re-parsing. *)

val set : User_macro_registry.registry -> unit
val get : unit -> User_macro_registry.registry option
val clear : unit -> unit
