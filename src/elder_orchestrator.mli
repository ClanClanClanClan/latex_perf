(** Incremental orchestrator public API (stub). *)

type session

val open_doc  : uri:string -> bytes -> session
val apply_patch :
  session ->
  start:int -> finish:int -> replacement:string -> Token.t array
val close_doc : session -> unit