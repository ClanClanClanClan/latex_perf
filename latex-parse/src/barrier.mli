(** Simple one-shot thread synchronisation barrier. *)

type t = { mutex : Mutex.t; cond : Condition.t; ready : bool ref }

val create : unit -> t
(** Create a new barrier in the unready state. *)

val release : t -> unit
(** Signal the barrier, waking all waiters. *)

val wait : t -> unit
(** Block until the barrier is released. *)
