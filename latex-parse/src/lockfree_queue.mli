(** Lock-free MPMC bounded ring buffer queue using OCaml 5.x Atomic (spec W63).
    Target: 8M events/sec on 4 cores. *)

type 'a t

val create : int -> 'a t
(** [create capacity] creates a queue with given capacity (rounded up to power
    of 2). *)

val capacity : 'a t -> int
(** The actual capacity (power of 2). *)

val try_push : 'a t -> 'a -> bool
(** Non-blocking enqueue. Returns [false] if full. *)

val try_pop : 'a t -> 'a option
(** Non-blocking dequeue. Returns [None] if empty. *)

val push : 'a t -> 'a -> unit
(** Blocking enqueue (spins until slot available). *)

val pop : 'a t -> 'a
(** Blocking dequeue (spins until data available). *)

val length : 'a t -> int
(** Approximate count of items (may race). *)

val is_empty : 'a t -> bool
(** Approximate emptiness check. *)
