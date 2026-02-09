(** GC tuning utilities for major-heap drainage and allocation-budget
    management. *)

val words_total : unit -> float
(** Total allocated words (minor + major). *)

val drain_major : ?slice:int -> unit -> unit
(** Drain the major heap by calling [Gc.major_slice] in a loop. *)

val prepay : unit -> unit
(** Trigger a full major cycle if accumulated allocations exceed the configured
    budget. *)

val init_gc : unit -> unit
(** Set GC parameters from {!Config} and perform an initial drain. *)
