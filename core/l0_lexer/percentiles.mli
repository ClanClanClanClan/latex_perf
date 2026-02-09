(** Percentile computation and tail-latency tracking. *)

val exact : float array -> float -> float
(** [exact arr q] returns the [q]-th percentile of [arr] (0.0--1.0). The array
    is copied and sorted internally. *)

type tail_trace = (float * string) list
(** Association list of [(latency_ms, metadata)] entries. *)

val keep_slowest : int -> tail_trace -> tail_trace
(** [keep_slowest n xs] retains the [n] entries with the largest latency. *)
