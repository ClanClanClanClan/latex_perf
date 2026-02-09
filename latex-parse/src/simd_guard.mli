(** SIMD availability detection and fail-fast requirement checks. *)

val available : unit -> bool
(** [true] if the current CPU supports the required SIMD instruction set. *)

val require : unit -> unit
(** Abort the process immediately if SIMD is unavailable. *)
