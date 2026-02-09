(** Monotonic clock access via C FFI. *)

val now : unit -> int64
(** Current monotonic time in nanoseconds. *)

val ns_of_ms : int -> int64
(** Convert milliseconds to nanoseconds. *)

val ms_of_ns : int64 -> float
(** Convert nanoseconds to milliseconds (float). *)
