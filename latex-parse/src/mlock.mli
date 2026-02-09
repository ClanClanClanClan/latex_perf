(** Lock process memory pages to prevent swapping.

    Respects [L0_NO_MLOCK=1] to skip locking in CI or constrained environments. *)

val init : unit -> unit
(** Call [mlockall] unless [L0_NO_MLOCK=1] is set. Silently ignores errors. *)
