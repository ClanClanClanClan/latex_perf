(** Process memory statistics via platform FFI. *)

val rss_mb : unit -> float
(** Current resident set size in megabytes. *)
