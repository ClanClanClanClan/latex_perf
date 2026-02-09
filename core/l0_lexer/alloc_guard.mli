(** Hot-path allocation guard for detecting unexpected GC pressure. *)

val enabled : bool ref
(** When [true], {!with_no_alloc} checks for allocations. Default [false]. *)

val words : unit -> float
(** Current total allocated words (minor + major - promoted). *)

val with_no_alloc : (unit -> 'a) -> 'a
(** [with_no_alloc f] runs [f ()]. When {!enabled} is [true], logs a warning to
    stderr if [f] allocates more than 1.0 words. *)
