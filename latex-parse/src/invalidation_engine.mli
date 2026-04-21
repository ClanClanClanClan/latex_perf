(** Invalidation engine alias (memo §16.2).

    Re-exports {!Invalidation} under the memo-prescribed name. Functionally
    identical to [Invalidation]; the alias exists so downstream references to
    the memo path resolve. *)

val compute :
  old_snap:Chunk_store.snapshot -> new_snap:Chunk_store.snapshot -> int list
(** Alias for {!Invalidation.compute}. *)
