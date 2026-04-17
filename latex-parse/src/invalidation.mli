(** Invalidation engine: computes minimal chunk invalidation set.

    Combines syntactic diffing (hash-based) with semantic edge propagation to
    reduce unnecessary re-validation of unchanged, unaffected chunks. *)

val compute :
  old_snap:Chunk_store.snapshot -> new_snap:Chunk_store.snapshot -> int list
(** [compute ~old_snap ~new_snap] returns the minimal set of chunk indices that
    need re-validation. Includes syntactically changed chunks plus chunks
    transitively reachable via semantic dependency edges. *)
