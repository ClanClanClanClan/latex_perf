(** Dependency graph: chunk-level dependency tracking with transitive
    propagation. *)

type t
(** Abstract graph: adjacency list from chunk index to dependent chunk indices. *)

val build : Semantic_edges.edge list -> int -> t
(** [build edges chunk_count] constructs the dependency graph. *)

val affected_set : t -> int list -> int list
(** [affected_set graph dirty_chunks] returns all chunks transitively reachable
    from dirty chunks via dependency edges. Sorted, deduplicated. *)
