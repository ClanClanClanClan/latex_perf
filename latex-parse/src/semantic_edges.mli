(** Semantic edges: typed dependency edges between chunks.

    Extracts label->ref and macro def->use relationships per chunk, enabling
    dependency-aware invalidation instead of whole-source fallback. *)

type edge_kind =
  | LabelRef of string  (** Label key: defining chunk -> referencing chunk. *)
  | MacroDef of string  (** Macro name: defining chunk -> using chunk. *)

type edge = { kind : edge_kind; source_chunk : int; target_chunk : int }

val extract_edges : Chunk_store.chunk array -> edge list
(** Extract all semantic edges from a chunk array. Labels, refs, and macro
    definitions are located per-chunk, then cross-chunk edges are generated. *)
