(** Chunk store — paragraph-level document splitting and incremental caching.

    Splits documents into chunks at paragraph boundaries, hashes each chunk with
    XXH64, and caches validator results per-chunk for incremental re-validation
    on edit (spec W111-120). *)

type chunk = { id : int64; start : int; length : int; content : string }
type snapshot = { chunks : chunk array }
type chunk_cache

val split_into_chunks : string -> chunk array
val create_snapshot : string -> snapshot
val diff_snapshots : snapshot -> snapshot -> int list
val create_cache : unit -> chunk_cache
val lookup_chunk : chunk_cache -> int64 -> Validators_common.result list option
val store_chunk : chunk_cache -> int64 -> Validators_common.result list -> unit
val invalidate_chunk : chunk_cache -> int64 -> unit
val cache_stats : chunk_cache -> string
