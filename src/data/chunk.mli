(* Chunk Module Interface - Week 3-6 Foundation *)
(* LaTeX Perfectionist v25 - PLANNER.yaml Section 3.1.1 *)

(** Chunk type for incremental processing 
    
    As specified in Section 3.1.1:
    - Chunked input enables O(Δ) re-lexing after edits
    - prev_hash closes integrity proofs *)
type t = {
  id       : int;        (* monotonic identifier *)
  bytes    : bytes;      (* raw UTF-8 content *)
  start_ofs: int;        (* global offset in document *)
  prev_hash: int64;      (* xxHash64 for chain integrity *)
}

(** Create a chunk with all fields specified *)
val create : id:int -> bytes:bytes -> start_ofs:int -> prev_hash:int64 -> t

(** Create the initial chunk (id=0, offset=0, hash=0) *)
val create_initial : bytes -> t

(** Get size of chunk in bytes *)
val size : t -> int

(** Get chunk content as string *)
val to_string : t -> string

(** Split a string into chunks of given size (default 4096 bytes = 4KB per spec) *)
val split_into_chunks : ?chunk_size:int -> string -> t list

(** Check if a document offset falls within this chunk *)
val contains_offset : t -> int -> bool

(** Get character at document offset if it's within this chunk *)
val get_char_at : t -> int -> char option

(** Find the chunk containing the given offset *)
val find_chunk_boundary : t list -> int -> t option

(** Pretty printer for debugging *)
val pp : Format.formatter -> t -> unit