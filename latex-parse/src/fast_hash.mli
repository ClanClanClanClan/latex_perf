(** FNV-1a 64-bit hash function. *)

val fnv_offset : int64
val fnv_prime : int64

val hash64_bytes : bytes -> int64
(** Hash a byte sequence with FNV-1a 64-bit. *)

val hash64_sub : bytes -> int -> int -> int64
(** [hash64_sub b off len] hashes the sub-range [b.[off .. off+len-1]]. *)
