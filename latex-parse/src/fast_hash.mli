(** FNV-1a 64-bit hash function. *)

val fnv_offset : int64
val fnv_prime : int64

val hash64_bytes : bytes -> int64
(** Hash a byte sequence with FNV-1a 64-bit. *)
