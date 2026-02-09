(** XXH64 hash with optional SIMD acceleration.

    Provides a bit-exact scalar implementation and an FFI-backed SIMD path
    selectable at runtime via [L0_USE_SIMD_XXH=1]. *)

val hash64 : ?seed:int64 -> bytes -> int64
(** Preferred entry point. Uses SIMD when [L0_USE_SIMD_XXH=1], falls back to
    scalar on error or when unset. *)

val hash64_bytes : ?seed:int64 -> bytes -> int64
(** Pure-OCaml scalar XXH64. *)

val hash64_bytes_simd : ?seed:int64 -> bytes -> int64
(** FFI-backed SIMD XXH64. *)
