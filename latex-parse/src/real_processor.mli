(** High-performance SIMD tokeniser integration. *)

val run : bytes -> Arena.buffers -> int * int * int
(** [run input out] tokenises [input] into the pre-allocated [out] buffers.
    Returns [(status, n_tokens, issues_len)] where [status = 0] indicates
    success. *)
