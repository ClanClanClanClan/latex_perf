(** Double-buffered token arenas backed by Bigarrays.

    Provides zero-copy, GC-free storage for SIMD tokeniser output. The
    double-buffer design allows the previous result to remain readable while the
    current request writes into the alternate buffer. *)

open Bigarray

type kinds_t = (int32, int32_elt, c_layout) Array1.t
type offs_t = (int32, int32_elt, c_layout) Array1.t
type codes_t = (int32, int32_elt, c_layout) Array1.t
type issues_t = (int32, int32_elt, c_layout) Array1.t

type buffers = {
  kinds : kinds_t;
  offs : offs_t;
  codes : codes_t;
  issues : issues_t;
  lines : offs_t;
  cols : offs_t;
  mutable next_ix : int;
}

type t
(** Opaque double-buffered arena. *)

val create : cap:int -> t
(** [create ~cap] allocates two buffer sets, each with room for [cap] tokens. *)

val swap : t -> unit
(** Switch to the alternate buffer and reset its write index. *)

val current : t -> buffers
(** Return the currently active buffer set. *)
