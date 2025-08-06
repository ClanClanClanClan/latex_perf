(** Byte‑offset based locations; line/column only for UI. *)

type t = { byte_start : int; byte_end : int }  (** invariant: 0 <= start < end *)

val length : t -> int
val merge  : t -> t -> t option
val pp     : Format.formatter -> t -> unit

(** Additional utility functions for DSL integration *)
val make : int -> int -> t
val make_single : int -> t
val make_span : int -> int -> t