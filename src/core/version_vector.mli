(* Version Vector - Version tracking and compatibility interface *)

type t

val current : t
(** Current version of LaTeX Perfectionist *)

val create : major:int -> minor:int -> patch:int -> ?revision:string -> unit -> t
(** Create a new version *)

val to_string : t -> string
(** Convert version to string representation (e.g., "v25.0.0-R0") *)

val compare : t -> t -> int
(** Compare two versions *)

val is_compatible : required:t -> actual:t -> bool
(** Check if actual version is compatible with required version *)

val parse : string -> t option
(** Parse version string into version type *)