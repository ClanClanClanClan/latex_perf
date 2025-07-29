(** Source location tracking for LaTeX Perfectionist v25 *)

type t = {
  byte_start : int;
  byte_end : int;
  line : int;
  column : int;
}

val make : byte_start:int -> byte_end:int -> line:int -> column:int -> t
val pp : Format.formatter -> t -> unit