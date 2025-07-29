(** Core token ADT for LaTeX Perfectionist v25 *)

type catcode = 
  | Escape | BeginGroup | EndGroup | MathShift
  | AlignTab | EndLine | Param | Superscript
  | Subscript | Ignored | Space | Letter
  | Other | Active | Comment | Invalid

type t = {
  cat: catcode;
  text: string;
  loc: Location.t;
  hash: int;
}

val make : catcode -> string -> Location.t -> t
val pp : Format.formatter -> t -> unit