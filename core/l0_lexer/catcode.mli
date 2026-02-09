(** TeX category codes — wraps the Coq-verified {!Data.Types.Catcode} type and
    adds integer/char conversion helpers. *)

(** {1 Re-exported from Data.Types.Catcode} *)

type catcode =
  | Escape
  | BeginGrp
  | EndGrp
  | Math
  | AlignTab
  | Newline
  | Param
  | Superscr
  | Subscr
  | Ignored
  | Space
  | Letter
  | Other
  | Active
  | Comment
  | Invalid

val catcode_to_string : catcode -> string
val catcode_to_int : catcode -> int

(** {1 Conversion helpers} *)

val of_int_opt : int -> catcode option
(** [of_int_opt n] returns [Some cat] for [n] in [0..15], [None] otherwise. *)

val of_ascii_code : int -> catcode
(** [of_ascii_code n] returns the catcode for integer [n], defaulting to
    {!Other} for out-of-range values. *)

val classify_char : char -> catcode
(** [classify_char ch] returns the catcode for the character [ch]. *)
