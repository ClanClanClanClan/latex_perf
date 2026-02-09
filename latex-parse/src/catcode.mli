(** ASCII category-code classifier aligned with the v25_R1 mapping. *)

val cc_escape : int
val cc_beginGrp : int
val cc_endGrp : int
val cc_math : int
val cc_alignTab : int
val cc_newline : int
val cc_param : int
val cc_superscr : int
val cc_subscr : int
val cc_ignored : int
val cc_space : int
val cc_letter : int
val cc_other : int
val cc_active : int
val cc_comment : int
val cc_invalid : int

val is_letter : int -> bool
(** [is_letter b] is [true] when [b] is an ASCII letter (A-Z, a-z). *)

val classify_ascii : int -> int
(** Map a byte value to its TeX category code. *)
