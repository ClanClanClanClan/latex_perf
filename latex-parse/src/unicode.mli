(** UTF-8 detection utilities for typographic characters. *)

val has_curly_quote : string -> bool
(** [true] if the string contains any Unicode curly quote (U+2018..U+201D). *)

val has_en_dash : string -> bool
(** [true] if the string contains U+2013 EN DASH. *)

val has_em_dash : string -> bool
(** [true] if the string contains U+2014 EM DASH. *)

val has_ellipsis_char : string -> bool
(** [true] if the string contains U+2026 HORIZONTAL ELLIPSIS. *)

val count_utf8_seq : string -> int -> int -> int -> int
(** [count_utf8_seq s a b c] counts occurrences of the 3-byte UTF-8 sequence
    [(a, b, c)] in [s]. *)

val count_en_dash : string -> int
val count_em_dash : string -> int
