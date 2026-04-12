(** Thread-safe regex operations compatible with Str's API.

    Drop-in replacement for the subset of [Str] used by the validator pipeline.
    Backed by the [Re] library — no global mutable state. All match results are
    returned as values, not stored globally. *)

type regexp
(** Compiled regex. *)

type match_result
(** Opaque result from a successful search. *)

val regexp : string -> regexp
(** Compile a Str-syntax regex pattern. Translates Str escapes ([\(], [\|],
    [\?], [\+]) to PCRE before compilation. *)

val regexp_string : string -> regexp
(** Match a literal string (no regex metacharacters). *)

val quote : string -> string
(** Escape regex metacharacters in a string. *)

val search_forward : regexp -> string -> int -> match_result * int
(** [search_forward re s pos] searches for [re] in [s] starting at [pos].
    Returns [(match_result, match_start_pos)].
    @raise Not_found if no match. *)

val matched_group : match_result -> int -> string -> string
(** [matched_group mr n s] returns the [n]-th captured group.
    @raise Not_found if group [n] did not participate. *)

val matched_string : match_result -> string -> string
(** [matched_string mr s] returns the full matched substring. *)

val match_end : match_result -> int
(** Byte position after the last matched character. *)

val match_beginning : match_result -> int
(** Byte position of the first matched character. *)

val split : regexp -> string -> string list
(** Split a string on regex matches. *)
