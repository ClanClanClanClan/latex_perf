(** Byte-range spans with shift-on-edit semantics (v26.2 PR B1).

    Extends [Node_id] with span-aware operations. A [t] is a half-open
    byte range [\[start; end\_\))] into a source string; edits that
    shift the range are applied via [shift_after]. See ADR-005. *)

type t = private { start_offset : int; end_offset : int }
(** Invariant: [0 <= start_offset <= end_offset]. *)

val make : start_offset:int -> end_offset:int -> t
(** [make ~start_offset ~end_offset] builds a span. Raises
    [Invalid_argument] if [start_offset > end_offset] or either is
    negative. *)

val zero : int -> t
(** [zero offset] is the zero-length span at [offset]. *)

val length : t -> int
(** [length s = s.end_offset - s.start_offset]. *)

val is_empty : t -> bool
(** [is_empty s] iff [length s = 0]. *)

val contains : t -> int -> bool
(** [contains s p] iff [start_offset <= p < end_offset]. *)

val disjoint : t -> t -> bool
(** [disjoint s1 s2] iff the spans do not overlap. *)

val substring : string -> t -> string
(** [substring src s] returns the bytes of [src] covered by [s]. Raises
    [Invalid_argument] if the span exceeds the source bounds. *)

(** ── Edit model ────────────────────────────────────────────────── *)

type edit = {
  edit_offset : int;  (** Start of the edited range in the pre-edit source. *)
  edit_old_length : int;  (** Length removed. *)
  edit_new_length : int;  (** Length inserted. *)
}

val shift_after : edit -> t -> t
(** Applies the edit's shift to [t]. If the span starts strictly after
    [edit_offset + edit_old_length], both endpoints shift by
    [edit_new_length - edit_old_length]. If the span ends at or before
    [edit_offset], it is unchanged. If the span overlaps the edit
    range, it is considered [damaged] — callers should check
    [damaged_by] before shifting. *)

val damaged_by : edit -> t -> bool
(** [damaged_by e s] iff the edit range overlaps [s]. *)

val of_located : Parser_l2.located_node -> t
(** Builds a span from a parser [located_node] using its
    [loc.offset] + [loc.end_offset]. *)

val equal : t -> t -> bool
(** Structural equality on spans. *)

val compare : t -> t -> int
(** Lexicographic by [start_offset] then [end_offset]. *)

val to_string : t -> string
(** Debug-oriented rendering [\[start, end_\))]. *)
