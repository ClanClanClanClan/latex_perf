(** Edit algebra for the CST-based rewrite engine (v26.2 PR B3).

    An edit is a triple (start_offset, end_offset, replacement) applied to the
    source string the CST was built from. Edits are composable but not
    commutative: applying two overlapping edits in different orders yields
    different results. [Cst_edit] detects overlaps at validation time so the
    rewrite engine can reject conflicting fix sets rather than silently
    corrupting the source.

    Invariants:
    - [start_offset <= end_offset] (non-negative length to replace).
    - [start_offset >= 0], [end_offset <= src_length] at apply time.
    - Applying [apply_all] to a pairwise-disjoint, ascending-sorted list of
      edits is commutative with respect to final output. *)

type t = private {
  start_offset : int;
  end_offset : int;
      (** Half-open: replaces bytes [[start_offset, end_offset))]. *)
  replacement : string;
}

val make : start_offset:int -> end_offset:int -> replacement:string -> t
(** Construct an edit. Raises [Invalid_argument] if
    [start_offset < 0 || end_offset < start_offset]. *)

val insert : at:int -> string -> t
(** [insert ~at s] inserts [s] at offset [at] (a zero-length edit). *)

val delete : start_offset:int -> end_offset:int -> t
(** [delete ~start_offset ~end_offset] removes the byte range, inserting nothing
    in its place. *)

val replace : start_offset:int -> end_offset:int -> string -> t
(** [replace ~start_offset ~end_offset s] replaces the byte range with [s]. *)

val span : t -> Stable_spans.t
(** The span the edit affects in the PRE-edit source. *)

val delta : t -> int
(** [delta e = String.length e.replacement - (e.end_offset - e.start_offset)].
    The net length change this edit introduces. *)

(** ── Conflict detection ──────────────────────────────────────────── *)

val conflicts : t -> t -> bool
(** Two edits [conflict] iff their spans overlap in the PRE-edit source (with
    one exception: two pure insertions at the same offset do NOT conflict; they
    are combined in the order they were supplied). *)

val validate_non_overlapping : t list -> (unit, t * t) result
(** Checks every pair in the list. Returns [Ok ()] if no two edits conflict, or
    [Error (a, b)] with the first conflicting pair. *)

(** ── Application ─────────────────────────────────────────────────── *)

val apply_single : string -> t -> string
(** [apply_single src e] returns [src] with [e] applied. Raises
    [Invalid_argument] if the edit range exceeds [src]. *)

val apply_all : string -> t list -> (string, [ `Overlap of t * t ]) result
(** [apply_all src edits] applies all edits in a single pass. Edits are sorted
    by [start_offset] (ascending) internally and validated for non-overlap
    before application. Returns [Error (`Overlap (a, b))] if any two edits
    conflict. *)

val apply_best_effort : string -> t list -> string * t list * t list
(** [apply_best_effort src edits] greedily applies as many edits as possible.
    Returns [(output, applied, skipped)]:

    - [output] is [src] with the [applied] edits applied in pre-edit
      coordinates, equivalent to [Ok x = apply_all src applied; x].
    - [applied] is the subset of [edits] that did not conflict with any
      earlier-accepted edit; first-occurrence-wins (input order is the
      conflict-resolution priority).
    - [skipped] is the complementary subset, in the order they were encountered.

    Pure insertions at the same offset are NOT conflicts (per {!conflicts}) and
    all of them land in [applied] in input order. v26.4 §1.1 enables this as the
    underlying primitive of the [--apply-fixes-best-effort] CLI mode. *)

val apply_with_priority :
  string -> (t -> int) -> t list -> string * t list * t list
(** [apply_with_priority src priority edits] sorts [edits] by descending
    [priority], then dispatches to [apply_best_effort]. Higher-priority edits
    dominate conflicting lower-priority ones. The returned [applied] list
    reflects the post-priority-sort order; [skipped] preserves the original
    input order of the rejected edits. *)

(** ── Shifting ────────────────────────────────────────────────────── *)

val shift_after : by:int -> at_or_after:int -> t -> t
(** Shifts [start_offset] and [end_offset] by [by] bytes if they are at-or-after
    [at_or_after]. Used by the rewrite engine to rebase edits when earlier edits
    grew or shrank the source. *)

val equal : t -> t -> bool
(** Structural equality on edits. *)

val compare : t -> t -> int
(** Lexicographic by [start_offset], then [end_offset], then [replacement]. *)

val to_string : t -> string
(** Debug-oriented rendering of the edit. *)
