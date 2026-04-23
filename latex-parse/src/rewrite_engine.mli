(** CST-based rewrite engine v1 (v26.2 PR B3).

    Given a source string, a list of edits, and the invariants of [Cst_edit],
    applies the edit set atomically and returns both the rewritten source and
    the re-parsed CST.

    The engine is intentionally minimal in v26.2:
    - Edit validation is byte-range conflict detection (delegated to
      [Cst_edit.validate_non_overlapping]).
    - Edit application is a single linear pass.
    - Re-parse of the rewritten source is via [Cst_of_ast.of_source]; callers
      who only need the raw rewritten string can skip [apply_and_reparse] and
      use [Cst_edit.apply_all] directly. *)

type conflict = [ `Overlap of Cst_edit.t * Cst_edit.t ]
(** Reason a rewrite was rejected. *)

val apply : source:string -> edits:Cst_edit.t list -> (string, conflict) result
(** [apply ~source ~edits] returns the rewritten source or a conflict error.
    Wraps [Cst_edit.apply_all]. *)

val apply_and_reparse :
  source:string ->
  edits:Cst_edit.t list ->
  (string * Cst.t list, conflict) result
(** [apply_and_reparse ~source ~edits] returns both the rewritten source and its
    CST. Convenience wrapper for the common "rewrite then visualize" flow. *)
