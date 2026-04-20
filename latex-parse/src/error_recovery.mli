(** Error recovery: boundary detection and repair predicates. *)

type recovery_point = { position : int; kind : string }

val find_recovery_points : string -> int -> recovery_point list
(** [find_recovery_points source error_pos] returns recovery boundaries
    (paragraph breaks, environment boundaries, section commands) near the error,
    sorted by proximity. *)

val is_repaired :
  old_errors:(string * Parser_l2.loc) list ->
  new_errors:(string * Parser_l2.loc) list ->
  bool
(** Monotonic repair: [true] iff [new_errors] is a strict subset of [old_errors]
    (fewer errors = repaired). *)

type dependency_boundary = { region : int * int; reason : string }
(** PR #239 (memo §6, E2): dependency boundaries bound the monotonic-repair
    guarantee. A repair that crosses a dep-boundary may invalidate
    previously-trusted zones; only repairs that stay disjoint from all
    boundaries satisfy [is_repaired_with_deps]. *)

val is_repaired_with_deps :
  old_errors:(string * Parser_l2.loc) list ->
  new_errors:(string * Parser_l2.loc) list ->
  deps:dependency_boundary list ->
  bool
(** [is_repaired_with_deps] is [true] iff [is_repaired] is [true] AND every
    remaining [new_errors] entry is position-disjoint from every entry of
    [deps]. Matches
    [proofs/RepairMonotonicity.v
    repair_monotonic_across_dep_boundaries]. *)
