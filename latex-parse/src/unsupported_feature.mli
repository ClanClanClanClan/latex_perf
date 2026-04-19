(** Detection of LaTeX source constructs outside the LP-Core subset.

    Mirrors [specs/v26/language_contract.yaml] forbidden_features and
    lp_foreign.triggers. Feature detection is regex-based (via Re_compat) on raw
    source, no parsing required.

    See [specs/v26/language_contract.md] for the full tier definitions. *)

type severity =
  | Forbidden_in_core
      (** LP-Core boundary violation (document becomes LP-Extended) *)
  | Foreign_trigger
      (** LP-Foreign classifier (document exits guaranteed mode) *)

type t = {
  id : string;  (** Stable feature ID, e.g. "arbitrary_def", "shell_escape" *)
  severity : severity;
      (** Whether this feature demotes tier or triggers foreign *)
  offset : int;  (** Byte offset in source where feature was detected *)
  line : int;  (** Line number (1-indexed) *)
  message : string;  (** Human-readable description *)
}

val detect : string -> t list
(** [detect src] scans [src] for all LP-Core forbidden constructs and all
    LP-Foreign triggers. Returns features in source order. Total on any input. *)

val any_foreign_trigger : t list -> bool
(** [any_foreign_trigger features] is [true] iff any element has severity
    [Foreign_trigger]. *)

val any_forbidden_in_core : t list -> bool
(** [any_forbidden_in_core features] is [true] iff any element has severity
    [Forbidden_in_core]. *)

val severity_to_string : severity -> string
(** [severity_to_string s] returns the YAML-compatible identifier. *)
