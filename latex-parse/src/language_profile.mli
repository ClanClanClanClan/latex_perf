(** Language profile classifier — LP-Core / LP-Extended / LP-Foreign tiering.

    Implements the tier membership decision procedure defined in
    [specs/v26/language_contract.md] §tier-membership-decision-procedure and
    proved in [proofs/LanguageContract.v].

    The classifier is total on any input: every source maps to exactly one tier. *)

type tier = LP_Core | LP_Extended | LP_Foreign

val classify_source : string -> tier * Unsupported_feature.t list
(** [classify_source src] runs the deterministic tier-membership pass on [src]
    and returns the tier plus the list of features that triggered demotion. For
    LP-Core, the feature list is empty. *)

val tier_of_string : string -> tier option
(** [tier_of_string s] parses a CLI/REST profile identifier. *)

val tier_to_string : tier -> string
(** [tier_to_string t] returns the canonical lowercase identifier (e.g.
    "lp-core"). *)

val tier_name : tier -> string
(** [tier_name t] returns the human-readable name ("LP-Core", etc.). *)

val tier_is_at_least : tier -> tier -> bool
(** [tier_is_at_least a b] is [true] iff tier [a] supports everything tier [b]
    supports. Ordering: LP_Foreign ⊂ LP_Extended ⊂ LP_Core (subset monotonicity
    in the memo §4.3 sense: LP-Core is the strictest). *)

(** Thread-local context for passing the effective tier through a request. Set
    by CLI/REST at request entry, cleared at request exit. *)
module Context : sig
  val set : tier -> unit
  val get : unit -> tier option
  val clear : unit -> unit
end
