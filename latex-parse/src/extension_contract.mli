(** Extension plane and foreign contracts (WS12 Stage 1).

    An {e extension} is any feature outside the guaranteed LP-Core/LP-Extended
    surface — a package binding, a tooling integration, a foreign rule bundle.
    v27's support contract is explicit and bounded (spec §6): unsupported or
    foreign features may only enter through an EXPLICIT contract, and an
    extension can never silently claim a stronger guarantee than its risk
    allows.

    This module provides:
    - the {b extension contract manifest} format (a JSON config declaring, per
      extension, its [name], what it [provides], what it [requires], a [risk]
      classification, and a declared [support] level), with total loading that
      reports errors instead of raising;
    - the {b foreign-contract boundary} [evaluate], which folds the loaded
      contracts against a base support level to compute the EFFECTIVE support
      level. A foreign/unsafe extension DOWNGRADES the effective guarantee and
      never upgrades it; an extension over-claiming (declaring a support level
      stronger than its risk allows) is REJECTED.

    Follows the WS9 config-module + CLI-flag pattern; the manifest mirrors the
    JSON shape of [specs/rules/rule_contracts.json]. Loading is total. *)

(** Risk classification of an extension. Ordered [Safe] < [Review] < [Unsafe]
    from least to most dangerous. *)
type risk = Safe | Review | Unsafe

(** Support / guarantee level. Ordered [Foreign] < [Community] < [Supported]
    from weakest to strongest guarantee. Higher = stronger promise. *)
type support = Foreign | Community | Supported

type contract = {
  ext_name : string;  (** Stable extension identifier, e.g. "tikz-cd". *)
  provides : string list;
      (** Rule-ids and/or feature tags the extension provides. *)
  requires : string list;  (** Packages/features the extension depends on. *)
  risk : risk;  (** Risk classification. *)
  support : support;  (** Declared support level (the CLAIM to be checked). *)
}

(* ── Ordering / parsing helpers ─────────────────────────────────── *)

val risk_to_string : risk -> string
val risk_of_string : string -> risk option
val support_to_string : support -> string
val support_of_string : string -> support option

val support_rank : support -> int
(** [Foreign = 0], [Community = 1], [Supported = 2]. *)

val support_min : support -> support -> support
(** The weaker of two support levels (never upgrades). *)

val max_support_for_risk : risk -> support
(** The strongest support an extension of the given risk may legitimately claim:
    [Safe -> Supported], [Review -> Community], [Unsafe -> Foreign]. *)

val over_claims : contract -> bool
(** [true] iff the contract declares a support level stronger than
    {!max_support_for_risk} allows for its risk. Such a contract is rejected. *)

(* ── Manifest loading (total, errors reported) ──────────────────── *)

val load_string : string -> (contract list, string) result
(** Parse a manifest from a JSON string. Never raises: a malformed manifest
    yields [Error msg]. *)

val load_file : string -> (contract list, string) result
(** Read and parse a manifest file. Never raises: a missing/unreadable/malformed
    file yields [Error msg]. *)

(* ── Foreign-contract boundary ──────────────────────────────────── *)

type entry = {
  e_name : string;
  e_risk : risk;
  e_declared : support;  (** The extension's declared support level. *)
  e_downgrade : bool;
      (** [true] iff this extension pulls the effective guarantee below [base]. *)
  e_reason : string;  (** Machine-readable reason token. *)
}

type effective = {
  base : support;  (** The base support level the evaluation started from. *)
  effective : support;  (** [min base] over every accepted extension. *)
  entries : entry list;  (** Per-extension risk / downgrade surfacing. *)
}

type rejection = {
  r_name : string;
  r_risk : risk;
  r_declared : support;
  r_reason : string;  (** Machine-readable reason token. *)
}

val evaluate :
  base:support -> contract list -> (effective, rejection list) result
(** Compute the effective support level. Fail-closed: if any extension
    {!over_claims} (declares a guarantee stronger than its risk allows) the
    whole evaluation is [Error rejections] — the manifest cannot be trusted.
    Otherwise [Ok effective], where [effective.effective] is the base level
    lowered by the weakest extension's declared support (foreign/unsafe
    extensions therefore downgrade it and none can upgrade it). *)

val downgrades_below : effective -> support -> bool
(** [downgrades_below eff threshold] is [true] iff the effective support is
    strictly weaker than [threshold]. Used by the CLI [--strict] variant. *)
