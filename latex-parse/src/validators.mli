(** LaTeX validation rules for typography, style, and modernisation. *)

type severity = Error | Warning | Info

type result = {
  id : string;
  severity : severity;
  message : string;
  count : int;
}

type rule = {
  id : string;
  run : string -> result option;
  languages : string list;
}

type layer = L0 | L1 | L2 | L3 | L4

val severity_to_string : severity -> string

val strip_math_segments : string -> string
(** Remove math-mode content (inline and display) from a LaTeX source string. *)

val run_all : string -> result list
(** Run all active rules against the source and return triggered results. *)

val run_all_parallel : ?n_domains:int -> string -> result list
(** Like {!run_all} but splits rules across OCaml 5.x domains for parallel
    execution. Gated behind [L0_PARALLEL=1] env var; falls back to sequential if
    unset. Default [n_domains] is 4. *)

val run_all_for_language : string -> string option -> result list
(** Like {!run_all} but with language gating. If [Some lang], only rules
    matching that language (or universal rules) are run. If [None], auto-detects
    language from the document preamble. *)

val run_all_with_timings : string -> result list * float * (string * float) list
(** Like {!run_all} but returns [(results, total_ms, per_rule_timings)]. *)

val run_all_with_timings_for_layer :
  string -> layer -> result list * float * (string * float) list
(** Like {!run_all_with_timings} but restricted to rules for the given layer. *)

val precondition_of_rule_id : string -> layer
(** Map a rule ID to the layer it belongs to based on its prefix. *)

val rules_vpd_catalogue : rule list
(** Rules with VPD pattern annotations and formal soundness proofs. *)

val vpd_catalogue_count : int
(** Number of rules in the VPD catalogue. *)
