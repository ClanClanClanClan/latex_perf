(** LaTeX validation rules for typography, style, and modernisation.

    {b Thread safety:} The OCaml [Str] module uses global mutable state for
    regex matching. Validators that use [Str.regexp] / [Str.search_forward] are
    NOT thread-safe. Do NOT call {!run_all} concurrently from multiple threads
    or OCaml 5 domains. Use sequential execution or process-level parallelism
    (separate OS processes) for concurrent linting.

    The [semantic_state] module uses per-thread [Hashtbl] keyed by [Thread.id],
    which is safe for threads but not for domains (domains share
    [Thread.id = 0]). *)

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

val run_all_scored :
  ?config:Evidence_scoring.scoring_config ->
  string ->
  Evidence_scoring.scored_result list
(** Like {!run_all} but returns confidence-scored results (spec W75). *)

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

val run_all_incremental : ?prev_src:string -> string -> result list
(** Incremental validation: only re-runs validators on chunks that changed since
    [prev_src]. Uses chunk_store for hash-based change detection. Cross-chunk
    rules (L3+) run on full source regardless. *)

val run_all_scheduled :
  ?edit_pos:int -> ?prev_src:string -> string -> result list
(** EDF-scheduled incremental validation. Chunks closer to [edit_pos] and lower
    layers execute first. Sequential execution in current version. *)
