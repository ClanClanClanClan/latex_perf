(** LaTeX validation rules for typography, style, and modernisation.

    {b Thread safety:} Regex operations use [Re_compat] (backed by the [Re]
    library), which is thread-safe — no global mutable state. Concurrent calls
    to {!run_all} from multiple threads are safe. For OCaml 5 domains, the
    [semantic_state] and [File_context] modules use per-thread [Hashtbl] keyed
    by [Thread.id], which is safe for threads but not for domains (domains share
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

val rules_class_c : rule list
(** Log-dependent rules (Class C). Only produce results when
    {!Log_parser.set_log_context} has been called. *)

val run_class_c : string -> result list
(** Run only Class C (log-dependent) rules. Requires log context to be set via
    {!Log_parser.set_log_context}; returns [[]] otherwise. *)

val rules_class_d : rule list
(** Advisory rules (Class D) — STYLE family heuristics. PR #241 (memo §11): NOT
    included in {!run_all}; reachable only through {!run_with_policy} with
    {!Execution_policy.with_advisory} / {!Execution_policy.full}. *)

val run_class_d : string -> result list
(** Run only Class D (advisory / STYLE family) rules. Separate from [run_all] so
    the keystroke-critical hot path never executes them. *)

val run_with_build : string -> result list
(** Run all A/B rules via {!run_all} plus Class C rules. Use when a compile log
    is available (save/build trigger). *)

val run_with_policy : Execution_policy.t -> string -> result list
(** Run rules according to the given execution policy. *)

val rules_user_macro : rule list
(** WS2 user macro registry validators (CMD-015/016/017). *)

val rules_project : rule list
(** WS3 project-level validators (PRJ-001/002/003/004). *)

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
