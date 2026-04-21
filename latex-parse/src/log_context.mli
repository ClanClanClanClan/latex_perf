(** Compile-log context (memo §10.4).

    Re-exports the structured log context from {!Log_parser} as a first-class
    module so validators and downstream consumers (Class C rules,
    Build_artifact_state, evidence_scoring) can reference [Log_context.t]
    without pulling in the full parser surface.

    The underlying type lives in [log_parser.mli] to avoid a mutual dependency
    between the parser and this API; this module re-exports the same type alias
    and the thread-local set/get/clear helpers. *)

type t = Log_parser.log_context
(** Alias for [Log_parser.log_context]. Identical structure; callers can treat
    either name. *)

val empty : t
(** Empty context: no events, no overfull lines, etc. Equal to
    [Log_parser.empty_context]. *)

val parse : string -> t
(** Parse a LaTeX .log-file string into a structured context. Delegates to
    {!Log_parser.parse_log}. *)

val set : t -> unit
(** Install [t] as the thread-local log context for downstream validators. *)

val get : unit -> t option
(** Retrieve the thread-local log context, if any. *)

val clear : unit -> unit
(** Clear the thread-local log context. *)

val is_active : unit -> bool
(** [true] iff [get ()] would return [Some _]. Convenience for
    [Evidence_scoring.score_result ~build_profile_active]. *)
