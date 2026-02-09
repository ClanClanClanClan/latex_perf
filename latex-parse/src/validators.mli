(** LaTeX validation rules for typography, style, and modernisation. *)

type severity = Error | Warning | Info

type result = {
  id : string;
  severity : severity;
  message : string;
  count : int;
}

type rule = { id : string; run : string -> result option }
type layer = L0 | L1 | L2 | L3 | L4

val severity_to_string : severity -> string

val strip_math_segments : string -> string
(** Remove math-mode content (inline and display) from a LaTeX source string. *)

val run_all : string -> result list
(** Run all active rules against the source and return triggered results. *)

val run_all_with_timings : string -> result list * float * (string * float) list
(** Like {!run_all} but returns [(results, total_ms, per_rule_timings)]. *)

val run_all_with_timings_for_layer :
  string -> layer -> result list * float * (string * float) list
(** Like {!run_all_with_timings} but restricted to rules for the given layer. *)
