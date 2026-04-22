(** Pre-compile readiness contract (memo §5.5, v26.2).

    Evaluates T0–T5 at runtime. Given a [Project_model.t] and a
    [Build_profile.t], returns [Ready] iff every static precondition holds, or
    [NotReady reasons] listing which preconditions fail.

    T6 (compilation progress) and T7 (output well-formedness) are NOT checked
    here — they are parametric-proof-level theorems, not runtime checks (see
    specs/v26/compilation_guarantee_stack.md). *)

type reason =
  | T0_parse_fails of { file : string; message : string }
  | T1_expansion_fails of string
  | T2_project_not_closed of [ `Cycle_in_build_graph | `Missing_file of string ]
  | T3_profile_incompatible of { feature : string; profile : string }
  | T4_semantic_incoherent of
      [ `Duplicate_labels of string list | `Missing_bib_entries of string list ]
  | T5_rule_violations of string list
      (** Rule-IDs that fired at Error severity. *)

type ready_check_result = Ready | NotReady of reason list

val check_ready_to_compile :
  ?aux_path:string -> Project_model.t -> Build_profile.t -> ready_check_result
(** Evaluate T0–T5 against the project + profile. If [aux_path] is provided, T4
    (semantic coherence) is informed by the .aux file contents; otherwise T4
    falls back to source-only analysis of labels declared in the root .tex. *)

val reason_to_string : reason -> string
