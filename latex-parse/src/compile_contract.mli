(** Pre-compile readiness contract (memo §5.5; T0/T5 de-stubbed v27.1.52).

    Evaluates T0–T5 at runtime. Given a [Project_model.t] and a
    [Build_profile.t], returns [Ready] iff every checked precondition holds, or
    [NotReady reasons] listing which preconditions fail.

    What each check actually runs at runtime:
    - T0: real parser acceptance — [Language_profile.classify_source] (NOT-READY
      on LP-Foreign) followed by [Parser_l2.parse_located] (NOT-READY with the
      first structural parse error's message + location).
    - T1: not runtime-checked at this layer (no-op; never claims a T1 property).
    - T2: include-graph closure — every [\input]/[\include] resolves, no cycle.
    - T3: engine/feature compatibility from the declared features + engine.
    - T4: semantic coherence from the [.aux] (duplicate labels), when supplied.
    - T5: real validator run — flags COMPILE-BLOCKING [Error] diagnostics only
      (rule families DELIM-/ENC-/PRT-), not every Error-severity style rule.

    T0 and T5 are complementary: the L2 parser is error-recovering, so a fault
    it does not itself flag (e.g. an unbalanced brace group, silently closed at
    EOF) is caught by T5's DELIM-001 rather than by T0.

    T6 (compilation progress) and T7 (output well-formedness) are NOT checked
    here — they are proof-level theorems over an ABSTRACT operational pdflatex
    model, not runtime checks, and are not yet connected byte-for-byte to this
    runtime parser (see specs/v26/compilation_guarantee_stack.md and
    docs/COMPILATION_GUARANTEE.md). A [Ready] result is therefore a sound
    readiness PRE-CHECK, not a total "it will compile" certificate. *)

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
  ?fast:bool ->
  ?aux_path:string ->
  ?source:string ->
  Project_model.t ->
  Build_profile.t ->
  ready_check_result
(** Evaluate T0–T5 against the project + profile. If [aux_path] is provided, T4
    (semantic coherence) is informed by the .aux file contents; otherwise T4
    falls back to source-only analysis of labels declared in the root .tex.

    [source] is the root document's bytes, used by the T0 (parser + language
    profile) and T5 (validator) checks. When omitted, the root [.tex] is read
    from disk; a read failure is reported as a T0 reason (never a silent
    [Ready]). Callers that already hold the source (e.g. the CLI lint path)
    should pass it to avoid a re-read.

    [fast] (default [true]) selects the fast readiness kernel: parse the source
    ONCE (shared between T0's structural-error check and T5's PRT context) and
    run ONLY the 37 compile-blocking rules (DELIM-/ENC-/PRT-) instead of all
    ~641. The verdict — [Ready] / [NotReady reasons] with the same reason
    constructors and messages — is identical to [~fast:false], which runs the
    original full path (every rule, then filter) and is retained as the safety
    fallback and the differential-harness reference. *)

val reason_to_string : reason -> string
