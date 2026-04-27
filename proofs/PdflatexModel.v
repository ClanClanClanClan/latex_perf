(** * PdflatexModel — v27 WS8 discharge target (Stage 1: scaffold).

    Per [proofs/ADMISSIBILITY_MAP.md] + `specs/v27/V27_WS8_PLAN.md`,
    this file's mission is to instantiate the [Compile_progress] and
    [Output_wellformed] Sections (in [CompileProgress.v] /
    [CompileWellFormed.v]) against a concrete pdflatex toolchain
    model, ultimately discharging both load-bearing hypotheses
    ([compile_progress_rule] + [output_wellformed_rule]) and
    producing an unconditional [pdflatex_compile_safe] theorem.

    **Stage 1 (this commit, v26.5.0).**
    Defines concrete carrier types and predicate instantiations,
    invokes the upstream Sections with those instantiations, and
    derives parametric-only-in-the-load-bearing-hypothesis variants.
    T2 and T3 are tied to the EXISTING concrete predicates from
    [ProjectClosure.v] / [BuildProfileSound.v]; T0, T1, T4, T5 use
    [True] placeholders that Stages 2–5 refine to non-trivial claims
    (per the plan's per-stage decomposition).

    The Stage 1 top-level theorems
    ([pdflatex_T6_modulo_compile_progress_rule],
     [pdflatex_T7_modulo_output_wellformed_rule]) are strictly
    stronger than the upstream Section's parametric form: they
    bake in the concrete carriers + concrete T0–T5 instantiations,
    leaving only the two load-bearing rules as parametric. v27 WS8
    Stages 3 + 5 discharge those rules; Stage 6 closes
    [pdflatex_compile_safe] unconditionally.

    Zero admits, zero axioms (maintained throughout the staging). *)

From Coq Require Import List Bool Arith.
From LaTeXPerfectionist Require Import
  ProjectClosure
  BuildProfileSound
  CompileProgress
  CompileWellFormed.
Import ListNotations.

(** ── Concrete carriers ────────────────────────────────────────────── *)

(** A pdflatex project is a build graph. Stage 1 reuses the existing
    [ProjectClosure.build_graph] type; Stage 4 may extend with
    artefact-specific metadata. *)
Definition pdflatex_project : Type := build_graph.

(** A pdflatex profile bundles an engine choice and a feature set.
    Reuses [BuildProfileSound]'s [engine] and [feature] types. *)
Record pdflatex_profile := mk_pdflatex_profile {
  prof_engine : engine;
  prof_features : list feature;
}.

(** Stage 1: artefact carrier is opaque (a placeholder byte stream).
    Stage 4 refines to [pdf_artefact + log_artefact]. *)
Definition pdflatex_artefact : Type := list nat.

(** ── T0–T5 predicate instantiations ───────────────────────────────── *)

(** T0 — parser acceptance.
    Stage 1: trivially accepts every pdflatex_project (placeholder).
    Stage 2 refines to: every Tex node in the build graph has a
    parse-witness via [T0_wrapper.T0_parser_accepts]. *)
Definition pdflatex_T0_accepts (_ : pdflatex_project) : Prop := True.

(** T1 — expansion admissibility.
    Stage 1: trivially admits.
    Stage 2 refines to: the user macro registry is acyclic per
    [T1_wrapper.T1_expansion_admissible_merge]. *)
Definition pdflatex_T1_admissible (_ : pdflatex_project) : Prop := True.

(** T2 — project closure. **CONCRETE** — uses
    [ProjectClosure.project_closed]. *)
Definition pdflatex_T2_closed (p : pdflatex_project) : Prop :=
  project_closed p.

(** T3 — profile admissibility. **CONCRETE** — uses
    [BuildProfileSound.profile_admits], threading the profile's
    feature list and engine. *)
Definition pdflatex_T3_compatible (_ : pdflatex_project)
    (pf : pdflatex_profile) : Prop :=
  profile_admits pf.(prof_features) pf.(prof_engine).

(** T4 — semantic coherence.
    Stage 1: trivially coherent.
    Stage 2 refines to: labels-unique via
    [T4_wrapper.T4_labels_unique_packaged]. *)
Definition pdflatex_T4_coherent (_ : pdflatex_project) : Prop := True.

(** T5 — rule safety.
    Stage 1: trivially safe.
    Stage 2 refines to: every deployed Error-level rule QEDs
    against the project's emitted spans. *)
Definition pdflatex_T5_safe (_ : pdflatex_project) : Prop := True.

(** ── Toolchain predicates (Stage 1 placeholders) ─────────────────── *)

(** Bound on pdflatex pass count.
    Stage 1: [True] placeholder.
    Stage 2 introduces a concrete [pdflatex_pass_state] Fixpoint and
    proves a 5-pass termination bound. *)
Definition pdflatex_bounded_terminates
    (_ : pdflatex_project) (_ : pdflatex_profile) : Prop := True.

(** Compilation success — pdflatex exits cleanly with no fatal log.
    Stage 1: [True] placeholder.
    Stage 2 refines to [clean_exit /\ no_fatal_in_log]. *)
Definition pdflatex_compilation_succeeds
    (_ : pdflatex_project) (_ : pdflatex_profile) : Prop := True.

(** ── Stage 1 partial discharge of the parametric Sections ────────── *)

(** Apply [CompileProgress.Section_Compile_progress] with the
    concrete pdflatex instantiations. The Section closure produces
    a theorem parametric ONLY in [compile_progress_rule] — concretely:

    [forall (rule : <type-of-compile_progress_rule>) ...
     (T0..T5 + bounded → succeeds for the pdflatex carriers)]

    Stage 3 will discharge [rule] as a Qed-proved lemma; this commit
    just exposes the instantiated theorem skeleton. *)
Theorem pdflatex_T6_modulo_compile_progress_rule :
  (forall (p : pdflatex_project) (pf : pdflatex_profile),
     pdflatex_T0_accepts p ->
     pdflatex_T1_admissible p ->
     pdflatex_T2_closed p ->
     pdflatex_T3_compatible p pf ->
     pdflatex_T4_coherent p ->
     pdflatex_T5_safe p ->
     pdflatex_bounded_terminates p pf ->
     pdflatex_compilation_succeeds p pf) ->
  forall (p : pdflatex_project) (pf : pdflatex_profile),
    pdflatex_T0_accepts p ->
    pdflatex_T1_admissible p ->
    pdflatex_T2_closed p ->
    pdflatex_T3_compatible p pf ->
    pdflatex_T4_coherent p ->
    pdflatex_T5_safe p ->
    pdflatex_bounded_terminates p pf ->
    pdflatex_compilation_succeeds p pf.
Proof.
  intros rule.
  exact (T6_compile_progress_under_bound
           pdflatex_project pdflatex_profile
           pdflatex_T0_accepts
           pdflatex_T1_admissible
           pdflatex_T2_closed
           pdflatex_T3_compatible
           pdflatex_T4_coherent
           pdflatex_T5_safe
           pdflatex_bounded_terminates
           pdflatex_compilation_succeeds
           rule).
Qed.

(** Stage 1 also exposes a *trivial* discharge that closes T6
    unconditionally for the placeholder predicates. This is honest
    only because T0–T5 + bounded + succeeds are all [True]; once
    Stages 2/3 refine to substantive predicates, the discharge will
    require real proof content (which Stage 3 supplies). *)
Theorem pdflatex_compile_progress_rule_trivial :
  forall (p : pdflatex_project) (pf : pdflatex_profile),
    pdflatex_T0_accepts p ->
    pdflatex_T1_admissible p ->
    pdflatex_T2_closed p ->
    pdflatex_T3_compatible p pf ->
    pdflatex_T4_coherent p ->
    pdflatex_T5_safe p ->
    pdflatex_bounded_terminates p pf ->
    pdflatex_compilation_succeeds p pf.
Proof.
  intros p pf _ _ _ _ _ _ _.
  unfold pdflatex_compilation_succeeds. exact I.
Qed.

(** Stage 1 unconditional T6 (with placeholder predicates).
    Stage 2/3 will REPLACE this with a substantive discharge that
    uses concrete [pdflatex_step] iteration semantics. *)
Theorem pdflatex_T6_stage1 :
  forall (p : pdflatex_project) (pf : pdflatex_profile),
    pdflatex_T0_accepts p ->
    pdflatex_T1_admissible p ->
    pdflatex_T2_closed p ->
    pdflatex_T3_compatible p pf ->
    pdflatex_T4_coherent p ->
    pdflatex_T5_safe p ->
    pdflatex_bounded_terminates p pf ->
    pdflatex_compilation_succeeds p pf.
Proof.
  exact (pdflatex_T6_modulo_compile_progress_rule
           pdflatex_compile_progress_rule_trivial).
Qed.

(** ── T7 instantiation — Stage 1 ──────────────────────────────────── *)

(** Produce-relation: Stage 1 placeholder (every project produces
    every artefact). Stage 4 refines to a concrete tying based on
    pdflatex_step output. *)
Definition pdflatex_produces
    (_ : pdflatex_project) (_ : pdflatex_profile)
    (_ : pdflatex_artefact) : Prop := True.

(** Output well-formedness predicate. Stage 1 placeholder.
    Stage 4 refines to [valid_pdf_graph \/ log_no_fatal]. *)
Definition pdflatex_output_format_well_formed
    (_ : pdflatex_artefact) : Prop := True.

(** Apply [CompileWellFormed.Section_Output_wellformed] with the
    pdflatex instantiations. Parametric in [output_wellformed_rule];
    Stage 5 discharges. *)
Theorem pdflatex_T7_modulo_output_wellformed_rule :
  (forall (p : pdflatex_project) (pf : pdflatex_profile)
          (out : pdflatex_artefact),
     pdflatex_compilation_succeeds p pf ->
     pdflatex_produces p pf out ->
     pdflatex_output_format_well_formed out) ->
  forall (p : pdflatex_project) (pf : pdflatex_profile)
         (out : pdflatex_artefact),
    pdflatex_compilation_succeeds p pf ->
    pdflatex_produces p pf out ->
    pdflatex_output_format_well_formed out.
Proof.
  intros rule.
  exact (T7_output_wellformed
           pdflatex_project pdflatex_profile pdflatex_artefact
           pdflatex_compilation_succeeds
           pdflatex_produces
           pdflatex_output_format_well_formed
           rule).
Qed.

Theorem pdflatex_output_wellformed_rule_trivial :
  forall (p : pdflatex_project) (pf : pdflatex_profile)
         (out : pdflatex_artefact),
    pdflatex_compilation_succeeds p pf ->
    pdflatex_produces p pf out ->
    pdflatex_output_format_well_formed out.
Proof.
  intros p pf out _ _.
  unfold pdflatex_output_format_well_formed. exact I.
Qed.

Theorem pdflatex_T7_stage1 :
  forall (p : pdflatex_project) (pf : pdflatex_profile)
         (out : pdflatex_artefact),
    pdflatex_compilation_succeeds p pf ->
    pdflatex_produces p pf out ->
    pdflatex_output_format_well_formed out.
Proof.
  exact (pdflatex_T7_modulo_output_wellformed_rule
           pdflatex_output_wellformed_rule_trivial).
Qed.

(** ── Stage 1 capstone: the parametric pdflatex_compile_safe ─────── *)

(** With Stage 1 placeholders, the compile-safe theorem closes
    trivially. Stages 2–6 substitute substantive predicates and
    rebuild this theorem against them; the final v27.0.0
    [pdflatex_compile_safe] will replace this with the discharged
    unconditional version against concrete pass-iteration semantics. *)
Theorem pdflatex_compile_safe_stage1 :
  forall (p : pdflatex_project) (pf : pdflatex_profile)
         (out : pdflatex_artefact),
    pdflatex_T0_accepts p ->
    pdflatex_T1_admissible p ->
    pdflatex_T2_closed p ->
    pdflatex_T3_compatible p pf ->
    pdflatex_T4_coherent p ->
    pdflatex_T5_safe p ->
    pdflatex_bounded_terminates p pf ->
    pdflatex_produces p pf out ->
    pdflatex_compilation_succeeds p pf /\
    pdflatex_output_format_well_formed out.
Proof.
  intros p pf out H0 H1 H2 H3 H4 H5 Hbound Hproduces.
  assert (Hsucc : pdflatex_compilation_succeeds p pf)
    by (apply pdflatex_T6_stage1; assumption).
  split.
  - exact Hsucc.
  - apply (pdflatex_T7_stage1 p pf out Hsucc Hproduces).
Qed.

(** ── Zero-admit witness ──────────────────────────────────────────── *)
Definition pdflatex_model_stage1_zero_admits : True := I.
