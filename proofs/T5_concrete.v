(** * T5_concrete — concrete carrier for T5_wrapper Section closure.

    Per `specs/v27/V27_T5_WIRING_PLAN.md` Stage 1:

    Pick a concrete `rule_id` and stage placeholder predicates that
    Stages 2–4 refine to substantive forms tied to the per-rule QED
    chain in `proofs/generated/`.

    Stage 1 (this file): scaffolding only.  Concrete `rule_id := string`,
    placeholder `pdflatex_rule_passes_pred := fun _ _ => True`, placeholder
    `pdflatex_no_static_violation_pred := fun _ _ => True`.  Stage 2
    discharges `T5_wrapper.rule_safety_rule` against the placeholders.
    Stage 3 refines `pdflatex_rule_passes_pred` to consume the per-rule
    soundness theorems for FAMILY-NNN rules with QEDs in
    `proofs/generated/`.  Stage 4 refines
    `pdflatex_no_static_violation_pred` to a meaningful "no rule fires
    on the project" predicate.  Stage 5 wires the result into
    `proofs/PdflatexModel.v`'s `pdflatex_T5_safe`.

    Zero admits, zero axioms. *)

From Coq Require Import List String.
From LaTeXPerfectionist Require Import ProjectClosure T5_wrapper.
Import ListNotations.

(** ── Concrete rule_id carrier ─────────────────────────────────────── *)

(** A rule identifier is a FAMILY-NNN string (e.g. "TYPO-001", "SPC-008")
    drawn from `specs/rules/rule_contracts.yaml`.  Strings are used
    rather than an inductive enumeration so the predicate can dispatch
    on the rule name without requiring a Coq mirror of the entire
    catalogue. *)
Definition rule_id : Type := string.

(** ── Stage 1 placeholder predicates ───────────────────────────────── *)

(** Stage 1 placeholder: every rule trivially passes.  Stage 3 refines
    by case-analysing on the rule string: for each FAMILY-NNN with a
    per-rule soundness QED, the predicate is the per-rule premise; for
    unknown / unimplemented rules it falls back to True (vacuous).
    Defined over `build_graph` to avoid depending on PdflatexModel.v
    (which would create a circular dependency). *)
Definition pdflatex_rule_passes_pred (_ : build_graph) (_ : rule_id) : Prop :=
  True.

(** Stage 1 placeholder: no rule list is in static violation.  Stage 4
    refines to "no rule in the list fires on the project at any
    catalogued span" once the runtime validator's emit-set is
    formalised. *)
Definition pdflatex_no_static_violation_pred (_ : build_graph)
    (_ : list rule_id) : Prop :=
  True.

(** ── Stage 1 zero-admit witness ───────────────────────────────────── *)

Definition t5_concrete_stage1_zero_admits : True := I.

(** Stage 2's discharge of `T5_wrapper.rule_safety_rule` against these
    placeholders is intentionally trivial (conclusion is True).  The
    Section closure produces a project-attached T5_safe theorem; with
    placeholders that theorem is vacuous, but the structure is in
    place for Stages 3–5 to refine without changing the wiring shape. *)
