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

(** ─────────────────────────────────────────────────────────────────
    v27 T5 STAGE 2 — discharge rule_safety_rule + Section closure
    ─────────────────────────────────────────────────────────────────

    Per V27_T5_WIRING_PLAN.md Stage 2: discharge T5_wrapper's
    rule_safety_rule hypothesis against the Stage-1 placeholders, and
    apply the T5_rule_safe Section closure to produce a project-
    attached T5_safe theorem.  With pdflatex_no_static_violation_pred
    := True the discharge is trivial; the structure is in place for
    Stages 3-4 to refine the predicates substantively without
    changing the wiring shape. *)

(** Project-attached "every rule in [rules] passes for project [p]". *)
Definition pdflatex_all_rules_pass (p : build_graph) (rules : list rule_id)
    : Prop :=
  forall r, In r rules -> pdflatex_rule_passes_pred p r.

(** Stage 2 discharge: rule_safety_rule for the Stage-1 placeholders.
    With no_static_violation_pred := True the conclusion is trivial;
    Stage 4 strengthens this to a meaningful "no rule fires" claim
    that genuinely consumes the all-pass premise. *)
Lemma pdflatex_rule_safety_rule_proof :
  forall (p : build_graph) (rules : list rule_id),
    pdflatex_all_rules_pass p rules ->
    pdflatex_no_static_violation_pred p rules.
Proof.
  intros p rules _.
  unfold pdflatex_no_static_violation_pred. exact I.
Qed.

(** Apply T5_wrapper.T5_rule_safe Section closure with our concrete
    instantiations.  Produces the project-attached T5 safety theorem.
    Stage 5 wires this into proofs/PdflatexModel.v's pdflatex_T5_safe
    (currently True). *)
Theorem pdflatex_T5_safe_stage2 :
  forall (p : build_graph) (rules : list rule_id),
    pdflatex_all_rules_pass p rules ->
    pdflatex_no_static_violation_pred p rules.
Proof.
  intros p rules Hall.
  apply (T5_rule_safe
           rule_id
           (pdflatex_rule_passes_pred p)
           (pdflatex_no_static_violation_pred p)
           (pdflatex_rule_safety_rule_proof p)
           rules).
  exact Hall.
Qed.

(** ── Stage 2 zero-admit witness ───────────────────────────────────── *)

Definition t5_concrete_stage2_zero_admits : True := I.
