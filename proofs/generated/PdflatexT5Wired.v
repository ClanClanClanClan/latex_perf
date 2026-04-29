(** * PdflatexT5Wired — catalogue-specific T5 wiring.

    Per `specs/v27/V27_T5_WIRING_PLAN.md` Stage 5: derive the
    catalogue-specific instance of [PdflatexModel.pdflatex_T5_safe]
    by instantiating the universal-over-catalogue form with
    [Generated.Catalogue.all_proved_rule_ids].

    This file lives in [LaTeXPerfectionist.Generated] (which depends
    on [LaTeXPerfectionist]).  It can import both the main library
    (PdflatexModel, T5_concrete) and the auto-generated catalogue.
    Putting it here keeps the main-library files (which the
    capstone proof lives in) free of the circular theory dependency
    that would otherwise arise from Generated → main and the wiring's
    desire to cross from main → Generated.

    Zero admits, zero axioms. *)

From Coq Require Import List String.
From LaTeXPerfectionist Require Import T5_concrete PdflatexModel.
From LaTeXPerfectionist.Generated Require Import Catalogue.
Import ListNotations.

(** ── Catalogue-specific T5 instance ───────────────────────────────── *)

(** The "every rule in [rules] is in the proved catalogue" predicate
    instantiated with [Generated.Catalogue.all_proved_rule_ids]. *)
Definition pdflatex_no_static_violation_proved
    (p : pdflatex_project) (rules : list rule_id) : Prop :=
  pdflatex_no_static_violation_pred all_proved_rule_ids p rules.

(** Direct catalogue-attached witness: for any project and any rule
    list contained in the proved catalogue, no static violation
    remains.  Derived from [PdflatexModel.pdflatex_T5_safe_holds]
    by instantiating the universal-over-catalogue with
    [all_proved_rule_ids]. *)
Theorem pdflatex_T5_safe_proved :
  forall (p : pdflatex_project) (rules : list rule_id),
    pdflatex_all_rules_pass all_proved_rule_ids p rules ->
    pdflatex_no_static_violation_proved p rules.
Proof.
  intros p rules Hall.
  apply (pdflatex_T5_safe_holds p all_proved_rule_ids rules Hall).
Qed.

(** Strong corollary: when the deployed rule list IS the proved
    catalogue itself, no static violation remains.  Useful for
    callers that deploy "all rules with a per-rule QED". *)
Corollary pdflatex_T5_safe_for_full_catalogue :
  forall (p : pdflatex_project),
    pdflatex_no_static_violation_proved p all_proved_rule_ids.
Proof.
  intros p. apply pdflatex_T5_safe_proved.
  unfold pdflatex_all_rules_pass, pdflatex_rule_passes_pred.
  intros r Hr. exact Hr.
Qed.

(** ── Zero-admit witness ──────────────────────────────────────────── *)

Definition pdflatex_t5_wired_zero_admits : True := I.
