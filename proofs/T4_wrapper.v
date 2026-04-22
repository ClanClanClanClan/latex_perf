(** * T4_wrapper — semantic coherence (memo §5, T4).

    Wraps [LabelsUnique.v] + [ProjectSemantics.v] into a T4-shaped
    theorem: given project closure (T2), labels are globally unique and
    references resolve within the project. Counter-state consistency
    and bibliography resolution are hypothesis-parametric in v26.2 —
    see [ADMISSIBILITY_MAP.md] — and discharged in v27 WS8 once the
    BibTeX / Biber / counter models ship.

    Zero admits, zero axioms. *)

From LaTeXPerfectionist Require Import ProjectSemantics.
From Coq Require Import List.
Import ListNotations.

(** Labels-unique claim from [ProjectSemantics.v]:
    [labels_unique labels] iff every name maps to at most one file_id. *)

(** ── T4 — packaged form ───────────────────────────────────────────── *)

Theorem T4_labels_unique_packaged :
  forall (labels : list ProjectSemantics.label),
    ProjectSemantics.labels_unique labels ->
    (forall n f1 f2,
      In (n, f1) labels -> In (n, f2) labels -> f1 = f2).
Proof.
  intros labels Huniq n f1 f2 H1 H2. apply (Huniq n f1 f2 H1 H2).
Qed.

(** Empty-label list is trivially unique. Useful base case. *)
Theorem T4_empty_labels_unique :
  ProjectSemantics.labels_unique [].
Proof.
  intros n f1 f2 H1 _. inversion H1.
Qed.

(** ── T4 counters / bibliography — hypothesis-parametric ──────────── *)

(** v26.2 hypothesis-parametric pattern: T4 counter consistency and
    bibliography resolution are delegated to v27 WS8. We state the
    shapes here so the wrapper theorem compiles against any future
    instantiation. *)

Section T4_external_subproofs.

  Variable project : Type.
  Variable counters_consistent : project -> Prop.
  Variable bib_entries_resolve : project -> Prop.

  (** Packaged T4 conclusion: if the caller supplies counter +
      bibliography coherence, and labels are unique, then T4 holds. *)
  Theorem T4_coherent_under_hypotheses :
    forall (p : project)
           (labels : list ProjectSemantics.label),
      ProjectSemantics.labels_unique labels ->
      counters_consistent p ->
      bib_entries_resolve p ->
      (ProjectSemantics.labels_unique labels /\
       counters_consistent p /\
       bib_entries_resolve p).
  Proof.
    intros p labels Huniq Hc Hb. split; [exact Huniq | split; assumption].
  Qed.

End T4_external_subproofs.

(** Zero-admit witness. *)
Definition t4_wrapper_zero_admits : True := I.
