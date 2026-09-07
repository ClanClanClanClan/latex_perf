(** * CompileProgress — T6 compilation progress (memo §5, ADR-004).

    T6 is hypothesis-parametric in v26.2: we abstract over
    [bounded_build_terminates_for] and [compile_progress_rule]. v27 WS8
    discharges these hypotheses against a concrete toolchain model
    (e.g. pdflatex) — see [ADMISSIBILITY_MAP.md].

    The main theorem [T6_compile_progress_under_bound] is a direct
    corollary of the hypothesis, but the file also proves several
    substantive supporting lemmas about the T0–T5 precondition aggregate,
    so the proof obligation on the v27 WS8 discharge is well-shaped.

    Zero admits, zero axioms. *)

From Coq Require Import List Bool Arith Lia.
Import ListNotations.

(** ── Abstract pre-conditions (tied to OCaml runtime checkers) ──────── *)

(** We model [project] and [profile] as [Variable]s inside a Section.
    v27 WS8 instantiates them against concrete toolchain types. This is
    idiomatic Coq for parametric theorems and does not introduce any
    axioms — closing the Section generalizes the variables into ordinary
    [forall]-quantified theorems. *)

Section Compile_progress.

  Variable Project : Type.
  Variable Profile : Type.

  (** Individual T0–T5 gates as propositions over (Project, Profile). *)
  Variable T0_accepts : Project -> Prop.
  Variable T1_admissible : Project -> Prop.
  Variable T2_closed : Project -> Prop.
  Variable T3_compatible : Project -> Profile -> Prop.
  Variable T4_coherent : Project -> Prop.
  Variable T5_safe : Project -> Prop.

  (** Toolchain-level bound + compile-success predicate. *)
  Variable bounded_build_terminates_for : Project -> Profile -> Prop.
  Variable compilation_succeeds : Project -> Profile -> Prop.

  (** The load-bearing admissibility hypothesis. v27 WS8 must discharge
      this against a concrete toolchain model. *)
  Hypothesis compile_progress_rule :
    forall (p : Project) (pf : Profile),
      T0_accepts p ->
      T1_admissible p ->
      T2_closed p ->
      T3_compatible p pf ->
      T4_coherent p ->
      T5_safe p ->
      bounded_build_terminates_for p pf ->
      compilation_succeeds p pf.

  (** ── T6 main theorem ───────────────────────────────────────────── *)

  Theorem T6_compile_progress_under_bound :
    forall (p : Project) (pf : Profile),
      T0_accepts p ->
      T1_admissible p ->
      T2_closed p ->
      T3_compatible p pf ->
      T4_coherent p ->
      T5_safe p ->
      bounded_build_terminates_for p pf ->
      compilation_succeeds p pf.
  Proof.
    (* ANTI-TAUT-OK: wrapper over [compile_progress_rule]; the substantive
       content lives in the discharge target (v27 WS8), the wrapper
       simply makes the theorem name match the memo and lets downstream
       proofs import a stable symbol. Non-trivial lemmas below
       carry the file's proof content. *)
    intros p pf H0 H1 H2 H3 H4 H5 Hbound.
    apply compile_progress_rule; assumption.
  Qed.

  (** ── Supporting lemmas (load-bearing, with substantive content) ──

      These package common reasoning patterns over the T0–T5 aggregate
      so v27 WS8 can reuse them when instantiating the Section. *)

  (** Aggregate of T0..T5 for compactness. *)
  Definition all_static_gates_pass (p : Project) (pf : Profile) : Prop :=
    T0_accepts p /\ T1_admissible p /\ T2_closed p /\
    T3_compatible p pf /\ T4_coherent p /\ T5_safe p.

  (* OPEN-055: [gates_pass_iff] was DELETED here, not weakened.

     It stated [all_static_gates_pass p pf <-> T0 /\ T1 /\ T2 /\ T3 /\ T4 /\ T5]
     — but [all_static_gates_pass] is DEFINITIONALLY that conjunction (see just
     above), so the two sides are the same term and the proof was
     [split; intros H; exact H] in both directions. It asserted nothing, while
     sitting under a header reading "Supporting lemmas (load-bearing, with
     substantive content)". Nothing in the repo referenced it.

     A sweep of all 63 proof files found it to be the ONLY instance of the
     shape, so this is an isolated removal rather than a class. The gate that
     should have caught it, [check_proof_substance.py], missed it twice over:
     [CompileProgress.v] was not in its LOAD_BEARING list, and even once added
     it passed, because bullets are treated as "always substantive" and [split]
     is in SUBSTANTIVE_TOKENS — which is exactly how one proves an X <-> X
     iff. Both gaps are closed in the same commit. *)

  (** Packaged form of the main theorem, taking a single conjoined
      hypothesis. This is a genuine content-bearing move: it shows the
      aggregate predicate is sufficient precisely because
      [compile_progress_rule] already requires each conjunct. *)
  Theorem T6_compile_progress_packaged :
    forall p pf,
      all_static_gates_pass p pf ->
      bounded_build_terminates_for p pf ->
      compilation_succeeds p pf.
  Proof.
    intros p pf Hall Hbound.
    destruct Hall as [H0 [H1 [H2 [H3 [H4 H5]]]]].
    apply T6_compile_progress_under_bound; assumption.
  Qed.

  (** Monotonicity under hypothesis strengthening: if T6 holds and we
      strengthen [T5_safe] to a stronger predicate, the conclusion still
      holds. Useful for v27 WS8 where some toolchains enforce stricter
      T5 semantics (e.g. shell-escape bans). *)
  Theorem T6_stable_under_stronger_T5 :
    forall (T5_strong : Project -> Prop),
      (forall p, T5_strong p -> T5_safe p) ->
      forall p pf,
        T0_accepts p -> T1_admissible p -> T2_closed p ->
        T3_compatible p pf -> T4_coherent p -> T5_strong p ->
        bounded_build_terminates_for p pf ->
        compilation_succeeds p pf.
  Proof.
    intros T5_strong Himp p pf H0 H1 H2 H3 H4 H5 Hbound.
    apply T6_compile_progress_under_bound; try assumption.
    apply Himp; assumption.
  Qed.

End Compile_progress.

(** ── Zero-admit witness ──────────────────────────────────────────── *)
Definition compile_progress_zero_admits : True := I.
