# ADR-004: T6/T7 proofs use Section + Variable (not Parameter / Axiom)

- **Status:** Accepted (2026-04-22); **Discharged for pdflatex profile in v27.0.0** (`pdflatex_compile_safe` Qed at commit `492ff90`); T0/T1/T4/T5 wired in v27.0.1 / v27.0.2 (PRs #312 / #313→#317).
- **Context owner:** v26.2 architectural decisions (plan §2.4)

## Context

Memo §5 defines the compile-guarantee theorem stack T0–T7. T6
("compilation progress") and T7 ("output well-formedness") require
modelling the LaTeX toolchain's pass-iteration and output semantics —
non-trivial work that belongs to v27 WS8, not v26.2.

But v26.2 should SHIP the theorem structure so v27 has something to
instantiate. The theorems need unproven *input assumptions* without
violating the project's zero-axiom invariant (`admit-audit` and
`check_regression_gates`).

## Decision

**Use Coq `Section` + `Variable` / `Hypothesis` pattern.** After
`End Section`, the theorem becomes universally quantified over the
Variables. Callers instantiate the Variables with concrete values.

```coq
Section Compile_progress.
  Variable bounded_build_terminates_for : project -> profile -> Prop.
  ...
  Hypothesis compile_progress_rule : ... -> compilation_succeeds p pf.

  Theorem compile_progress_under_bound : ... .
  Proof. ... apply compile_progress_rule; assumption. Qed.
End Compile_progress.
```

**Zero `Parameter` / `Axiom` declarations.** `Variable`s inside a Section
are *not* axioms — they become parameters of the final theorem after
`End`.

## Alternatives considered

- **Option A: Declare `Parameter bounded_build_terminates_for : ...`**
  Banned by `check_regression_gates` / `proof.yml` anti-axiom gate.
  Rejected.
- **Option B: Define concretely as `True` (trivial).**
  Theorem becomes vacuously satisfied; no content. Rejected — defeats
  the purpose.
- **Option C: Use Coq Modules + Functors.**
  More verbose; same end result as Section pattern for our needs.
  Rejected as overkill.
- **Option D: Defer T6/T7 to v27 entirely.**
  Considered. Rejected because v26.2 compile_contract module ships
  runtime checkers for T0–T5; having abstract T6/T7 wrappers keeps
  the proof surface complete even if the concrete toolchain model is
  deferred.

## Consequences

- v27 WS8 writes an OCaml-style `Module PdflatexModel` that instantiates
  the Section's Variables with concrete types and discharges
  `compile_progress_rule` with a real proof.
- **Canary test required:** before A3 merges, verify the anti-axiom
  gate doesn't misfire on Section-quantified Variables. Add a minimal
  .v file with a Section pattern; run `check_regression_gates.py` and
  `admit-audit` on it.
- `proofs/ADMISSIBILITY_MAP.md` (created in A3) lists every Hypothesis
  T6/T7 rely on, serving as the entry point for v27 WS8 implementers.

## Discharge log (post-v26.2)

- **v27.0.0** (commit `492ff90`, PR #310 + #311 release-bump): WS8
  capstone delivered.  `proofs/PdflatexModel.v` instantiates both
  Section's Variables; both `compile_progress_rule` and
  `output_wellformed_rule` discharged via Qed-proved lemmas
  (`pdflatex_compile_progress_rule_proof`,
  `pdflatex_output_wellformed_rule_proof`).  Headline
  `pdflatex_compile_safe` Qed; `Print Assumptions` returns "Closed
  under the global context".  Engine-generic aliases
  `xelatex_compile_safe` / `lualatex_compile_safe` ship in v27.0.1.
- **v27.0.1** (PR #312): T0/T1/T4 wired to LP-Core wrappers
  (`T0_wrapper.T0_parser_accepts`,
  `T1_wrapper.T1_expansion_admissible_merge`,
  `T4_wrapper.T4_labels_unique_packaged`); discharge lemmas
  `pdflatex_T{0,1,4}_*_holds` Qed.
- **v27.0.2** (PRs #313→#317): T5 substantively wired via
  `proofs/T5_concrete.v` Section-parametric carriers + downstream
  `proofs/generated/PdflatexT5Wired.v` against
  `Generated.Catalogue.all_proved_rule_ids`.
- **v27.0.3** (PRs #319→#324): apply_edits associative-reorder
  cycle (orthogonal to T6/T7 but builds on the same rewrite
  engine — closes the v26.4-deferred
  `apply_edits_concrete_associative_subset` under the corrected
  name `apply_edits_parallel_perm`).

The compile-guarantee stack T0–T7 is now substantively discharged
end-to-end for the pdflatex profile; the engine-agnostic aliases
extend the carrier-level result to xelatex / lualatex profiles.
The faithful operational semantics (extending the abstract
counter-bounded pass model to real aux/log evolution) is queued
as `specs/v27/V27_FAITHFUL_SEMANTICS_PLAN.md` (target tag
v27.1.0).
