# ADR-004: T6/T7 proofs use Section + Variable (not Parameter / Axiom)

- **Status:** Accepted (2026-04-22)
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
