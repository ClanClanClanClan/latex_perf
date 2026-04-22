# ADR-007: Compile-guarantee stack (T0–T7) ships in v26.2, not v27

- **Status:** Accepted (2026-04-22)
- **Context owner:** v26.2 architectural decisions (plan §2.7)

## Context

Memo §5 defines the compilation-guarantee theorem stack T0–T7. The memo
itself is ambiguous about timing — §16.3 doesn't list it for v26.2,
but §17 (v27) mentions it under WS8. Two reasonable readings:

1. T0–T7 is v27 scope; v26.2 doesn't touch it.
2. T0–T7 needs to START in v26.2 so v27 has scaffolding to build on.

## Decision

**Ship compile-guarantee scaffolding + T0–T5 mechanized wrappers + T6/T7
hypothesis-parametric proofs in v26.2.** Discharge the T6/T7 hypotheses
in v27 WS8 with a concrete toolchain model.

Concrete v26.2 deliverables (PRs A1–A3):

- **A1:** `specs/v26/compilation_guarantee_stack.md`, `compilation_profiles.yaml`.
- **A2:** `project_model.{ml,mli}`, `build_graph.{ml,mli}`,
  `aux_state.{ml,mli}`, `compile_contract.{ml,mli}`.
- **A3:** `T0_wrapper.v` / `T1_wrapper.v` / `T4_wrapper.v` / `T5_wrapper.v`
  (reuse existing proofs); `ProjectClosure.v` (T2); `BuildProfileSound.v`
  (T3); `CompileProgress.v` (T6); `CompileWellFormed.v` (T7); per ADR-004.

## Alternatives considered

- **Option A: Defer all of §5 to v27 (strict memo-§17 reading).**
  Leaves v26.2 compile_contract module without a formal backing. Users
  of compile_contract have no theorem to cite. Rejected.
- **Option B: Ship runtime modules in v26.2, all proofs in v27.**
  Runtime without proofs is fine pragmatically, but v27 WS8 then has
  to do proof AND integration work at once. Better to front-load the
  proof structure. Rejected.
- **Option C: Full discharge (concrete toolchain model) in v26.2.**
  Toolchain modelling is multi-week work that expands v26.2 scope
  beyond the memo §16.3 scope. Rejected — out of budget.

## Consequences

- v26.2 plan Track A has 3 PRs (A1/A2/A3) of increasing complexity.
- v27 WS8 focuses on instantiation + hypothesis discharge, not from-
  scratch proof work.
- `proofs/ADMISSIBILITY_MAP.md` serves as the handoff document from
  v26.2 A3 → v27 WS8.
- By shipping v26.2 as planned, we effectively deliver v27 WS7 (CST
  substrate) AND WS8 scaffolding. v27 reduces to WS9/10/11/12.
