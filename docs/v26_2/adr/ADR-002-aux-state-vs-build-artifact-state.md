# ADR-002: aux_state and build_artifact_state are distinct modules

- **Status:** Accepted (2026-04-22)
- **Context owner:** v26.2 architectural decisions (plan §2.2)

## Context

Memo §5.5 prescribes a new `aux_state.{ml,mli}` for the compilation
guarantee stack. The repo already has `build_artifact_state.{ml,mli}`
shipped in v26.0. Superficially similar names — are they the same thing?

## Decision

**They are different. Both ship, with distinct responsibilities.**

- `build_artifact_state.ml` (v26.0, ~30 LOC) — thread-local wrapper
  around `Build_profile.t`; holds a *parsed compile-log context*
  (produced by `Log_parser` and `Log_context`).
- `aux_state.ml` (v26.2, NEW, ~300+ LOC estimated) — reads and parses
  the `.aux` FILE on disk; builds a cross-reference table (`\newlabel`,
  `\bibcite`, counters, `\@LN`, etc.). pdflatex-only for v26.2.

## Alternatives considered

- **Option A: Extend `build_artifact_state` to also parse .aux.**
  Mixes two very different concerns (runtime wrapper vs. file parser)
  and makes the module non-cohesive. Rejected.
- **Option B: Rename `build_artifact_state` → `aux_state` and extend.**
  Breaking change to a v26.0-shipped module; would violate API stability.
  Rejected.

## Consequences

- Two similarly-named modules; doc `docs/FOUR_GRAPHS.md` (created in A1)
  documents the distinction alongside the graph-module disambiguation.
- `aux_state.ml` is multi-day work (~1.5 days in A2 estimate).
  Explicit scope: pdflatex-only; `.toc` / `.lof` / `.lot` / `.idx` /
  `.glg` out of scope for v26.2.
- `Compile_contract.ml` (new in A2) uses BOTH modules: `aux_state`
  for .aux content, `build_artifact_state` for log context.
