# ADR-010 — Park WS10/WS11 (collaboration & platform), keep the project compatible

**Status:** Accepted (2026-07-12). **Deciders:** maintainer.

## Context
WS10 (Collaboration & review) and WS11 (Platform roles/permissions/deployment) —
the Overleaf-like multi-user collaborative platform layer — are a product commitment
not yet decided. The rest of Tier 4 (WS9 editorial policy, WS12 extension plane) is
in scope and delivered (Stage 1 + Stage 2 each).

## Decision
**Park WS10/WS11 for potential later development — do NOT build now, do NOT give up.**
The engine and its surfaces must remain *compatible* with adding a collaborative
platform later, so a future WS10/WS11 is an additive layer, not a rewrite.

## Compatibility requirements to preserve (so WS10/WS11 can be added later)
- **Stable anchors:** findings/edits are keyed by CST/project-graph spans
  (`Cst`, `Stable_spans`, byte-lossless CST) — the substrate WS10 "stable anchors
  backed by CST/project graph" needs. Keep byte-lossless CST + stable spans intact.
- **Review state already externalized:** WS9 Stage 2 `editorial_review.ml`
  (review states + owner + audit trail, `.lpreview`) is the single-user precursor of
  WS10 review threads / accept-reject; keep it decoupled from the core linter (it is:
  applied post-`run_all`, default output byte-identical).
- **Deterministic, side-effect-free core:** `Validators.run_all` is pure over source +
  contexts; WS10 merge/rebase semantics require deterministic results under supported
  conditions — keep the core free of hidden mutable global state beyond the explicit
  `*_context` modules that are cleared per run.
- **Policy/permission seam:** WS9 policy + WS12 contracts are config-module + CLI-flag
  layers that never change default output — WS11 roles/permissions can extend the same
  seam. Do not bake auth/roles into the core.
- **No format lock-in:** `.lppolicy`/`.lpreview`/extension manifests are line/JSON
  configs; a collaborative backend can adopt them without engine changes.

## Consequences
Mandate is complete except this parked layer. Revisit when the product decision is made;
this ADR is the compatibility contract to check against.
