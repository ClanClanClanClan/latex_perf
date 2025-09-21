# Rules Implementation Plan (v25)

## Start Criteria

- Runtime baselines in place
  - L0 lexer + catcodes rebuilt and green under `latex-parse/`
  - Performance α gate re‑run and recorded (readme targets)
  - Proof posture maintained (0 admits for core L0 proofs)
- Spec stability
  - `specs/rules/rules_v3.yaml` remains the authoritative catalog (623 rules)
  - Freeze rule IDs/severity for pilot batches; no “Reserved” families

## Phase Rollout (by precondition)

- L0_Lexer (187 rules)
  - Start here. Implement 10–20 high‑signal Error/Warning rules as a pilot
  - Keep validators behind a feature flag in the service
  - Add Coq soundness lemmas following `specs/rules/phase1/TypoRules.v`
- L1_Expanded (158 rules)
  - Begin only after L1 expander is production‑ready (Q2)
  - Focus on expansion correctness and post‑expansion hygiene first
- L2_Ast (96 rules) / L3_Semantics (112 rules)
  - Blocked on parser/semantics delivery; schedule after L2/L3 land
- L4_Style (70 rules)
  - Defer until earlier layers are stable to avoid FP churn

## Prioritization

- Severity: Error → Warning → Info
- Cost: Lexical checks with narrow scope and clear auto‑fixes first
- Value: Frequent real‑world issues (quotes, dashes, tabs, trailing spaces)
- Risk: Avoid rules with broad scope or weak signals in early batches

## Batching & Quality Gates

- Batch size: 10–20 rules per drop; weekly cadence acceptable post‑gate
- Tests: Golden inputs per rule; mixed‑case corpora coverage
- Perf: Verify p95 budgets unaffected (full‑doc and 4 KB window)
- Telemetry: Track per‑rule hit rates, FP complaints, and fix uptake
- Docs: For each rule, record: ID, scope, examples, auto‑fix, FP notes

## Definitions

- Definition of Ready (per rule)
  - Precondition layer implemented (e.g., L0 runtime available)
  - Severity and message finalized; optional auto‑fix designed
  - Example corpus and expected diagnostics prepared
  - Coq lemma shape identified (for L0 pilots)
- Definition of Done (per rule)
  - Validator implemented and covered by tests
  - Optional auto‑fix implemented or explicitly deferred
  - Performance unchanged within gate; FP budget accepted
  - Documentation updated; added to rule index in service
  - Coq soundness lemma landed (where applicable)

## Near‑Term Actions (Week‑aligned)

- Week 2–5
  - Reconcile L0 runtime; re‑run perf α gate; maintain 0 admits
  - Prepare pilot list (10–20 L0 Error/Warning rules) + corpora
- Week 6–10
  - Implement L0 pilot behind a feature flag; add soundness lemmas
  - Add per‑rule telemetry and FP intake workflow
- Q2 (Weeks 14–26)
  - Expand L0 coverage in batches; begin L1 validators once expander ships
  - Establish CI gates for validators + proofs

## References

- Catalog: `specs/rules/rules_v3.yaml`
- L0 examples: `specs/rules/phase1/TypoRules.v`, `specs/rules/phase1/CommandRules.v`
- Post‑expansion examples: `specs/rules/phase1_5/PostExpansionRules.v`

