# LaTeX Perfectionist v25 — Rules Directory

## Files

- `rules_v3.yaml` — Unified, authoritative ruleset (623 rules)
- `rules_unified.cache.pkl` — Cached index for tooling (generated)
- `phase1/` — Coq spec stubs for early L0 rules (typography/commands)
- `phase1_5/` — Coq spec stubs for early L1 post‑expansion rules

## Organization (by precondition layer)

- `L0_Lexer` — Lexical analysis (pre‑AST)
- `L1_Expanded` — Post‑macro expansion
- `L2_Ast` — AST‑aware validation
- `L3_Semantics` — Semantic/meaning checks
- `L4_Style` — Style and formatting

## Catalog Snapshot (rules_v3.yaml)

- Total rules: 623
- By layer (exact):
  - L0_Lexer: 187
  - L1_Expanded: 158
  - L2_Ast: 96
  - L3_Semantics: 112
  - L4_Style: 70
- By default severity:
  - Error: 46
  - Warning: 206
  - Info: 371
- Maturity:
  - Draft: 607
  - Reserved: 16 (future families; do not implement yet)

## Implementation Guidance (When to Start)

- Gate on runtime baselines first
  - Rebuild L0 runtime + catcodes and re‑establish perf α gate (README Targets)
  - Keep proofs at 0 admits for core L0 modules
- Pilot before scale
  - Start with a small, high‑impact L0 subset (10–20 Error/Warning rules)
  - Wire into the `latex-parse` service path behind a feature flag
- Align layer to precondition
  - Implement only `L0_Lexer` rules until the L1 expander is production‑ready
  - Defer `L1_Expanded` rules until L1 macro expander ships (Q2 timeline)
  - Defer `L2_Ast`/`L3_Semantics` until parser/semantics land
- Proof posture
  - Provide soundness lemmas for L0 pilots (pattern in `phase1/TypoRules.v`)
  - Keep “Reserved” families out of scope
- Quality gates
  - Add per‑batch false‑positive review, perf smoke (p95 budgets), and golden tests

See also: `docs/RULES_IMPLEMENTATION_PLAN.md` for the rollout roadmap and definitions of ready/done.

## Pilot (Runtime)

- A pilot set of 10 L0 rules is wired into the REST façade behind `L0_VALIDATORS`.
- Files:
  - `specs/rules/pilot_v1.yaml` — enumerates the pilot rules
  - `specs/rules/pilot_v1_golden.yaml` — golden mapping file → expected IDs
  - `corpora/lint/pilot_v1/` — sample inputs per rule
- Usage: see `docs/VALIDATORS_RUNTIME.md` and README “Pilot Smoke”.
