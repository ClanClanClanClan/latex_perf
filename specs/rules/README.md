# LaTeX Perfectionist v27.0.x — Rules Directory

## Files

- `rules_v3.yaml` — Unified, authoritative ruleset (660 rules, 644 non-reserved, 16 reserved)
- `rule_contracts.yaml` — Per-rule execution/proof/project metadata (PR #237; source of truth for runtime DAG)
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

> Counts mirror `rules_v3.yaml` (the unified ruleset).  Regenerate via
> `python3 scripts/tools/generate_project_facts.py` if `rules_v3.yaml` grows
> or shrinks; the canonical `total_specified` lives in
> `governance/project_facts.yaml`.

- Total rules: 660
- By layer (exact):
  - L0_Lexer: 192
  - L1_Expanded: 180
  - L2_Ast: 102
  - L3_Semantics: 116
  - L4_Style: 70
- By default severity:
  - Error: 49
  - Warning: 231
  - Info: 380
- Maturity:
  - Draft: 619
  - Implemented: 19
  - Impl: 6
  - Reserved: 16 (future families; do not implement yet)
- Fix producers (`produces_fix: true` in `rule_contracts.yaml`): 101 as of
  v27.1.2.  See `../v27/V27_FIX_PRODUCER_CADENCE.md` for cadence and
  `../v27/FIX_PRODUCER_LEDGER.md` for the per-rule shipping ledger.

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
