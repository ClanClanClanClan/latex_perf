# LaTeX Perfectionist v25 — Risk Register

Canonical risk register per v25 master plan section 2.3.
CI badge turns red if any Residual >= 4.

**Last reviewed:** 2026-04-02 (Week 80)
**Next review:** 2026-05-05 (first Monday of May)

## Scoring

- **P** (Probability): L=Low, M=Medium, H=High
- **I** (Impact): L=Low, M=Medium, H=High
- **Score**: P x I (L=1, M=2, H=3) → max 9
- **Residual**: Score after mitigations applied
- **C** (Critical): Y = requires immediate escalation if triggered

## Register (33 risks)

| # | Area | Risk | P | I | Score | Residual | C | Mitigation | Status |
|---|------|------|---|---|-------|----------|---|------------|--------|
| T-1 | Tech | Pattern-mining over-generalises → FP increase | M | H | 6 | 3 | N | FP review queue per batch; ML confidence gating ≥ 0.95 | Active |
| T-2 | Tech | Coq 8.20 upgrade breaks proofs | M | H | 6 | 3 | N | Pin Coq 8.18.0; test upgrade in branch before merge | Active |
| T-3 | Tech | Incremental parser O(n²) corners | M | M | 4 | 2 | N | Dirty-window cap at 16 KiB; suffix-array fallback | Active |
| T-4 | Tech | Unicode RTL segmentation bug | M | M | 4 | 2 | N | Property-based fuzz on RTL/CJK inputs; golden tests | Active |
| T-5 | Tech | SIMD feature mis-detect on exotic ARM | L | M | 2 | 1 | N | Runtime feature detection; auto-disable if slower | Active |
| T-6 | Tech | GPU cold-start prototype starves CPU | L | M | 2 | 1 | N | GPU off-load is optional (Week 141+); CPU path primary | Deferred |
| S-1 | Sec | FFI dependency CVE | M | M | 4 | 2 | Y | SBOM via CycloneDX; Dependabot alerts; Cosign signing | Active |
| S-2 | Sec | Supply-chain attack via opam pin | L | H | 3 | 2 | Y | No opam pins; deps from opam-repository only | Mitigated |
| L-1 | Legal | Upstream licence revoked / DMCA | L | H | 3 | 2 | Y | SPDX manifest; corpus from permissive sources only | Active |
| L-2 | Legal | GDPR: accidental PII in corpus | M | M | 4 | 2 | Y | Corpus cleaning SOP; no real names in test data | Active |
| C-1 | Comp | Regulatory drift (EU AI Act) | L | M | 2 | 2 | Y | Monitor regulatory changes; ML component is advisory only | Active |
| Q-1 | Qual | FP spike after ML batch | M | H | 6 | 3 | N | ML confidence gating; per-batch FP review; rollback path | Active |
| Q-2 | Qual | Proof debt resurfaces | M | M | 4 | 2 | N | Zero-admit CI gate; @proof-debt deadline mechanism | Mitigated |
| Q-3 | Qual | Validator fix-ordering overlap | L | M | 2 | 1 | N | Conflict-resolution DAG; priority tuple ordering | Active |
| O-1 | Ops | Proof-farm outage | M | M | 4 | 2 | N | Local dune build fallback; k8s auto-restart | Active |
| O-2 | Ops | Disk-space exhaustion | M | L | 2 | 1 | N | Repo size < 200 MB policy; .gitignore coverage | Mitigated |
| O-3 | Ops | Proof-cache mismatch | L | M | 2 | 1 | N | Cache key includes Coq version + _CoqProject hash | Active |
| O-4 | Ops | S3 permission drift | L | M | 2 | 1 | N | IAM policy review quarterly | Active |
| O-5 | Ops | Backup/restore failure → data loss | L | H | 3 | 2 | Y | Git + GitHub as primary; local clones as backup | Active |
| B-1 | Biz | Solo-developer burnout | M | H | 6 | 3 | N | Weekly cadence; buffer days; clear milestone boundaries | Active |
| B-2 | Biz | Funding gap for compute | L | M | 2 | 1 | N | CPU baselines as fallback; A100 access via Colab/grants | Active |
| B-3 | Biz | Key-person outage >= 1 week | L | H | 3 | 2 | N | Documentation-first approach; ARCHITECTURE.md maintained | Active |
| R-1 | Res | Pattern-mining research stagnates | L | H | 3 | 2 | N | v2 candidate pipeline as alternative to BERT; CPU baselines | Active |
| E-1 | Eth | Dialect bias in NLP | M | M | 4 | 2 | Y | 21-language target; fairness metrics per language pack | Active |
| P-1 | Perf | 2 ms target unrealistic | L | M | 2 | 1 | N | Retired; tiered targets (20ms scalar, 8ms SIMD) | Mitigated |
| P-2 | Perf | Cache-thrash on > M docs | M | M | 4 | 2 | N | Arena allocator; monotone bump + whole-arena free | Active |
| P-3 | Perf | L4 NLP exceeds CJK budget | M | M | 4 | 2 | N | Per-language timing budget; incremental NLP diff engine | Active |
| P-4 | Perf | Domain parallelism < linear | M | M | 4 | 2 | N | Benchmark before shipping; fallback to sequential | Active |
| P-5 | Perf | Bigarray optimisations raise GC pressure | L | M | 2 | 1 | N | GC tuning; minor heap 128 MB; benchmark after changes | Active |
| X-1 | Ext | New TeX engine primitives in LuaTeX 2.0 | L | M | 2 | 1 | N | Monitor LuaTeX releases; lexer extensibility design | Active |
| X-2 | Ext | spaCy v5 file-format shifts | M | L | 2 | 1 | N | Pin spaCy version; test upgrade in branch | Active |
| I-1 | Inf | GitHub Actions minutes exhausted | M | L | 2 | 1 | N | Timeout caps on all 30 workflows; cache heavy builds | Active |
| D-1 | Doc | Documentation backlog | M | L | 2 | 1 | N | Docs site (mkdocs) planned; README kept current | Active |

## Summary

| Residual | Count | IDs |
|----------|-------|-----|
| 3 | 4 | T-1, T-2, Q-1, B-1 |
| 2 | 14 | T-3, T-4, S-1, S-2, L-1, L-2, C-1, Q-2, O-1, O-5, B-3, R-1, E-1, P-2, P-3, P-4 |
| 1 | 13 | T-5, T-6, Q-3, O-2, O-3, O-4, B-2, P-1, P-5, X-1, X-2, I-1, D-1 |

**Maximum residual: 3** (below 4 threshold — CI badge remains green)
