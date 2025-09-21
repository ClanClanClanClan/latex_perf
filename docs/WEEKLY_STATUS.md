Weekly Status (Weeks 0–7)
=========================

Week 0 — Bootstrap
- Minimal repo layout (latex-parse/, core/, proofs/, scripts/, specs/) and dune build green
- REST façade scaffolded; basic endpoints and smoke harness

Week 1 — Baseline + Zero‑Admit
- `dune build` green for latex-parse/
- Proofs: 0 admits for core stubs
- Performance baseline measured and recorded

Week 2–3 — Runtime Reconciliation & Catcode
- Catcode classifier restored and aligned with Data.Types.Catcode
- Benches runnable; perf_smoke numbers refreshed
- Docs updated with baseline results

Week 4 — Proofs (Foundations)
- L0 small‑step and segmented control models ported; window lemmas established
- Coq imports normalized for stable CI loadpath

Week 5 — Performance α Gate
- perf_smoke and edit‑window benches wired; gate scripts present
- Nightly perf job activated (gating on p95 < 20 ms, median-of-100); badge published to gh-pages

Week 6 — Validators (Pilot)
- Pilot L0 rules enabled behind `L0_VALIDATORS=pilot`
- CLI and REST smokes for pilot rules
- Message alignment added for core pilot IDs

Week 7 — Unicode + L1 + CI Gates
- Unicode token‑aware heuristics made paragraph‑aware; positive/negative goldens
- Dune unicode path flipped to uutf; fallback removed
- L1 expander summary (post_commands + spans) exposed under `L0_DEBUG_L1`
- L1 rules added: EXP‑001 (incomplete expansion), MOD‑001/2/3/4 (modernization)
- Goldens and corpora added; smokes enforce exact IDs + messages
- Proof progress in `LexerIncremental.v`: outside‑edits + window corollaries
- CI: proof-ci (Coq) added; Unicode/L1/pilot smokes enforce messages; branch-protection workflow provided

Next (Week 8)
- Expand proofs for incremental determinism and locality with a faithful L0 relation
- Activate nightly perf gates; monitor regressions (full-doc p95, edit-window p95, first-token p95)
- Gradually broaden message checks to remaining rules as wording stabilizes

Week 8 — Proof β Gate (CI wiring)
- Proof CI enforces zero admits and zero axioms across `proofs/`
- Proof regression alert workflow opens GitHub issues on failures

Week 9 — Performance β Gate (CI wiring)
- Performance Gate CI added as required check (quick gates on PRs)
- Nightly perf gates run full suite and open issues on regression
- Badges and rolling history published on gh-pages

Week 10 — Proof β Gate (enforced)
- Branch protection can enforce required checks (proof/perf/smokes)
- Proof β Gate now effective via required Proof CI (Coq)
