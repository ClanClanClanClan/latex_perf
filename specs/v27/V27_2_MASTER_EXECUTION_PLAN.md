# v27.2 Master Execution Plan — Tiers 1–3 + Candidate Pool

**Goal (per directive):** complete Tiers 1–3 *and* the candidate pool, perfectly,
then touch base. This is the single source of truth for the remaining work,
grounded in two data-driven audits (`REMAINING_FIXABILITY_AUDIT.md`,
`L3_MIGRATION_INVENTORY.md`), not spec aspiration.

## State at authoring (v27.1.21)

- 644/660 rules implemented; **166 auto-fix producers + 18 Bucket-C candidates**.
- All safety gates in CI: multi-trigger coverage (166×1013), verbatim, convergence,
  differential, code-quality, ledger.
- Pending merges: #456 (v27.1.20 depth+docs), #457 (v27.1.21 +7 producers).

## The five workstreams (data-grounded sizes)

| # | Workstream | Real size | Status |
|---|---|---|---|
| T1 | Reconcile & de-risk | small | **DONE** (README, plan banners, expert briefings, ML scope, 2 audit docs) |
| M | Finish mechanical auto-fix | 10 rules | **7 shipped** (#457); 3 infra-gated left |
| CP | Candidate pool | ~170 rules | 18 shipped; **~40–60 clean + ~50 medium + ~60 risky/hold** |
| T2 | L3-AST migration | **~6–11 rules** (not 116) | not started; scoped in inventory |
| T3 | Faithful semantics (Coq) | epic | not started; re-scoped off tag v27.1.0 |

## Execution order (value × certainty, dependency-aware)

### Phase A — land what's built + finish mechanical
1. Merge #456 → #457; tag v27.1.20, v27.1.21.
2. **M-tail (v27.1.22):** ENC-006 (overlong-UTF8 re-encode), DE-006 (Swiss ß→ss,
   locale-gated), BIB-010 (month number→macro table). Small; completes the
   auto-fix universe (166→169).

### Phase B — the candidate pool, by risk (the largest fix-coverage)
3. **CP-1 clean/render-identical (v27.1.23):** MATH bracing/reorder
   (MATH-016/019/035/047/059), DELIM sizing (DELIM-008/010), math font
   wrap/unwrap (MATH-036/048/050/087/096), SCRIPT notation bracing, MATH-058
   text-unwrap. Corruption-free candidates; each `--apply-fixes-for` byte-identical.
4. **CP-2 medium (v27.1.24–25):** differential/thin-space insertion (MATH-013/034/
   060/042/068, TYPO-011), MOD legacy font→NFSS (MOD-001..007), CMD placement
   (CMD-001/006/008/013/014), TIKZ/DOC/SPC small edits, VERB options. Review-gated;
   watch differential + verbatim-safety interactions.
5. **CP-3 risky — HOLD:** REF/BIB cross-ref & cite-key renames (atomic multi-site,
   real corruption risk), STYLE prose/punctuation & spelling-variant normalization
   (needs a review/approval UX + dictionaries). Do NOT ship until a review surface
   exists; document as the reason.

### Phase C — Tier 2 L3-AST (small refactor)
6. **T2-Stage1 (v27.2.0-a):** `ast_semantic_state.ml` — `env_node` (comment/
   verbatim-aware, nesting-correct) + `math_seg` (wrap byte-accurate
   `find_math_ranges`) + `label_entry`; do NOT duplicate `project_state.ml` or
   synthesize layout facts (those stay in `Log_parser`).
7. **T2-Stage2 (v27.2.0-b):** migrate the 6 env/math rules (MATH-076/089/103/107,
   TAB-004, CHEM-010) + REF-008/010 to AST; add a regex-vs-AST parity gate; keep
   2 green releases before deprecating the regex path. (CJK/RTL byte-scanners are
   OUT of scope — a separate line/script-context epic.)

### Phase D — Tier 3 faithful semantics (Coq epic)
8. **T3 (v27.2.x):** `tokenize` + `tokenize_preserves_byte_count` (seed from
   `proofs/LexerFaithfulStep.v`); then aux/log evolution, a *meaningful* `converged`
   flag, ≤2-pass convergence theorem, re-prove `pdflatex_compile_safe` against it.
   Retarget the stale v27.1.0 label.

## Invariants for every batch (non-negotiable)
- Producers: match ORIGINAL source; idempotent; valid-UTF-8; vcu/exempt-guarded;
  `control_word_repl` for control-word emitters; adversarial variant in the
  coverage registry (letter-adjacent + protected-preserve).
- Candidates: `produces_fix:false`; NEVER auto-apply (`--apply-fixes-for`
  byte-identical); exempt-filtered (incl. label-only self-gating).
- Every workflow: build clean-from-main (no infra dup); verify on the BUILD
  worktree (`path_match`); ground-truth negative verdicts.
- Every release: full bar (runtest, coverage, differential 0-diff or reconciled,
  convergence, verbatim, code-quality, doc-refs, version-labels, ledger).

## Definition of done
Every fixable rule has an auto-fix (Bucket A) or a reviewable candidate (Bucket C);
the ~211 diagnose-only rules stay diagnose-only by design; T2 env/math rules run on
real AST nodes; T3 gives a faithful ≤2-pass convergence theorem. Then touch base.
