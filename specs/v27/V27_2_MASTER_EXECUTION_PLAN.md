# v27.2 Master Execution Plan — Tiers 1–3 + Candidate Pool

> **STATUS (v27.1.39): Tiers 1–3 + candidate pool COMPLETE.** The directive
> ("complete Tiers 1–3 *and* the candidate pool, perfectly, then touch base")
> is met. This doc is now a completed-plan record; forward work is the Tier 4
> scope clarified in `V27_REPO_EXACT_MASTER_SPEC.md` (WS9 + WS12 in scope; WS10
> + WS11 deferred pending a product decision).

**Goal (per directive):** complete Tiers 1–3 *and* the candidate pool, perfectly,
then touch base. This was the single source of truth for the remaining work,
grounded in two data-driven audits (`REMAINING_FIXABILITY_AUDIT.md`,
`L3_MIGRATION_INVENTORY.md`), not spec aspiration.

## Final state (v27.1.39)

- 643/660 rules implemented (17 reserved); **167 auto-fix producers + 69 Bucket-C
  candidates**. Every fixable rule has an auto-fix or a `--list-candidate-fixes`
  candidate.
- All safety gates in CI: multi-trigger coverage, verbatim, convergence,
  differential, code-quality, ledger, doc-refs, version-labels, repo-facts.
- ~1,450 theorems / 0 admits / 0 axioms; capstone `pdflatex_compile_safe` Qed,
  Closed under the global context.

## The five workstreams (final)

| # | Workstream | Real size | Status |
|---|---|---|---|
| T1 | Reconcile & de-risk | small | **DONE** (README, plan banners, expert briefings, ML scope, 2 audit docs) |
| M | Finish mechanical auto-fix | 10 rules | **DONE** — mechanical auto-fix universe exhausted (167 producers) |
| CP | Candidate pool | ~170 rules | **DONE** — 69 Bucket-C candidates shipped; risky REF/BIB/STYLE renames documented as HELD pending a review UX |
| T2 | L3-AST migration | **~6–11 rules** (not 116) | **COMPLETE** — `ast_semantic_state` module (v27.1.28) + REF migration (v27.1.36) + regex-vs-AST parity gate |
| T3 | Faithful semantics (Coq) | epic | **COMPLETE** — faithful pdflatex operational semantics, Stages 1–6 + residuals (v27.1.29–39) |

## Execution order (value × certainty, dependency-aware) — ALL PHASES COMPLETE

### Phase A — land what's built + finish mechanical — **DONE**
1. Merge #456 → #457; tag v27.1.20, v27.1.21.
2. **M-tail (v27.1.22):** ENC-006 (overlong-UTF8 re-encode), DE-006 (Swiss ß→ss,
   locale-gated), BIB-010 (month number→macro table). Small; completes the
   auto-fix universe (166→169).

### Phase B — the candidate pool, by risk (the largest fix-coverage) — **DONE** (CP-1/2 shipped; CP-3 HELD by design)
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

### Phase C — Tier 2 L3-AST (small refactor) — **COMPLETE** (`ast_semantic_state` module v27.1.28; REF migration + parity gate v27.1.36)
6. **T2-Stage1 (shipped v27.1.28):** `ast_semantic_state.ml` — `env_node` (comment/
   verbatim-aware, nesting-correct) + `math_seg` (wrap byte-accurate
   `find_math_ranges`) + `label_entry`; do NOT duplicate `project_state.ml` or
   synthesize layout facts (those stay in `Log_parser`).
7. **T2-Stage2 (shipped v27.1.36):** migrated the env/math + REF rules to AST
   nodes with a regex-vs-AST parity gate in CI. (CJK/RTL byte-scanners remain
   OUT of scope — a separate line/script-context epic.)

### Phase D — Tier 3 faithful semantics (Coq epic) — **COMPLETE** (v27.1.29–39)
8. **T3 (shipped v27.1.29–39):** `tokenize` + `tokenize_preserves_byte_count`;
   token-driven aux/log evolution; `project_tokens` with label/ref + profile +
   document-required features; a *meaningful* `converged` flag with
   warnings-iff-unresolved; a tight ≤2-pass convergence theorem + additive WS8
   bridge; a PDF-artefact model with genuine T2/T3/T4; Stage 6 re-proof of the
   WS8 capstone `pdflatex_compile_safe` (Qed, Closed, 0 admits / 0 axioms).
   See `V27_FAITHFUL_SEMANTICS_PLAN.md` for the per-stage record.

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

## Definition of done — MET (v27.1.39)
Every fixable rule has an auto-fix (Bucket A) or a reviewable candidate (Bucket C);
the diagnose-only rules stay diagnose-only by design; T2 env/math + REF rules run on
real AST nodes (parity-gated); T3 gives a faithful ≤2-pass convergence theorem with
the WS8 capstone re-proved against it. Directive complete — touched base.

**Honest remaining residuals (out of the Tiers 1–3 scope, tracked, not overclaimed):**
the T0/T1/T5 universal proof obligations and the PDF *structural* semantics remain
conservative/deferred; the faithful model covers aux/log/pass convergence and the
compile-safety capstone, not byte-exact PDF page structure.
