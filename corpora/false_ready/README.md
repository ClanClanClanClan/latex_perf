# `corpora/false_ready/` — the known false-READY regression corpus (R7-INFRA-1)

Each fixture here is a document where `validators_cli --compile-check` reports
**READY (exit 0)** but **pdflatex rejects it** under the strict READY oracle
(clean single pass, no LaTeX Error — `docs/COMPILATION_GUARANTEE.md` SO1). Every
one is a confirmed finding of the round-7 deep code audit
(`docs/v27/AUDIT_R7_FIX_PLAN.md`), verified against pdfTeX / TeX Live 2026.

**This corpus is deliberately NOT under `corpora/compile_check/`** — it must not
perturb the flat differential matrix (`scripts/tools/diff_compile_check.sh`) nor
the recursive front-end parity sweep (`test_body_token_frontend.ml`), both of
which are scoped to `lint`/`compile_check`.

## The two gates

- **`scripts/tools/check_known_false_ready.py`** — the CI gate (runs in the
  `build` job). CLI-only, **no TeX needed**: the pdflatex ground truth is baked
  into `manifest.json`. It fails on either direction of drift:
  - a fixture recorded as fixed (`expected_cli: NOT-READY`) becomes READY again
    (**regression**), or
  - a fixture recorded as live (`expected_cli: READY`) becomes NOT-READY
    (**an unrecorded fix** — update the manifest to lock the win in).
- **`scripts/tools/false_ready_oracle.sh`** — the local drift guard (needs
  pdflatex). Re-runs the real oracle and checks each fixture's observed grade
  still matches the manifest's `pdflatex` field. Run before a release or after a
  TeX Live upgrade.

## Workflow for a fix PR

When a round-7 fix rank lands, for each fixture it closes: set that entry's
`expected_cli` to `NOT-READY` in `manifest.json` and lower
`baseline.false_ready_total`. The gate then holds the win permanently — the
false-READY count is monotone-decreasing and can never silently climb.

## Manifest fields

`pdflatex`: `strong-fatal` = no PDF even under `nonstopmode`; `error-halt` =
fails `-halt-on-error` / emits a LaTeX Error but limps to a PDF under
`nonstopmode` (still a false-READY under the strict oracle). `fix_rank` points
at the fix-program rank in `AUDIT_R7_FIX_PLAN.md`. `class` is the audit belt
(input-model-divergence / closed-world / capacity / glue-polarity).

## Baseline (this commit)

21 confirmed false-READY fixtures — 13 strong-fatal, 8 error-halt — spanning
fix ranks 1, 2, 4, 5, 6, 7. Multi-file cases (`fr_dir_target`, `fr_two_cycle`,
`fr_fatal_bbl`, `fr_corrupt_aux`) are subdirectories rooted at the file named in
the manifest `path`. The large capacity fixtures (100k-label main-memory,
>buf_size single line) are deferred to the rank-6 PR that closes them.

Regenerate/verify the ground truth with `false_ready_oracle.sh`; the fixtures
themselves are static and hand-reviewed.
