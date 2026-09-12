CI Required Status Checks
=========================

The authority is `.github/required-status-checks.json`, which
`branch-protection.yml` PUTs on every push to main (process invariant 7).
Edit that file, never the API, and never this list on its own.

As of 2026-09-12 it holds **11** contexts:

- Build / build
- Proof CI (Coq) / proof-ci
- Unicode Rules Smoke / unicode-smoke
- L1 Rules Smoke / l1-smoke
- Validators Pilot Smoke (CLI) / smoke-cli
- REST Smoke Test / rest-smoke
- Performance Gate CI / perf-ci
- Unit Tests / unit-tests
- Spec Drift / spec-drift
- TeX Oracle (real pdflatex) / tex-oracle
- XXH64 SIMD Selfcheck / xxh-selfcheck

⚠ This document listed only the first seven of these until 2026-09-12, omitting
`build`, `spec-drift`, `tex-oracle` and `xxh-selfcheck` — the build, the whole
19-gate drift belt, the real-pdflatex oracle and the hash self-check. Anyone
following it would have switched four required contexts off. Recorded as
OPEN-085.

How to enable branch protection (recommended)
--------------------------------------------

Option A — via workflow (requires admin token):

1. Add repo secret `REPO_ADMIN_TOKEN` with admin scope (repo:admin access).
2. Trigger the workflow manually: Actions → Configure Branch Protection → Run workflow.
   - Optionally specify a branch; defaults to the repository default branch.
3. The workflow sets branch protection with the required status checks from
   `.github/required-status-checks.json` and enforces admin reviews.

Option B — manually via GitHub UI:

1. Settings → Branches → Branch protection rules → Add rule.
2. Select default branch (e.g., `main`).
3. Enable “Require status checks to pass before merging” and add the checks
   listed above exactly as contexts.
4. Enable “Include administrators” and “Require pull request reviews” ≥ 1.

Updating required checks
------------------------

- Edit `.github/required-status-checks.json` to add/remove contexts.
- Re-run the “Configure Branch Protection” workflow (Option A) or update the UI manually (Option B).
