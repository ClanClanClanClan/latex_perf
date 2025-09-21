CI Required Status Checks
=========================

This repo defines the following CI workflows as required checks:

- Proof CI (Coq) / proof-ci
- Unicode Rules Smoke / unicode-smoke
- L1 Rules Smoke / l1-smoke
- Validators Pilot Smoke (CLI) / smoke-cli
- REST Smoke Test / rest-smoke
- Performance Gate CI / perf-ci
- Unit Tests / unit-tests

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
