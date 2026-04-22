# v26.2 rollback drill

Concrete procedures for two failure modes: a bad v26.2.0 tag and
`--apply-fixes` source corruption.

## Scenario 1 — v26.2.0 tag reveals critical bug (post-publish)

**Assumption:** a user reports that v26.2.0 breaks their document
within 24h of tag.

### Step 1 — triage (30 min)
- Reproduce from a clean checkout of `v26.2.0`.
- Classify: blocker (corruption, crash on valid input, severe perf) vs
  non-blocker (edge case, documentation, minor UX).
- Non-blocker → document, roll into v26.2.1 batch.
- Blocker → Step 2.

### Step 2 — hotfix branch (1 hour)
```bash
git checkout v26.2.0
git checkout -b v26.2.1-hotfix
# minimal fix, targeted at the reproducer
```

### Step 3 — validate (1 hour)
- Run `pre_release_check.py` (must pass).
- Run `test_l2_gate` (perf ratchet).
- Add regression test that reproduces the user's failure and now passes.
- Run differential test against v26.1.0 and v26.2.0 on corpus — expect
  identical output except at the reproducer input.

### Step 4 — ship v26.2.1 (30 min)
```bash
bash scripts/release.sh 26.2.1 --dry-run
bash scripts/release.sh 26.2.1
git push origin v26.2.1-hotfix:main   # or a hotfix PR merged
git push origin v26.2.1
```

### Step 5 — announce
- Release notes published.
- If communication plan in effect, post alpha-channel notice.
- Update `README.md` recommended version.

**Total time budget:** 3 hours from reporter → published v26.2.1.

**Gotcha:** `release.sh` requires clean tree. Commit the hotfix first.

## Scenario 2 — `--apply-fixes` corrupts user source

**Assumption:** user runs `validators_cli --apply-fixes doc.tex`, the
tool writes a modified file, and later the user discovers the rewrite
was wrong.

### v26.2 must ship with these guards:

1. **Backup before write.** Every `--apply-fixes` invocation writes
   `doc.tex.bak-<timestamp>` before modifying `doc.tex`. CLI prints
   the backup path.

2. **Atomic per-file writes.** Write to `doc.tex.tmp`, fsync, rename
   over `doc.tex`. No partial writes on crash.

3. **Multi-file projects: all-or-nothing.** If `--project root.tex`
   produces fixes for 5 files, either all 5 write successfully or zero
   do. Use a staging directory + atomic rename pattern.

4. **Refuse on conflict.** If two rules produce overlapping
   `Cst_edit.edit` on the same span, `--apply-fixes` fails with a
   clear message listing the conflict. User must `--apply-fixes` a
   subset. No silent merge.

5. **Refuse on parse failure.** After applying fixes, re-parse the
   result. If it fails to parse where the original did, abort and
   restore from backup. No corruption reaches disk.

### Restore procedure (user-driven)

```bash
# User sees broken output, wants to revert:
mv doc.tex.bak-<timestamp> doc.tex
# Or for multi-file:
for f in *.tex.bak-<timestamp>; do mv "$f" "${f%.bak-*}"; done
```

Document this in `docs/MIGRATION_v26.1_to_v26.2.md`.

## Scenario 3 — release.yml fails silently

**Assumption:** `scripts/release.sh 26.2.0` runs to completion locally,
git tag pushed, but GitHub Actions `release.yml` fails to publish
artefacts (SBOM, Cosign, Docker push).

### Detection (MUST check within 10 min of push)
```bash
gh run watch --exit-status
# If red: release workflow failed.
```

### Recovery

Options in order of preference:
1. **Rerun release.yml** (GitHub UI → rerun failed jobs). Usually
   transient.
2. **Manually publish artefacts** (via `scripts/manual_release.sh`, to
   be created as part of A0 if not already in tree).
3. **Abandon v26.2.0 and cut v26.2.1 immediately** (if the workflow
   failure is structural, not infrastructure).

### Prevention (PR A0 task)
- Add a `.github/workflows/release.yml` dry-run step that catches
  credential or config errors BEFORE tag push.
- Add a smoke test: after release.yml success, try `docker pull
  ghcr.io/.../latex-perfectionist:26.2.0` — fail the post-release
  check if the image isn't pullable.

## When to drill

- Before v26.2.0 tag: execute Scenario 3 steps with a throwaway tag
  `v26.2.0-drill` on a fork.
- Before v26.2.0-alpha1 tag: execute Scenario 1 steps with a
  hypothetical bug to time the 3-hour budget.

**Drill is a prerequisite in PR C** acceptance criteria.
