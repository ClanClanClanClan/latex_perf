#!/usr/bin/env bash
# Release automation for LaTeX Perfectionist (spec J-9)
#
# Usage:
#   scripts/release.sh 26.1.0           # full release
#   scripts/release.sh 26.1.0 --dry-run # verify without committing
set -euo pipefail

VERSION="${1:?Usage: release.sh <version> [--dry-run]}"
DRY_RUN="${2:-}"
TAG="v${VERSION}"

echo "[release] Preparing ${TAG}..."

# 0. PR #241 (p1.3): pre-flight — refuse to release with a dirty tree.
# A release cut from uncommitted state can embed local experiments into the
# tag. The only safe state is: every file either committed or explicitly
# .gitignored.
if [[ -n "$(git status --porcelain)" ]]; then
  echo "[release] FATAL: working tree has uncommitted changes:" >&2
  git status --porcelain >&2
  echo "[release] Commit or stash before releasing." >&2
  exit 1
fi
echo "[release] Working tree clean ✓"

# 1. Update version in dune-project
echo "[release] Updating dune-project version..."
sed -i.bak "s/^(version .*)/(version ${VERSION})/" dune-project
rm -f dune-project.bak

# 1b. PR #241 (p1.3): regenerate governance + rule contracts so the release
# tag points to a self-consistent source tree. Without this the release could
# ship with stale project_facts.yaml or rule_contracts.yaml (drift gates
# would then fail CI on the release branch).
echo "[release] Regenerating governance/project_facts.yaml..."
python3 scripts/tools/generate_project_facts.py > /dev/null
echo "[release] Regenerating specs/rules/rule_contracts.{yaml,json}..."
python3 scripts/tools/generate_rule_contracts.py 2>&1 | tail -3
echo "[release] Running drift gates..."
python3 scripts/tools/check_repo_facts.py --facts governance/project_facts.yaml --repo . > /dev/null
python3 scripts/tools/check_rule_contracts.py > /dev/null
python3 scripts/validate_catalogue.py > /dev/null
echo "[release] Governance + contracts in sync ✓"

# 2. Regenerate opam files
echo "[release] Regenerating opam files..."
opam exec -- dune build latex-perfectionist.opam latex-parse/latex_parse.opam 2>/dev/null || true

# 3. Build
echo "[release] Building..."
opam exec -- dune build @all

# 4. Run tests
echo "[release] Running tests..."
opam exec -- dune runtest

# 5. Verify zero admits
echo "[release] Checking zero admits..."
if grep -rn "Admitted\." proofs/ --include="*.v" | grep -v archive | grep -v "\.disabled"; then
  echo "[release] FATAL: Admitted found in proofs"
  exit 1
fi
echo "[release] Zero admits confirmed"

# 6. Generate SBOM (if trivy available)
if command -v trivy &>/dev/null; then
  echo "[release] Generating SBOM..."
  trivy fs --format cyclonedx --output sbom-cyclonedx.json . 2>/dev/null
  echo "[release] SBOM: sbom-cyclonedx.json"
else
  echo "[release] SKIP: trivy not found (SBOM generated in CI)"
fi

if [[ "$DRY_RUN" == "--dry-run" ]]; then
  echo ""
  echo "[dry-run] Would commit: dune-project, opam files"
  echo "[dry-run] Would tag: ${TAG}"
  echo "[dry-run] All checks passed ✓"
  # Revert version change
  git checkout dune-project 2>/dev/null || true
  exit 0
fi

# 6b. PR #245 (p1.11): pre-release uber-gate before any state mutation.
# Runs EVERY gate + full build + all tests. Fails fast if ANY check
# is red. Skipped in --dry-run (the user is expected to have run this
# manually before invoking release.sh).
if [[ "$DRY_RUN" != "--dry-run" ]]; then
  echo "[release] Running pre-release uber-gate (all gates + build + tests)..."
  if ! python3 scripts/tools/pre_release_check.py --allow-dirty --skip-build; then
    echo "[release] FATAL: pre-release gates failed. Aborting." >&2
    exit 1
  fi
  echo "[release] Pre-release gates ✓"
fi

# 7. Commit version bump
echo "[release] Committing version bump..."
git add dune-project latex-perfectionist.opam latex-parse/latex_parse.opam \
  governance/project_facts.yaml specs/rules/rule_contracts.yaml \
  specs/rules/rule_contracts.json
git commit -m "chore: bump version to ${VERSION}"

# 8. Tag
echo "[release] Tagging ${TAG}..."
git tag -a "${TAG}" -m "Release ${TAG}"

echo ""
echo "═══════════════════════════════════════════════"
echo "  Release ${TAG} prepared ✓"
echo "═══════════════════════════════════════════════"
echo ""
echo "Next steps:"
echo "  git push origin main"
echo "  git push origin ${TAG}"
echo ""
echo "This triggers:"
echo "  - .github/workflows/release.yml (SBOM + Cosign + GitHub Release)"
echo "  - .github/workflows/docker-push.yml (Docker image to GHCR)"
