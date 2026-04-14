#!/usr/bin/env bash
# Release automation for LaTeX Perfectionist v25 (spec J-9)
#
# Usage:
#   scripts/release.sh 25.0.0           # full release
#   scripts/release.sh 25.0.0 --dry-run # verify without committing
set -euo pipefail

VERSION="${1:?Usage: release.sh <version> [--dry-run]}"
DRY_RUN="${2:-}"
TAG="v${VERSION}"

echo "[release] Preparing ${TAG}..."

# 1. Update version in dune-project
echo "[release] Updating dune-project version..."
sed -i.bak "s/^(version .*)/(version ${VERSION})/" dune-project
rm -f dune-project.bak

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

# 7. Commit version bump
echo "[release] Committing version bump..."
git add dune-project latex-perfectionist.opam latex-parse/latex_parse.opam
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
