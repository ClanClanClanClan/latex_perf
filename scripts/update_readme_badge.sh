#!/usr/bin/env bash
set -euo pipefail

# Update README badge block with the gh-pages badge JSON endpoint.
README=README.md
REPO_SLUG=${GITHUB_REPOSITORY:-$(git remote get-url origin 2>/dev/null | sed -E 's#.*github.com[:/](.+)\.git#\1#')}
ENDPOINT="https://raw.githubusercontent.com/${REPO_SLUG}/gh-pages/public-badges/expand_latency.json"
BADGE="![Expand Latency p95](https://img.shields.io/endpoint?url=${ENDPOINT})"

awk -v badge="$BADGE" '
  BEGIN{inside=0}
  /<!-- LAT_BADGE_START -->/ {print; print badge; inside=1; next}
  /<!-- LAT_BADGE_END -->/ {print; inside=0; next}
  inside==1 {next}
  {print}
' "$README" > /tmp/README.badge && mv /tmp/README.badge "$README"

echo "[readme] Badge updated to $ENDPOINT"

