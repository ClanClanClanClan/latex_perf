#!/usr/bin/env bash
# fetch_corpora.sh — Download and verify external corpora from corpora.lock
#
# Usage:
#   bash scripts/fetch_corpora.sh [--dry-run] [--corpus NAME]
#
# Reads corpora.lock (YAML), downloads each corpus, verifies SHA-256,
# extracts to the target directory. Skips already-present corpora.

set -euo pipefail

LOCK_FILE="corpora.lock"
EXTERNAL_DIR="external_corpora"
DRY_RUN=false
FILTER_NAME=""

# Parse arguments
while [[ $# -gt 0 ]]; do
  case "$1" in
    --dry-run) DRY_RUN=true; shift ;;
    --corpus)  FILTER_NAME="$2"; shift 2 ;;
    *)         echo "Unknown argument: $1"; exit 1 ;;
  esac
done

if [[ ! -f "$LOCK_FILE" ]]; then
  echo "ERROR: $LOCK_FILE not found. Run from project root."
  exit 1
fi

mkdir -p "$EXTERNAL_DIR"

# Simple YAML parser for our fixed schema
# Extract corpus entries as name|url|sha256|format|target_dir
parse_corpora() {
  python3 -c "
import yaml, sys
with open('$LOCK_FILE') as f:
    data = yaml.safe_load(f)
for c in data.get('corpora', []):
    print(f\"{c['name']}|{c['url']}|{c['sha256']}|{c['format']}|{c['target_dir']}|{c['size_bytes']}\")
"
}

TOTAL=0
SKIPPED=0
DOWNLOADED=0
FAILED=0

while IFS='|' read -r name url sha256 format target_dir size_bytes; do
  # Filter if --corpus specified
  if [[ -n "$FILTER_NAME" && "$name" != "$FILTER_NAME" ]]; then
    continue
  fi

  TOTAL=$((TOTAL + 1))

  # Skip if already extracted
  if [[ -d "$target_dir" ]]; then
    echo "[SKIP] $name — already at $target_dir"
    SKIPPED=$((SKIPPED + 1))
    continue
  fi

  # Skip placeholder entries
  if [[ "$sha256" == "placeholder-"* ]]; then
    echo "[SKIP] $name — placeholder SHA256 (update corpora.lock with real URL)"
    SKIPPED=$((SKIPPED + 1))
    continue
  fi

  if $DRY_RUN; then
    echo "[DRY-RUN] Would download $name ($((size_bytes / 1048576)) MB) → $target_dir"
    continue
  fi

  echo "[FETCH] $name ($((size_bytes / 1048576)) MB)..."
  TMPFILE=$(mktemp)

  # Download
  if ! curl -fSL --progress-bar -o "$TMPFILE" "$url"; then
    echo "[FAIL] $name — download failed"
    rm -f "$TMPFILE"
    FAILED=$((FAILED + 1))
    continue
  fi

  # Verify SHA-256
  ACTUAL_SHA=$(shasum -a 256 "$TMPFILE" | awk '{print $1}')
  if [[ "$ACTUAL_SHA" != "$sha256" ]]; then
    echo "[FAIL] $name — SHA-256 mismatch!"
    echo "  Expected: $sha256"
    echo "  Got:      $ACTUAL_SHA"
    rm -f "$TMPFILE"
    FAILED=$((FAILED + 1))
    continue
  fi

  # Extract
  mkdir -p "$target_dir"
  case "$format" in
    tar.gz) tar xzf "$TMPFILE" -C "$target_dir" ;;
    zip)    unzip -q "$TMPFILE" -d "$target_dir" ;;
    tex)    cp "$TMPFILE" "$target_dir/" ;;
    *)      echo "[FAIL] $name — unknown format: $format"; FAILED=$((FAILED + 1)); continue ;;
  esac

  rm -f "$TMPFILE"
  echo "[OK]   $name → $target_dir"
  DOWNLOADED=$((DOWNLOADED + 1))

done < <(parse_corpora)

echo ""
echo "=== Corpus Fetch Summary ==="
echo "  Total:      $TOTAL"
echo "  Downloaded: $DOWNLOADED"
echo "  Skipped:    $SKIPPED"
echo "  Failed:     $FAILED"

if [[ $FAILED -gt 0 ]]; then
  exit 1
fi
