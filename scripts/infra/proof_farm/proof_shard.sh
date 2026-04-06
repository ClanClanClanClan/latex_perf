#!/usr/bin/env bash
# Proof shard script (spec W18, W86-91)
#
# Compiles a subset of Coq proof files based on shard index.
# Used by both k8s proof-farm (32 shards) and CI matrix (8 shards).
#
# Usage:
#   bash proof_shard.sh <shard_index> <total_shards>
#
# Example:
#   bash proof_shard.sh 0 8   # compile shard 0 of 8

set -euo pipefail

SHARD_INDEX="${1:?Usage: proof_shard.sh <shard_index> <total_shards>}"
TOTAL_SHARDS="${2:?Usage: proof_shard.sh <shard_index> <total_shards>}"

echo "[proof-shard] Shard ${SHARD_INDEX} of ${TOTAL_SHARDS}"

# Collect all .v files
PROOF_FILES=()
for f in proofs/*.v proofs/generated/*.v; do
  [ -f "$f" ] && PROOF_FILES+=("$f")
done

TOTAL_FILES=${#PROOF_FILES[@]}
echo "[proof-shard] Total proof files: ${TOTAL_FILES}"

# Assign files to this shard (round-robin)
SHARD_FILES=()
for i in "${!PROOF_FILES[@]}"; do
  if (( i % TOTAL_SHARDS == SHARD_INDEX )); then
    SHARD_FILES+=("${PROOF_FILES[$i]}")
  fi
done

echo "[proof-shard] Files in this shard: ${#SHARD_FILES[@]}"

if [ ${#SHARD_FILES[@]} -eq 0 ]; then
  echo "[proof-shard] No files assigned to this shard. Done."
  exit 0
fi

# Compile each file using opam exec (for k8s/container environments)
# In CI, prefer `dune build proofs` for dependency management.
# This script is for k8s proof-farm where each pod compiles its shard.
COQC="${COQC:-opam exec -- coqc}"
FAILURES=0
for f in "${SHARD_FILES[@]}"; do
  echo "[proof-shard] Compiling: $f"
  START_TIME=$(date +%s%N)
  if $COQC -R proofs LaTeXPerfectionist \
           -R proofs/generated LaTeXPerfectionist.Generated \
           -Q core/interfaces LaTeXPerfectionist.Core \
           "$f" 2>&1; then
    END_TIME=$(date +%s%N)
    ELAPSED_MS=$(( (END_TIME - START_TIME) / 1000000 ))
    echo "[proof-shard]   OK (${ELAPSED_MS}ms)"
  else
    echo "[proof-shard]   FAIL: $f"
    FAILURES=$((FAILURES + 1))
  fi
done

echo "[proof-shard] Shard ${SHARD_INDEX}: ${#SHARD_FILES[@]} files, ${FAILURES} failures"

if [ $FAILURES -gt 0 ]; then
  echo "[proof-shard] FAILED"
  exit 1
fi

echo "[proof-shard] PASSED"
