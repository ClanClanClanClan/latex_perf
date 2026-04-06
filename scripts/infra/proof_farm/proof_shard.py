#!/usr/bin/env python3
"""Proof sharding for parallel CI compilation (spec W86-91).

Assigns .v proof files to shards (round-robin by file index).
Used by proof.yml CI matrix and k8s proof-farm.

Usage:
    python proof_shard.py <shard_index> <total_shards>

Example:
    python proof_shard.py 0 8  # list files for shard 0 of 8
    python proof_shard.py 3 8  # list files for shard 3 of 8

Output: one .v file path per line (for xargs or direct iteration).
"""

import glob
import sys
from pathlib import Path


def collect_proof_files() -> list[str]:
    """Collect all .v files from proofs/ and proofs/generated/."""
    files = []
    for pattern in ["proofs/*.v", "proofs/generated/*.v"]:
        files.extend(sorted(glob.glob(pattern)))
    # Exclude archived/disabled files
    files = [f for f in files if ".disabled" not in f and "archive" not in f]
    return sorted(files)


def assign_shard(files: list[str], shard_index: int, total_shards: int) -> list[str]:
    """Round-robin assignment of files to shards."""
    return [f for i, f in enumerate(files) if i % total_shards == shard_index]


def main():
    if len(sys.argv) != 3:
        print(f"Usage: {sys.argv[0]} <shard_index> <total_shards>", file=sys.stderr)
        sys.exit(1)

    shard_index = int(sys.argv[1])
    total_shards = int(sys.argv[2])

    if shard_index < 0 or shard_index >= total_shards:
        print(f"Error: shard_index must be in [0, {total_shards})", file=sys.stderr)
        sys.exit(1)

    all_files = collect_proof_files()
    shard_files = assign_shard(all_files, shard_index, total_shards)

    print(f"# Shard {shard_index}/{total_shards}: {len(shard_files)} of {len(all_files)} files",
          file=sys.stderr)

    for f in shard_files:
        print(f)


if __name__ == "__main__":
    main()
