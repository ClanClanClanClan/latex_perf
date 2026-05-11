#!/usr/bin/env python3
"""Pre-release gate: ensure FIX_PRODUCER_LEDGER.md is in sync with the
ledger generator (which itself is in sync with the validator source).

This prevents the ledger from drifting after a new fix producer ships
without the corresponding SHIPPED_VERSIONS update.

Exits 0 on sync, non-zero on drift.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
GENERATOR = REPO_ROOT / "scripts/tools/generate_fix_producer_ledger.py"


def main() -> int:
    result = subprocess.run(
        [sys.executable, str(GENERATOR), "--check"],
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        # Re-emit the generator's stderr verbatim so users see the actionable
        # error message (mismatch / SHIPPED_VERSIONS drift).
        sys.stderr.write(result.stderr)
        return result.returncode
    print("[ledger-sync] ok: FIX_PRODUCER_LEDGER.md in sync.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
