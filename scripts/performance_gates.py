#!/usr/bin/env python3
"""
DEPRECATED performance gates runner.
Delegates to native bash scripts instead of custom Python logic.
"""
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).parent.parent

def main():
    print("[performance_gates] DEPRECATED: use scripts/run_all_gates.sh")
    cmd = ["bash", "scripts/run_all_gates.sh", "corpora/perf/perf_smoke_big.tex", "corpora/perf/edit_window_4kb.tex", "100"]
    print("[performance_gates] → ", " ".join(cmd))
    rc = subprocess.call(cmd, cwd=ROOT)
    sys.exit(rc)

if __name__ == "__main__":
    main()
