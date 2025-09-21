#!/usr/bin/env python3
"""
DEPRECATED wrapper for performance gates.
Use the project-native bash gates instead:
  - scripts/perf_gate.sh corpora/perf/perf_smoke_big.tex 100
  - scripts/edit_window_gate.sh corpora/perf/edit_window_4kb.tex 2000
"""
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).parent.parent

def main():
    print("[perf-harness] DEPRECATED: delegating to scripts/perf_gate.sh and edit_window_gate.sh")
    runs = [
        ["bash", "scripts/perf_gate.sh", "corpora/perf/perf_smoke_big.tex", "100"],
        ["bash", "scripts/edit_window_gate.sh", "corpora/perf/edit_window_4kb.tex", "2000"],
    ]
    for cmd in runs:
        print("[perf-harness] → ", " ".join(cmd))
        rc = subprocess.call(cmd, cwd=ROOT)
        if rc != 0:
            sys.exit(rc)
    print("[perf-harness] OK")

if __name__ == "__main__":
    main()
