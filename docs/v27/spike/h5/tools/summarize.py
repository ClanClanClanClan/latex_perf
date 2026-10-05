#!/usr/bin/env python3
"""summarize.py RUNS_DIR RUN...: one TSV row per run from its last PROBE line, verdict and comparison
(spike H.5 stage 1). cpu is the process's own CPU time (Sys.time) at the end of the run."""
import json, re, sys
from pathlib import Path
d = Path(sys.argv[1])
cols = ["cpu", "minor", "promoted", "major", "minc", "majc", "heap", "top", "set", "get", "make",
        "reroot_steps", "stale", "live", "reach_state", "other"]
print("\t".join(["run", "verdict"] + cols + ["compare"]))
for r in sys.argv[2:]:
    p = d / r
    probes = [l for l in (p / "stderr").read_text(errors="replace").splitlines() if l.startswith("PROBE ")]
    kv = {}
    if probes:
        t = probes[-1].split()[1:]
        kv = {t[i]: t[i + 1] for i in range(0, len(t) - 1, 2)}
    v = (p / "verdict").read_text().strip() if (p / "verdict").exists() else "-"
    c = "-"
    if (p / "compare.json").exists():
        c = json.loads((p / "compare.json").read_text()).get("class", "-")
    print("\t".join([r, v] + [kv.get(k, "-") for k in cols] + [c]))
