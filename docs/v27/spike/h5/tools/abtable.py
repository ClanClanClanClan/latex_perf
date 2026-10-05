#!/usr/bin/env python3
"""abtable.py RUNS_DIR: the interleaved A/B rounds (abN-VARIANT-PREFIX) as a table of CPU seconds per
round and their median, with each run's top of the major heap and peak footprint (spike H.5 stage 1)."""
import re, statistics, sys
from pathlib import Path
d = Path(sys.argv[1]); rows = {}
for p in sorted(d.glob("ab[0-9]-*")):
    m = re.match(r"ab(\d)-(.+)-(p\w+)$", p.name)
    probes = [l for l in (p / "stderr").read_text(errors="replace").splitlines() if l.startswith("PROBE ")]
    if not m or not probes or not (p / "verdict").exists():
        continue
    t = probes[-1].split()[1:]; kv = {t[i]: t[i + 1] for i in range(0, len(t) - 1, 2)}
    peak = re.search(r"peak (\d+)MB", (p / "verdict").read_text())
    rows.setdefault((m.group(3), m.group(2)), []).append((int(m.group(1)), float(kv["cpu"]), int(kv["top"]), int(peak.group(1)) if peak else -1))
print("prefix\tvariant\tcpu_s_per_round\tmedian_cpu_s\ttop_heap_words\tpeak_footprint_mb")
for (pre, var), v in sorted(rows.items()):
    v.sort()
    print(f"{pre}\t{var}\t{' '.join(f'{c:.2f}' for _, c, _, _ in v)}\t{statistics.median(c for _, c, _, _ in v):.2f}\t{max(t for *_, t, _ in v)}\t{max(f for *_, f in v)}")
