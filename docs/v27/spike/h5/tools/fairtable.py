#!/usr/bin/env python3
"""fairtable.py FAIRDIR RUNSDIR TAG: the fair rounds of fairtime.sh as tables (spike H.5, stage-1 correction, C-145).

Medians on BOTH sides, over the SAME name populations:
  - the binary: every BIN line of FAIRDIR/bin.txt (BINREPS runs per prefix per round), user + sys;
  - each model variant: the final PROBE line's `cpu` (Sys.time: user + sys) of RUNSDIR/TAG<r>-<variant>-<prefix>
    (its `stderr`, or the committed `stderr-probes.txt`).
Live: fairtable.py ~/.cache/lp-spike-h1/h5/fair/fr ~/.cache/lp-spike-h1/h5/runs fr
Committed evidence: fairtable.py docs/v27/spike/h5/evidence/fair docs/v27/spike/h5/evidence/fair/runs fr
Ratios are median(model) / median(binary) on the same prefix. The marginal cost per name is
(median(pN) - median(p0)) / N on each side, with the same N (1,000 and all 23,519 names).
Also: the top of the major heap (words) and the peak physical footprint (MB) of each run, and the
host load (1-min uptime) and memory_pressure free % recorded before each run.
"""
import re, statistics as st, sys
from pathlib import Path

fair, runsdir, tag = Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3]
NAMES = {"p0": 0, "p250": 250, "p1000": 1000, "pall": 23519}
med = st.median

binr, rnd = {}, 0
for l in (fair / "bin.txt").read_text().splitlines():
    if l.startswith("ROUND "):
        rnd = int(l.split()[1])
    m = re.match(r"BIN (\S+) \d+ user ([\d.]+) sys ([\d.]+) rc (\d+) logsize (\d+) logsha (\w+) vmload (\S+)", l)
    if m:
        assert m.group(4) == "0", l
        binr.setdefault(m.group(1), []).append((rnd, float(m.group(2)) + float(m.group(3)), m.group(6), m.group(7)))

loads = {}
for l in (fair / "load.log").read_text().splitlines():
    m = re.match(r"LOAD (\S+) \d+ uptime\[([\d.]+)[^\]]*\] mem_free_pct (\d+)%", l)
    if m:
        loads[m.group(1)] = (float(m.group(2)), int(m.group(3)))

runs = {}
for d in sorted(runsdir.glob(f"{tag}[0-9]*-*-p*")):
    m = re.match(rf"{tag}(\d+)-(.+)-(p\w+)$", d.name)
    if not m or not (d / "verdict").exists():
        continue
    ver = (d / "verdict").read_text().strip()
    err = d / "stderr" if (d / "stderr").exists() else d / "stderr-probes.txt"
    probes = [l for l in err.read_text(errors="replace").splitlines() if l.startswith("PROBE ")]
    if not ver.startswith("finished rc 0") or not probes:
        runs.setdefault((m.group(2), m.group(3)), []).append((int(m.group(1)), None, None, None, ver))
        continue
    t = probes[-1].split()[1:]
    kv = {t[i]: t[i + 1] for i in range(0, len(t) - 1, 2)}
    peak = int(re.search(r"peak (\d+)MB", ver).group(1))
    runs.setdefault((m.group(2), m.group(3)), []).append((int(m.group(1)), float(kv["cpu"]), int(kv["top"]), peak, ver))

print("## binary (pinned pdfTeX, container-local storage): user+sys s")
print("prefix\tn\tmedian\tmin\tmax\tlogsha")
bmed = {}
for p in NAMES:
    if p in binr:
        v = [c for _, c, _, _ in binr[p]]
        shas = sorted({s[:8] for *_, s, _ in binr[p]})
        bmed[p] = med(v)
        print(f"{p}\t{len(v)}\t{med(v):.3f}\t{min(v):.3f}\t{max(v):.3f}\t{','.join(shas)}")

print("\n## model variants: CPU s (final probe), top of heap (M words), peak footprint (MB), host load / mem free % before the run")
print("variant\tprefix\tcpu per round\tmedian\ttop_heap_Mw max\tpeak_MB max\tloads\tratio_vs_binary_median")
vmed = {}
for (v, p), rs in sorted(runs.items(), key=lambda kv: (kv[0][0], NAMES.get(kv[0][1], 0))):
    rs.sort()
    ok = [r for r in rs if r[1] is not None]
    bad = [r[4] for r in rs if r[1] is None]
    ld = " ".join(f"{loads.get(f'{tag}{r}-{v}-{p}', ('?', '?'))[0]}/{loads.get(f'{tag}{r}-{v}-{p}', ('?', '?'))[1]}%" for r, *_ in rs)
    if not ok:
        print(f"{v}\t{p}\tNONE FINISHED: {bad}\t\t\t\t{ld}"); continue
    c = [r[1] for r in ok]; vmed[(v, p)] = med(c)
    print(f"{v}\t{p}\t{' '.join(f'{x:.2f}' for x in c)}\t{med(c):.2f}\t{max(r[2] for r in ok)/1e6:.1f}\t{max(r[3] for r in ok)}\t{ld}\t"
          f"{med(c)/bmed[p]:.0f}x" + (f"\tNOT FINISHED: {bad}" if bad else ""))

print("\n## marginal cost per name, (median(pN) - median(p0)) / N on each side")
for n in ("p1000", "pall"):
    if n not in bmed or "p0" not in bmed:
        continue
    b = (bmed[n] - bmed["p0"]) / NAMES[n]
    # resolvable only if the difference of the medians exceeds the binary's own spread at p0
    spread = max(c for _, c, _, _ in binr["p0"]) - min(c for _, c, _, _ in binr["p0"])
    ok = bmed[n] - bmed["p0"] > spread
    print(f"binary {n}: {b*1e3:.4f} ms/name" + ("" if ok else
          f"  NOT RESOLVABLE: the difference of medians ({(bmed[n]-bmed['p0'])*1e3:.0f} ms) is within the binary's p0 spread ({spread*1e3:.0f} ms)"))
    for v in sorted({v for v, _ in vmed}):
        if (v, n) in vmed and (v, "p0") in vmed:
            m = (vmed[(v, n)] - vmed[(v, "p0")]) / NAMES[n]
            print(f"  {v} {n}: {m*1e3:.3f} ms/name" + (f" = {m/b:.0f}x" if ok else " (no binary denominator)"))
