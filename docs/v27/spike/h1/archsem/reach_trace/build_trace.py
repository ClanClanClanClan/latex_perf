#!/usr/bin/env python3
"""Turn the raw gdb trace (raw/<arch>/<document>.json, written by trace_gdb.py)
into reach_trace.tsv: one row per (document, candidate site, architecture on
which the site has instructions).

usage: python3 docs/v27/spike/h1/archsem/reach_trace/build_trace.py [--check]

Pure: reads only files in this directory and ../probes/out/; runs nothing.
With --check it writes nothing and exits 1 if reach_trace.tsv is not exactly
what it would write (verify_h1.py runs it so).

Columns:
  doc          the probe document (archsem/probes/<doc>.tex or probes/lead/)
  class, site  the census site (site_addrs.tsv)
  arch         arm64 | amd64
  addrs        link-time addresses of the site's DIV/F2I instructions on arch
  hits         executions of each of those instructions, same order
  edge_hits    executions with an EDGE operand (trace_gdb.py: divisor 0 or -1,
               an INT_MIN operand; a NaN or out-of-int-range conversion source)
  edge_example first edge operands seen (dividend,divisor or the double)
  rc_traced    the run's rc under the trace: aarch64, gdb's exit code (or 128 +
               the signal); x86_64, the shell's $? for the traced engine
               (raw/amd64/shellrc.tsv, from the driver's `shellrc=` lines),
               because gdb learns no exit signal through qemu-user's gdbstub;
               where gdb did learn an exit code it must equal the shell's
  rc_recorded  the rc in the committed probe outputs (probes/out/*-<arch>.out)
  fault        the site, if the run died of a signal AT one of its instructions
Every raw file is checked: one breakpoint per site_addrs.tsv row of its arch,
each at the link address plus ONE load bias common to the whole run (0 on
amd64, whose build is not PIE); no conversion hit whose source lane could not
be matched to its result (trace_gdb.py `inconsistent`), none left undecided at
exit; a run that died of a signal recorded the signal stop; and rc_traced
equal to rc_recorded wherever the probe outputs record one."""
import csv
import json
import re
import sys
from pathlib import Path

H = Path(__file__).resolve().parent
OUT = H.parent / "probes" / "out"
errs = []
sa = list(csv.DictReader(open(H / "site_addrs.tsv"), delimiter="\t"))


def recorded(arch):
    rc = {}
    for f in sorted(OUT.glob(f"*-{arch}.out")):
        for ln in f.read_text().splitlines():
            m = re.match(r"^(\S+) rc=(\d+)$", ln)
            if m:
                if m.group(1) in rc and rc[m.group(1)] != int(m.group(2)):
                    errs.append(f"{arch} {m.group(1)}: two different recorded rcs")
                rc[m.group(1)] = int(m.group(2))
    return rc


rows = []
for arch in ("arm64", "amd64"):
    want = [r for r in sa if r["arch"] == arch]
    rec = recorded(arch)
    shellrc = {}
    if arch == "amd64":
        for ln in (H / "raw" / "amd64" / "shellrc.tsv").read_text().splitlines()[1:]:
            k, v = ln.split("\t")
            shellrc[k] = int(v)
    raws = sorted((H / "raw" / arch).glob("*.json"))
    if not raws:
        errs.append(f"no raw trace for {arch}")
    for p in raws:
        doc = p.stem
        d = json.loads(p.read_text())
        bps = d["breakpoints"]
        if [(b["site"], b["link_addr"], b["insn"]) for b in bps] != [(r["site"], r["addr"], r["insn"]) for r in want]:
            errs.append(f"{arch} {doc}: breakpoints are not site_addrs.tsv's {len(want)} rows in order")
            continue
        bias = {int(b["runtime_addr"], 16) - int(b["link_addr"], 16) for b in bps}
        if len(bias) != 1 or (arch == "amd64" and bias != {0}):
            errs.append(f"{arch} {doc}: breakpoints not at link address + one load bias ({sorted(map(hex, bias))})")
        if d["exitcode"] is not None:
            rc = d["exitcode"]
        elif d["exitsignal"] is not None:
            rc = 128 + d["exitsignal"]
        else:
            rc = None
        if arch == "amd64":
            if doc not in shellrc or (rc is not None and rc != shellrc[doc]):
                errs.append(f"{arch} {doc}: shell rc {shellrc.get(doc)} vs gdb exit status {rc}")
                continue
            rc = shellrc[doc]
        if rc is None:
            errs.append(f"{arch} {doc}: the traced run has no exit status")
            continue
        for b in bps:
            if b.get("inconsistent") or b.get("pending_at_exit"):
                errs.append(f"{arch} {doc} {b['site']} {b['link_addr']}: {b.get('inconsistent')} conversion hit(s) "
                            f"whose source matches no result, pending at exit {b.get('pending_at_exit')}")
            if b["class"] == "F2I" and "lanes" not in b:
                errs.append(f"{arch} {doc} {b['site']}: a conversion traced without the result cross-check")
        if doc in rec and rec[doc] != rc:
            errs.append(f"{arch} {doc}: rc {rc} under gdb, {rec[doc]} recorded")
        fault_sites = {s for st in d["signal_stops"] for s in st["at_site"]}
        if arch == "amd64" and set(shellrc) != {q.stem for q in raws}:
            errs.append(f"amd64: shellrc.tsv documents differ from the raw traces")
        if rc >= 128 and not d["signal_stops"]:
            errs.append(f"{arch} {doc}: died of a signal but no signal stop was recorded")
        by = {}
        for b in bps:
            by.setdefault((b["class"], b["site"]), []).append(b)
        for (cl, site), bs in by.items():
            ex = next((b["edge_examples"][0] for b in bs if b["edge_examples"]), "")
            rows.append([doc, cl, site, arch, ",".join(b["link_addr"] for b in bs), ",".join(str(b["hits"]) for b in bs),
                         str(sum(b["edge_hits"] for b in bs)), json.dumps(ex) if ex != "" else "-", str(rc),
                         str(rec.get(doc, "-")), site if site in fault_sites else "-"])
rows.sort(key=lambda r: (r[0], r[2], r[1], r[3]))
text = "\t".join(["doc", "class", "site", "arch", "addrs", "hits", "edge_hits", "edge_example", "rc_traced",
                  "rc_recorded", "fault"]) + "\n" + "".join("\t".join(r) + "\n" for r in rows)
if "--check" in sys.argv:
    if (H / "reach_trace.tsv").read_text() != text:
        errs.append("reach_trace.tsv is not build_trace.py's output")
else:
    (H / "reach_trace.tsv").write_text(text)
for e in errs:
    print("FAIL", e)
print(f"build_trace: {len(rows)} rows, {'OK' if not errs else f'{len(errs)} failure(s)'}")
sys.exit(1 if errs else 0)
