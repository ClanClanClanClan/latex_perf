#!/usr/bin/env python3
"""Native amd64 against the committed qemu-amd64 outcomes, probe by probe (owner decision E3).

usage: compare.py --native NATIVE_MANIFEST.json [--outdir DIR]

Inputs:
  - NATIVE_MANIFEST.json: manifest.py's output over the native run directories, made by
    .github/workflows/spike-native-amd64.yml on an x86_64 runner;
  - qemu-amd64-manifest.json (beside this file): manifest.py's output over the raw qemu-user runs
    the spike left in ~/.cache/lp-spike-h1/ (every file, full sha256);
  - the committed summaries those raw runs produced: h1/archsem/probes/out/*-amd64.out (and the
    full logs beside them), h2/diff/results-amd64.tsv, h2/evidence/inirun/ref-*amd64*.

Verdicts, per probe:
  CONFIRMS  native equals qemu: the same exit status and every output file byte-identical
            (core dumps excluded: they are written by the host's core handler, not by pdfTeX);
            with "(mask: coreline)" or "(mask: date)" when equal only under a declared mask of
            manifest.py, and only where that mask is declared to apply
  REFUTES   anything else; the differing items are listed

Also checked (BASELINE rows): that the raw qemu runs are the runs the committed summaries were
made from. A BASELINE mismatch is a fault of the evidence chain, reported, never hidden.

Exit status: 0 whatever the verdicts (a difference is a finding, not a failure); 2 when an input
is missing (the native run did not produce what the harness should have: an infrastructure error).
"""
import hashlib
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SPIKE = HERE.parent
H1OUT = SPIKE / "h1/archsem/probes/out"
TSV = SPIKE / "h2/diff/results-amd64.tsv"
INIRUN = SPIKE / "h2/evidence/inirun"
ARCHSEM = ("r", "q", "s", "t", "lead")
# H.2 inputs whose run identity leaves pdfTeX on the real clock (H2-report.md, checkpoint 3:
# FORCE_SOURCE_DATE = 01, empty or unset, and SOURCE_DATE_EPOCH unset).
REALCLOCK = ("env-fsd01", "env-fsd-empty", "env-fsd-unset", "env-sde-unset")
# The full logs committed beside the summaries (h1/archsem/README.md).
H1LOGS = (("q", "nh-intmin", "nh-intmin.log", "nh-intmin.amd64.log"),
          ("t", "slanthuge", "slanthuge.log", "slanthuge.amd64.log"),
          ("s", "nh-strings", "nh-strings.log", "nh-strings.arm64.log"))  # s: one log, both arches
# The fingerprints _oracle.py records for the pinned image's pdflatex.fmt (H1-report.md §3).
FMT_AMD64 = "5a9dfc4e27b5c67c737d9bb2bd7d623c6470a4fd9740ff0376d4b871e3a9afc2"
FMT_ARM64 = "a476533c0d6e64f08b47de9c109cc4e9a04874f5bc7a897ad5b622ef9faa54d3"

MISSING = []


def sha_file(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def is_core(rel: str) -> bool:
    n = rel.rsplit("/", 1)[-1]
    return n == "core" or n.endswith(".core")


def rc_lines(text: str) -> dict:
    return {m.group(1): int(m.group(2)) for m in re.finditer(r"^(\S+) rc=(\d+)$", text, re.M)}


def cmp_files(q: dict, n: dict, mask: str | None, skip=lambda rel, e: False):
    """(equal_exact, equal_under_mask, differences) over every non-core file."""
    keys = sorted({k for k in q if not is_core(k) and not skip(k, q[k])}
                  | {k for k in n if not is_core(k) and not skip(k, n[k])})
    diffs, masked_only = [], []
    for k in keys:
        a, b = q.get(k), n.get(k)
        if a is None or b is None:
            diffs.append(f"{k}: {'only native' if a is None else 'only qemu'}")
        elif a["sha256"] != b["sha256"]:
            if mask and "masked" in a and "masked" in b and a["masked"][mask] == b["masked"][mask]:
                masked_only.append(k)
            else:
                diffs.append(f"{k}: qemu {a['sha256'][:16]} native {b['sha256'][:16]}")
    return (not diffs and not masked_only), not diffs, diffs, masked_only


def cores(d: dict) -> str:
    c = sorted(k for k in d if is_core(k))
    return ",".join(c) if c else "-"


def verdict(exact, under_mask, mask):
    if exact:
        return "CONFIRMS"
    if under_mask:
        return f"CONFIRMS (mask: {mask})"
    return "REFUTES"


def main(argv):
    if "--native" not in argv:
        sys.exit(__doc__)
    nat = json.loads(Path(argv[argv.index("--native") + 1]).read_text())
    outdir = Path(argv[argv.index("--outdir") + 1]) if "--outdir" in argv else None
    qm = json.loads((HERE / "qemu-amd64-manifest.json").read_text())
    rows = []   # group, probe, verdict, rc_qemu, rc_native, detail

    def need(g):
        if g not in nat:
            MISSING.append(f"group {g}")
            return False
        return True

    # ---- H.1 architecture probes (h1/archsem/probes, run.sh / run2.sh / lead/run.sh)
    for g in ARCHSEM:
        committed = (H1OUT / f"{g}-amd64.out").read_text()
        if qm[g]["outfile"]["text"] != committed:
            rows.append(["BASELINE", g, "MISMATCH", "", "", f"raw qemu {g}-amd64.out is not the committed one"])
        if not need(g):
            continue
        if nat[g]["inputs"] != qm[g]["inputs"]:   # the documents, images and run script themselves
            rows.append(["INPUTS", g, "MISMATCH", "", "", "native run directory's inputs differ from the qemu run's: "
                         + ",".join(sorted(k for k in set(nat[g]["inputs"]) | set(qm[g]["inputs"])
                                           if nat[g]["inputs"].get(k) != qm[g]["inputs"].get(k)))])
        ntext = nat[g]["outfile"]["text"]
        qrc, nrc = rc_lines(committed), rc_lines(ntext)
        same_out = ntext == committed
        rows.append([g, f"({g}-amd64.out)", "CONFIRMS" if same_out else "REFUTES", "", "",
                     "terminal summary byte-identical to the committed one" if same_out else
                     "terminal summary differs from the committed one (see native/" + f"{g}-amd64.out)"])
        names = sorted(set(qm[g]["probes"]) | set(nat[g]["probes"]))
        for p in names:
            qf, nf = qm[g]["probes"].get(p), nat[g]["probes"].get(p)
            if nf is None:
                MISSING.append(f"{g}/{p}")
                continue
            if qf is None:
                rows.append([g, p, "REFUTES", "-", str(nrc.get(p, "?")), "probe ran only natively"])
                continue
            ex, um, diffs, mo = cmp_files(qf, nf, "coreline", skip=lambda rel, e: e.get("input"))
            rcq, rcn = qrc.get(p), nrc.get(p)
            v = verdict(ex, um, "coreline") if rcq == rcn else "REFUTES"
            det = []
            if rcq != rcn:
                det.append(f"rc qemu {rcq} native {rcn}")
            det += diffs
            if mo:
                det.append("equal only under the coreline mask: " + ",".join(mo))
            det.append(f"core files qemu {cores(qf)} native {cores(nf)}")
            rows.append([g, p, v, str(rcq), str(rcn), "; ".join(det)])
    for g, p, f, committed in H1LOGS:
        if g in nat and p in nat[g]["probes"] and f in nat[g]["probes"][p]:
            c = sha_file(H1OUT / committed)
            n = nat[g]["probes"][p][f]["sha256"]
            rows.append([g, f"{p} (committed {committed})", "CONFIRMS" if c == n else "REFUTES", "", "",
                         f"committed {c[:16]} native {n[:16]}"])
        else:
            MISSING.append(f"{g}/{p}/{f}")

    # ---- H.1 §5.3 adversarial rot2.tex (\pdfsetmatrix, FMA)
    if need("rot"):
        q, n = qm["rot"], nat["rot"]
        ex, um, diffs, mo = cmp_files(q["files"], n["files"], None)
        same_rc = q["rc_line"] == n["rc_line"]
        rows.append(["rot", "rot2", "CONFIRMS" if ex and same_rc else "REFUTES",
                     q["rc_line"].strip(), n["rc_line"].strip(),
                     "; ".join(diffs) or "rot2.pdf " + n["files"]["rot2.pdf"]["sha256"][:16]])

    # ---- H.1 §3 the format: f7amd.sh
    if need("f7amd"):
        q, n = qm["f7amd"]["files"], nat["f7amd"]["files"]
        ex, um, diffs, mo = cmp_files(q, n, None)
        fp = []
        for rel, want in (("shipped-x86_64.fmt", FMT_AMD64), ("own/pdflatex.fmt", FMT_AMD64),
                          ("armclock/pdflatex.fmt", FMT_ARM64)):
            got = n.get(rel, {}).get("sha256", "absent")
            fp.append(f"{rel} {'=' if got == want else '!='} {want[:16]}")
        ok = ex and all(" = " in x for x in fp)
        drop = lambda t: [l for l in t.splitlines() if not l.startswith(("docker run", "RC="))]
        same_log = drop(qm["f7amd"]["outfile"]["text"]) == drop(nat["f7amd"]["outfile"]["text"])
        rows.append(["f7amd", "pdflatex.fmt", "CONFIRMS" if ok and same_log else "REFUTES", "", "",
                     "; ".join(diffs + fp + ([] if same_log else ["f7amd.sh output differs"]))])

    # ---- H.2 the differential's binary side (h2/diff, run_bin.zsh) and the INITEX evidence
    tsv = [l.split("\t") for l in TSV.read_text().splitlines()[1:]]
    if need("h2"):
        qi, ni = qm["h2"]["inputs"], nat["h2"]["inputs"]
        for r in tsv:
            name, brc, out16, files16, nclock = r[0], r[2], r[4], r[5], r[6]
            qb = qi.get(name, {}).get("bin")
            # baseline: the raw qemu run is the one the committed row summarises
            if qb is None:
                rows.append(["BASELINE", f"h2/{name}", "MISMATCH", "", "", "no raw qemu run"])
            else:
                f16 = ",".join(f"{k[2:]}={v['sha256'][:16]}" for k, v in sorted(qb.items())
                               if k.startswith("w/") and k != "w/clock.log") or "-"
                ql = qb.get("w/clock.log", {}).get("text")
                qn = str(len(ql.splitlines())) if ql is not None else "0"
                if (qb["rc"]["text"].strip(), qb["out"]["sha256"][:16], f16, qn) != (brc, out16, files16, nclock):
                    rows.append(["BASELINE", f"h2/{name}", "MISMATCH", "", "",
                                 "raw qemu run is not the committed row"])
            nb = ni.get(name, {}).get("bin")
            if nb is None:
                MISSING.append(f"h2/{name}")
                continue
            mask = "date" if name in REALCLOCK else None
            ex, um, diffs, mo = cmp_files(qb or {}, nb, mask)
            rq, rn = (qb or {}).get("rc", {}).get("text", "?").strip(), nb["rc"]["text"].strip()
            det = list(diffs)
            if mo:
                det.append("equal only under the date mask: " + ",".join(mo))
            if rq != rn:
                det.insert(0, f"rc qemu {rq} native {rn}")
            det.append(f"core files qemu {cores(qb or {})} native {cores(nb)}")
            rows.append(["h2", name, verdict(ex, um, mask) if rq == rn else "REFUTES", rq, rn, "; ".join(det)])
        # the INITEX evidence (h2/evidence/inirun): t0 shimmed, and its real-clock control
        t0 = ni.get("t0", {})
        for sub, pre, pairs in (("bin", "ref-amd64", (("rc", "rc"), ("out", "stdout"), ("err", "stderr"),
                                                       ("w/texput.log", "texput.log"), ("w/clock.log", "clock.log"))),
                                ("realclock", "ref-realclock-amd64", (("rc", "rc"), ("out", "stdout"),
                                                                       ("w/texput.log", "texput.log")))):
            if sub not in t0:
                MISSING.append(f"h2/t0/{sub}")
                continue
            bad = []
            for nrel, cname in pairs:
                c = sha_file(INIRUN / f"{pre}.{cname}")
                n = t0[sub].get(nrel, {}).get("sha256", "absent")
                if c != n:
                    bad.append(f"{pre}.{cname}: committed {c[:16]} native {n[:16]}")
            rows.append(["h2-inirun", pre, "CONFIRMS" if not bad else "REFUTES", "", "",
                         "; ".join(bad) or f"{len(pairs)} files byte-identical to h2/evidence/inirun/{pre}.*"])

    # ---- report
    hdr = ["group", "probe", "verdict", "rc_qemu", "rc_native", "detail"]
    tsv_out = "\t".join(hdr) + "\n" + "".join("\t".join(x.replace("\t", " ") for x in r) + "\n" for r in rows)
    tally = {}
    for r in rows:
        k = (r[0] if r[0] in ("BASELINE",) else r[0], r[2].split(" ")[0])
        tally[k] = tally.get(k, 0) + 1
    lines = [f"{g}: {v} {c}" for (g, v), c in sorted(tally.items())]
    print("\n".join(lines))
    print("per probe (group, probe, verdict, rc qemu, rc native, detail):")
    for r in rows:
        print("  ", "\t".join(r))
    if MISSING:
        print("MISSING (infrastructure):", ", ".join(MISSING))
    if outdir:
        outdir.mkdir(parents=True, exist_ok=True)
        (outdir / "compare.tsv").write_text(tsv_out)
        (outdir / "compare-summary.txt").write_text("\n".join(lines) + "\n"
                                                    + ("MISSING: " + ", ".join(MISSING) + "\n" if MISSING else ""))
    return 2 if MISSING else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
