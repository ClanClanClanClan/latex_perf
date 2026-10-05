#!/usr/bin/env python3
"""Recompute the native-amd64 confirmation's numbers from the committed manifests (../NATIVE-AMD64.md).

usage: python3 docs/v27/spike/native-amd64/verify_native.py      (exit 0 = every check holds)

For each committed native run (native/, native-run2/):
  1. compare.py over its manifest reproduces the committed compare.tsv and compare-summary.txt
     byte for byte;
  2. the summary's tallies equal the per-row verdicts of compare.tsv, by FULL verdict: a
     "CONFIRMS (mask: date)" row is never counted as a byte-identical CONFIRMS;
and for the report:
  3. the H.2 table of NATIVE-AMD64.md §4 (inputs, byte-identical, equal under the date mask,
     REFUTES, per set) equals the counts recomputed from native/compare.tsv;
  4. the report never calls the masked inputs byte-identical (no "176" next to "byte").
It starts no program but compare.py, and reads only committed files.
"""
import re
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORT = HERE.parent / "NATIVE-AMD64.md"
RUNS = ("native", "native-run2")
FAIL = []


def check(ok, msg):
    print(("ok   " if ok else "FAIL ") + msg)
    if not ok:
        FAIL.append(msg)


def rows(tsv: str):
    return [l.split("\t") for l in tsv.splitlines()[1:] if l]


def h2_set(name: str) -> str:
    if name.startswith("deep"):
        return "deep"
    if name == "t0":
        return "t0"
    if name.startswith(("clk-", "env-", "kpse-")):
        return "regressions"
    return "reviewA"


def main():
    for run in RUNS:
        d = HERE / run
        with tempfile.TemporaryDirectory() as t:
            p = subprocess.run([sys.executable, str(HERE / "compare.py"), "--native",
                                str(d / "native-amd64-manifest.json"), "--outdir", t],
                               capture_output=True, text=True)
            check(p.returncode == 0, f"{run}: compare.py exit 0 (got {p.returncode})")
            for f in ("compare.tsv", "compare-summary.txt"):
                check((Path(t) / f).read_bytes() == (d / f).read_bytes(),
                      f"{run}: recomputed {f} equals the committed one")
        rs = rows((d / "compare.tsv").read_text())
        want = {}
        for r in rs:
            want[(r[0], r[2])] = want.get((r[0], r[2]), 0) + 1
        got = {}
        for l in (d / "compare-summary.txt").read_text().splitlines():
            m = re.fullmatch(r"(\S+): (.+) (\d+)", l)
            if m:
                got[(m.group(1), m.group(2))] = int(m.group(3))
        check(got == want, f"{run}: summary tallies equal compare.tsv's rows by full verdict "
              f"(summary {sorted(got.items())} rows {sorted(want.items())})")

    # 3. the report's H.2 table against native/compare.tsv
    count = {}
    for r in rows((HERE / "native" / "compare.tsv").read_text()):
        if r[0] != "h2":
            continue
        s = h2_set(r[1])
        c = count.setdefault(s, [0, 0, 0, 0])
        c[0] += 1
        c[{"CONFIRMS": 1, "CONFIRMS (mask: date)": 2}.get(r[2], 3)] += 1
    count["all"] = [sum(c[i] for c in list(count.values())) for i in range(4)]
    text = REPORT.read_text()
    label = {"reviewA": "review A's graded inputs", "deep": "deep-recursion inputs",
             "t0": "the INITEX run `t0`", "regressions": "checkpoint-3 regressions", "all": "**all**"}
    for s, want in count.items():
        m = re.search(r"^\| " + re.escape(label[s]) + r"[^|]*\|" + r"\s*\**(\d+)\**\s*\|" * 4, text, re.M)
        got = [int(x) for x in m.groups()] if m else None
        check(got == want, f"report H.2 row '{label[s]}': {got} = recomputed {want} "
              "(inputs, byte-identical, date mask, REFUTES)")
    # 4. no sentence calls the masked inputs byte-identical
    bad = [l for l in text.splitlines() if re.search(r"\b176\b", l) and re.search(r"byte", l)]
    check(not bad, "report: no line pairs '176' with 'byte' " + (repr(bad[:2]) if bad else ""))
    print("FAILED" if FAIL else "all checks hold")
    return 1 if FAIL else 0


if __name__ == "__main__":
    sys.exit(main())
