#!/usr/bin/env python3
"""Gate (binary level): the capacity evidence is what the EXTRACTED model
says, recomputed, not what the evidence files say about themselves.

Correction C-98, M-1/M-2 of the round-2 review. check_strict_kernel.py is
pure: it reads the committed evidence and recomputes every derived number
from the per-document records. What it cannot do without the extracted
decider is re-derive the records' MODEL side. A forged capacity file that
drops a frame pair and decrements its count, or states a peak or a held
count the model never computed, passed it. This gate builds
latex-parse/strict/strict_decide.exe (the extraction) and:

  1. re-runs `--frame-pairs` and requires the SET of pairs recorded in
     corpora/strict_s0/capacity.json to be exactly the model's (not the count);
  2. rebuilds every pair's streams at the group bound and one past it
     (_strict_capacity.stream) and requires the bytes (sha256), the peak and
     the verdict recorded to be the model's;
  3. rebuilds every memory worst case of the argument signatures
     (_strict_capacity.mem_build, from the recorded depth and counts and the
     recorded filler) and every phase-1 memory document, and requires the
     recorded bytes, memory account (Decide.mem) and verdict to be the model's.

So every oracle grade the pure gate reasons about is a grade of the bytes the
model actually decides. No TeX is run.

Run: python3 scripts/tools/check_strict_capacity.py [--repo .]
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=".")
    args = ap.parse_args()
    repo = Path(args.repo).resolve()
    sys.path.insert(0, str(repo / "scripts/tools"))
    import _strict_capacity as C
    import _strict_s0 as S
    fails: list[str] = []
    cap = json.loads((repo / "corpora/strict_s0/capacity.json").read_text())
    sig = json.loads(S.SIGNATURES.read_text())
    asig = json.loads(S.ARG_SIGNATURES.read_text())
    kern = S.Kernel()
    sha = lambda m: hashlib.sha256(m["tex"].encode()).hexdigest()  # noqa: E731

    # 1. the SET of frame pairs
    pairs = kern.frame_pairs()
    model = {(p["below"], p["above"]) for p in pairs["pairs"]}
    rec = {(r.get("below"), r.get("above")) for r in cap.get("pairs", [])}
    if model != rec:
        fails.append(f"capacity: the recorded frame pairs are not the model's: "
                     f"{len(model - rec)} missing (e.g. {sorted(model - rec)[:3]}), "
                     f"{len(rec - model)} extra (M-1)")

    # 2. every pair's streams, as the model builds and decides them
    groups = C.arg_groups(asig["arg_signatures"])
    reqs, keys = [], []
    for r in cap.get("pairs", []):
        b, a = r.get("below"), r.get("above")
        for key, T in (("at", S.MAX_GROUPS), ("past", S.MAX_GROUPS + 1)):
            st = C.stream(pairs, b, a, T, groups)
            if st is None:
                fails.append(f"capacity: pair {b}>{a} has no stream at {T} groups")
                continue
            reqs.append(C.request(st[0]))
            keys.append((r, key))
    for (r, key), m in zip(keys, kern.run(reqs) if reqs else []):
        got = (sha(m), m["peak_groups"], m["verdict"])
        want = (r[key].get("sha256"), r[key].get("peak"), r[key].get("verdict"))
        if got != want:
            fails.append(f"capacity: pair {r['below']}>{r['above']} {key}: the model gives "
                         f"{got[1:]} for other bytes than recorded ({want[1:]}; M-1)")

    # 3. the memory worst cases and the phase-1 memory documents
    mb = asig.get("capacity", {}).get("memory_bound", {})
    unit = mb.get("filler", {}).get("unit")
    jobs = []
    for n, d in sorted(mb.items()):
        if n == "filler" or not isinstance(d, dict):
            continue
        for w, r in sorted(d.items()):
            for key, extra in (("at", 0), ("past", 1)):
                doc = C.mem_build(S, n, w, unit, r["depth"], r["inner_units"],
                                  r["outer_units"], r["chars"] + extra)
                jobs.append((f"{n}/{w} {key}", {"doc": doc}, r[key]))
    ms = S.Kernel().run([q for _, q, _ in jobs]) if jobs else []
    for (tag, _, want), m in zip(jobs, ms):
        if (sha(m), m.get("mem"), m["verdict"]) != (want.get("sha256"), want.get("mem"),
                                                    want.get("verdict")):
            fails.append(f"arg signatures: memory worst case {tag}: the model gives "
                         f"mem {m.get('mem')} {m['verdict']} for other bytes than recorded "
                         f"(mem {want.get('mem')} {want.get('verdict')}; M-2)")
    t = S.text("x")
    mk = {"R-MEM-TEXT": lambda c, k: S.doc(*([c] * k), t),
          "R-MEM-MATH": lambda c, k: S.doc(S.math("paren", *([c] * k))),
          "R-MEM-DISPLAY": lambda c, k: S.doc(S.math("bracket", *([c] * k))),
          "R-CAP-TEXT": lambda c, k: S.doc(*([c] * k), t),
          "R-CAP-MATH": lambda c, k: S.doc(S.math("paren", *([c] * k)))}
    jobs = []
    for part in ("names", "cap"):
        for n, fams in sorted(sig.get("memory", {}).get(part, {}).items()):
            for f, r in sorted(fams.items()):
                base = f[:-5] if f.endswith("-PAST") else f
                if base in mk and r.get("count"):
                    jobs.append((f"{n} {f}", {"doc": mk[base](S.cmd(n), r["count"])}, r))
    ms = kern.run([q for _, q, _ in jobs]) if jobs else []
    bad = 0
    for (tag, _, want), m in zip(jobs, ms):
        if sha(m) != want.get("sha256") or m["ntoks"] != want.get("ntoks"):
            bad += 1
            if bad <= 10:
                fails.append(f"signatures: memory document {tag} is not the bytes the "
                             f"model builds from its recorded count (M-2)")
    if fails:
        for f in fails:
            print(f"FAIL {f}")
        print(f"[strict-capacity] FAIL — {len(fails)} finding(s)")
        return 1
    print(f"[strict-capacity] OK — {len(model)} frame pairs are exactly the model's; "
          f"{len(keys)} pair streams and every memory document re-derived by the "
          f"extracted decider")
    return 0


if __name__ == "__main__":
    sys.exit(main())
