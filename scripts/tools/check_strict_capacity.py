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
     recorded fillers), stage G's memory documents, and every phase-1 memory
     and dimension document (the structural levels, the names' contexts, the
     bound documents, the dimension-bound documents and their box
     instruments, the round-1 review's documents), and requires the recorded
     bytes, token count, memory account (Decide.mem), dimension account
     (Decide.dim) and verdict to be the model's, every document one past a
     bound to be outside, and pdfTeX's report on every graded one to be within
     the committed account (C-98, C-100).

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
    wt = C.dim_weight(asig["arg_signatures"], sig["dims"])
    reqs, keys = [], []
    for r in cap.get("pairs", []):
        b, a = r.get("below"), r.get("above")
        for key, T in (("at", S.MAX_GROUPS), ("past", S.MAX_GROUPS + 1)):
            st = C.stream(pairs, b, a, T, groups, wt, C.STREAM_BUDGET)
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

    # 3. the memory worst cases and the phase-1 memory documents: every
    # record's bytes, model counts (tokens, account, dimensions) and verdict
    # are the extracted model's under the committed files, rebuilt from the
    # recorded family and counts (C-98, C-100); and pdfTeX's report is within
    # the account (base + Decide.mem) on every graded one, stage G's included
    import _strict_dims as DM
    m0 = sig["memory"]["structural"]["BASE"]["used"]
    mb = asig.get("capacity", {}).get("memory_bound", {})
    jobs = []
    for n, d in sorted(mb.items()):
        if n in ("filler", "filler_costly") or not isinstance(d, dict):
            continue
        for key, r in sorted(d.items()):
            w = key.split(":")[0]
            unit = mb["filler_costly" if key.endswith(":costly") else "filler"]["unit"]
            for which, extra in (("at", 0), ("past", 1)):
                doc = C.mem_build(S, n, w, unit, r["depth"], r["inner_units"],
                                  r["outer_units"], r["chars"] + extra)
                jobs.append((f"arg {n}/{key} {which}", {"doc": doc}, r[which]))
    t = S.text("x")
    for n, recs in sorted(asig.get("capacity", {}).get("memory", {}).get("records", {}).items()):
        for f, r in sorted(recs.items()):
            fam, w = f.split(":")[0], f.split(":")[1].split("@")[0]
            root = (lambda b: S.doc(*b)) if w == "text" else \
                (lambda b: S.doc(S.math("paren", *b)))
            if fam in ("G-MEM-FLAT", "G-MEM-FLATX"):
                unit = [S.cmd(n), S.group()] if fam == "G-MEM-FLAT" else [S.cmd(n), S.group(t)]
                doc = root([q for _ in range(r["count"]) for q in unit])
            else:
                inner = [S.text("x" * (2500 if fam == "G-MEM-DEEP-HALF" else 5000))]
                doc = root(C.nested(S, n, r["depth"], inner))
            jobs.append((f"arg {n} {f}", {"doc": doc}, dict(r, _raw=True)))
    dz = DM.Dims(sig["dims"], {n: v["dim"] for n, v in sig["signatures"].items()})
    mem1 = sig.get("memory", {})
    bjobs = []
    for f, r in sorted(mem1.get("structural", {}).items()):
        if r.get("bytes"):
            bjobs.append((f"structural {f}", C.hyph_bytes(r["units"]), r))
            continue
        doc = S.doc(t) if f == "BASE" else C.structural_doc(S, f[2:].split("@")[0], r["units"])
        jobs.append((f"structural {f}", {"doc": doc}, r))
    for n, fams in sorted(mem1.get("names", {}).items()):
        for f, r in sorted(fams.items()):
            ctx = f[len("R-MEM-"):].split("@")[0]
            jobs.append((f"{n} {f}", {"doc": C.name_mem_doc(S, n, ctx, r["count"])}, r))
    for n, fams in sorted(mem1.get("cap", {}).items()):
        for f, r in sorted(fams.items()):
            where = f.split("-")[2]
            jobs.append((f"{n} {f}", {"doc": C.cap_doc(S, dz, n, where, r["count"])}, r))
    for n, fams in sorted(sig.get("dim_bound", {}).items()):
        for f, r in sorted(fams.items()):
            where = f.split("-")[2]
            jobs.append((f"{n} {f}", {"doc": C.dim_doc(S, n, where, r["count"])}, r))
            if "box_tex_sha256" in r:
                snip = DM.snippet("name", n) * r["count"]
                ds = "\\displaystyle " if where == "DISPLAY" else ""
                box = snip if where == "TEXT" else "$" + ds + snip + "$"
                inst = (DM.HEAD + "\\setbox0\\hbox{" + box + "}\\typeout{BOXDIM:\\the\\wd0:"
                        "\\the\\ht0:\\the\\dp0}\n\\end{document}\n")
                if hashlib.sha256(inst.encode()).hexdigest() != r["box_tex_sha256"]:
                    fails.append(f"signatures: {n} {f}: the box instrument's bytes are not "
                                 f"the ones its measure is recorded for (C-100)")
    rv = {f: d for f, _, d in C.review_docs(S)}
    for f, r in sorted(mem1.get("review", {}).items()):
        if f not in rv:
            fails.append(f"signatures: review document {f} is not one of the round-1 review's")
            continue
        jobs.append((f"review {f}", {"doc": rv[f]}, r))
    ms = kern.run([q for _, q, _ in jobs]) if jobs else []
    if bjobs:
        bm = S.BytesKernel().run([b for _, b, _ in bjobs])
        for (tag, b, r), m in zip(bjobs, bm):
            jobs.append((tag, None, r))
            ms.append(dict(m, tex=b.decode("ascii")))
    bad = 0
    for (tag, _, want), m in zip(jobs, ms):
        why = None
        if sha(m) != want.get("sha256"):
            why = "other bytes than the ones graded"
        elif not want.get("_raw") and (m["ntoks"], m.get("mem"), m.get("dim"), m["verdict"]) != (
                want.get("ntoks"), want.get("mem"), want.get("dim", m.get("dim")),
                want.get("verdict")):
            why = (f"the model gives ntoks/mem/dim/verdict {m['ntoks']}/{m.get('mem')}/"
                   f"{m.get('dim')}/{m['verdict']}, recorded {want.get('ntoks')}/"
                   f"{want.get('mem')}/{want.get('dim')}/{want.get('verdict')}")
        elif want.get("used") is not None and (want.get("oracle") or [1])[0] == 0 \
                and want["used"] > m0 + m.get("mem", 0):
            why = (f"pdfTeX reports {want['used']} words, more than the committed account "
                   f"{m0 + m.get('mem', 0)}")
        elif tag.endswith("-PAST") and m["verdict"] != "not_strict":
            why = "one past the bound is inside the fragment"
        if why:
            bad += 1
            if bad <= 12:
                fails.append(f"memory document {tag}: {why} (M-2, C-100)")
    if bad > 12:
        fails.append(f"{bad} memory documents fail in all")
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
