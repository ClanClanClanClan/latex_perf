#!/usr/bin/env python3
"""Measure the strict fragment's TeX CAPACITY account (correction C-94).

WHY. pdfTeX has fixed capacities that no rule of the semantics models; a
document past one stops with "! TeX capacity exceeded" whatever the model
says. C-86 bounded the fragment by BRACE depth; slice A let a formula (a TeX
group) open inside an argument, so 128 levels of \\mbox{$ ... $} held 256
groups inside the brace bound and the model said PROVEN-READY for a document
pdfTeX refuses. The fix bounds the exact quantity: Decide.groups, the TeX
groups of the frame stack, in every state of the run (Decide.peak <= 200).
This tool produces the evidence that the account is exact and the margin
real, corpora/strict_s0/capacity.json:

  1. TEXMF: the pinned image's capacity settings (kpsewhich -var-value).
  2. PAIRS: every ordered pair of frame kinds the EXTRACTED model can stack
     (strict_decide.exe --frame-pairs), each as a token stream repeating the
     pair to exactly 200 groups (graded: the model must decide it and agree
     with pdfTeX), to 201 (the model must place it outside the fragment;
     graded too, for the record), and the depth at which pdfTeX itself
     overflows, searched: the first failing peak must lie in
     [CAPACITY + 1 - MAX_TRANSIENT, CAPACITY + 1] (the account is exact:
     one group per frame, an argument its measured g).
  3. TRANSIENTS: the groups a construct holds on top of its frames while it
     runs (a paragraph start, \\[, a page break's output routine,
     \\end{document}'s), each measured by the deepest nesting it survives.
  4. USAGE: pdfTeX's own report of every other capacity (main memory,
     save stack, input stack, parameter stack, semantic nest, buffer,
     string pool, strings, hash, fonts) on the documents at the bounds:
     every pair stream at 200 groups, the token bound in text and in math,
     the longest line, and the most names pdfTeX can be made to enter into
     its hash (19,990 distinct undefined names of 100 letters, read whole as
     one argument).

Needs the oracle (docker and the pinned image). Usage:
    python3 scripts/tools/measure_strict_capacity.py [--workers 4]
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import _oracle  # noqa: E402
import _strict_capacity as C  # noqa: E402
import _strict_s0 as S  # noqa: E402
import _strict_dims as DM  # noqa: E402

# Version 2 (C-98): the memory account (a maximiser over every construct,
# the per-held-token slope of every argument command, the worst case at the
# bound and one token past it for every command), and every graded document
# recorded with its bytes' sha256, grade and pdfTeX's capacity report, so the
# gates recompute every derived number from these PRIMARY records.
# Version 3 (C-104): the dimension bound is one of the bounds; the usage
# documents at the token bound are cut into paragraphs and formulas within
# it (a document of one 19,999-character paragraph is outside the fragment
# now); the longest line (19,998 spaces) is recorded as an instrument of the
# buffer, outside the fragment.
GENERATOR_VERSION = "3"
OUT = S.REPO / "corpora/strict_s0/capacity.json"
MAX_GROUPS, MAX_TOKENS, MAX_NAME = S.MAX_GROUPS, S.MAX_TOKENS, S.MAX_NAME
# The search range of pdfTeX's own overflow, in model groups.
SEARCH_HI = 330
TEXMF_VARS = ("main_memory", "extra_mem_top", "extra_mem_bot", "font_mem_size",
              "font_max", "hash_extra", "pool_size", "string_vacancies",
              "max_strings", "pool_free", "buf_size", "nest_size", "max_in_open",
              "param_size", "save_size", "stack_size", "expand_depth",
              "hyph_size", "trie_size")


def texmf(oracle) -> dict:
    out = {}
    for v in TEXMF_VARS:
        rc, o, _ = oracle.image_command(["kpsewhich", f"-var-value={v}"])
        if rc not in (0, 1):
            raise _oracle.OracleError(f"kpsewhich {v}: rc {rc}")
        val = o.decode().strip()
        out[v] = int(val) if val.isdigit() else (val or None)
    return out


def undef_names(k: int, members: set[str]) -> list[str]:
    """k distinct names of MAX_NAME letters outside the closed world."""
    out, i = [], 0
    alpha = "abcdefghijklmnopqrstuvwxyz"
    while len(out) < k:
        n, s = i, []
        while True:
            s.append(alpha[n % 26])
            n //= 26
            if n == 0:
                break
        name = ("lpq" + "".join(s)).ljust(MAX_NAME, "z")
        if name not in members:
            out.append(name)
        i += 1
    return out



class Grades:
    """Every grade of this run, keyed by the sha256 of the graded bytes, with
    pdfTeX's capacity report; seeded only from COMMITTED capacity files
    (S.committed_source, LOW-2)."""

    def __init__(self, oracle, reuse: list[str]):
        import threading
        self.oracle, self.cache, self.lock = oracle, {}, threading.Lock()
        self.reused, self.sources = 0, []
        for spec in reuse:
            text, src = S.committed_source(spec)
            d = json.loads(text)
            if d.get("oracle") != oracle.provenance():
                raise SystemExit(f"--reuse {spec}: graded by another oracle")
            n = 0
            for r in _records(d):
                if "sha256" in r and "oracle" in r and "stats" in r:
                    rc, pdf, err, line = r["oracle"]
                    self.cache[r["sha256"]] = {"rc": rc, "pdf": pdf, "error": err,
                                               "line": line, "timed_out": False,
                                               "passes": None, "stats": r["stats"]}
                    n += 1
            self.sources.append({**src, "records": n})

    def grade(self, tex: str) -> dict:
        h = hashlib.sha256(tex.encode()).hexdigest()
        with self.lock:
            g = self.cache.get(h)
            if g is not None:
                self.reused += 1
                return g
        g = S.grade(self.oracle, tex, stats=True)
        with self.lock:
            self.cache[h] = g
        return g


def _records(d: dict):
    """Every per-document record of a capacity file."""
    def walk(x):
        if isinstance(x, dict):
            if "sha256" in x and "oracle" in x:
                yield x
            for v in x.values():
                yield from walk(v)
        elif isinstance(x, list):
            for v in x:
                yield from walk(v)
    yield from walk(d)


def record(m: dict, g: dict | None, **extra) -> dict:
    """The primary record of one document: the model's verdict and counts,
    and (when graded) the grade and pdfTeX's capacity report."""
    r = {"sha256": hashlib.sha256(m["tex"].encode()).hexdigest(),
         "verdict": m["verdict"], "reason": m.get("reason"), "ntoks": m["ntoks"],
         "held": m.get("held"), "peak": m.get("peak_groups"), **extra}
    if g is not None:
        agree, why = S.agrees(m, g)
        r.update({"oracle": [g["rc"], g["pdf"], g["error"], g["line"]],
                  "stats": g.get("stats", {}), "agree": agree, "why": why})
    return r


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--out", default=str(OUT))
    ap.add_argument("--reuse", nargs="*", default=[],
                    help="COMMITTED capacity files (REV:path) whose grades of "
                         "byte-identical documents are reused")
    args = ap.parse_args()
    oracle = _oracle.get_oracle()
    kern = S.Kernel()
    sig = json.loads(S.SIGNATURES.read_text())["signatures"]
    asig = json.loads(S.ARG_SIGNATURES.read_text())["arg_signatures"]
    groups = C.arg_groups(asig)
    wt = C.dim_weight(asig, json.loads(S.SIGNATURES.read_text())["dims"])
    pairs = kern.frame_pairs()
    G = Grades(oracle, args.reuse)
    t0 = time.time()

    def pmap(f, xs):
        with ThreadPoolExecutor(args.workers) as ex:
            return list(ex.map(f, xs))

    # ---- 2. the pairs: at the bound, past it, pdfTeX's own overflow --------
    def one_pair(p):
        b, a = p["below"], p["above"]
        at = C.stream(pairs, b, a, MAX_GROUPS, groups, wt, C.STREAM_BUDGET)
        past = C.stream(pairs, b, a, MAX_GROUPS + 1, groups, wt, C.STREAM_BUDGET)
        if at is None or past is None:
            return {"below": b, "above": a, "error": "no stream reaches the bound"}
        m, mp = kern.run([C.request(at[0]), C.request(past[0])])
        g = G.grade(m["tex"])
        rec = {"below": b, "above": a, "chain": at[1],
               "at": record(m, g, frames=m["peak_frames"],
                            adjacent=C.adjacent(m["peak_frames"], b, a)),
               "past": record(mp, G.grade(mp["tex"]))}
        # pdfTeX's own overflow, by bisection over the target; EVERY step is
        # recorded (the gate recomputes the first failing target from them)
        steps = []

        def probe(T):
            sm = C.stream(pairs, b, a, T, groups, wt, C.STREAM_BUDGET)
            mm = kern.run([C.request(sm[0])])[0]
            gm = G.grade(mm["tex"])
            steps.append(record(mm, gm, target=T))
            return gm["rc"] == 0 and gm["pdf"]
        lo, hi = MAX_GROUPS, SEARCH_HI
        if not probe(hi):
            while hi - lo > 1:
                mid = (lo + hi) // 2
                if probe(mid):
                    lo = mid
                else:
                    hi = mid
        rec["overflow_steps"] = sorted(steps, key=lambda r: r["target"])
        return rec

    recs = []
    for i, r in enumerate(pmap(one_pair, pairs["pairs"])):
        recs.append(r)
    print(f"[capacity] {len(recs)} pairs ({time.time() - t0:.0f}s)", flush=True)

    # ---- 3. transients: the deepest nesting each construct survives --------
    x = S.text("x")

    def nest(k, inner):
        node = inner
        for _ in range(k):
            node = [S.group(*node)]
        return node

    trans_fams = {
        "paragraph_start": lambda k: {"doc": S.doc(*nest(k, [x]))},
        "display_bracket": lambda k: {"doc": S.doc(x, *nest(k, [S.math("bracket", x)]))},
        "page_break": lambda k: {"doc": S.doc(*nest(k, [n for _ in range(300)
                                                         for n in (x, S.par())]))},
        "end_document_open": lambda k: {"toks": [["open"]] * k + [["char", "x"], ["end"]]},
        "none_in_math": lambda k: {"doc": S.doc(S.math("paren", *nest(k, [x])))},
    }

    def deepest(fam):
        mk, steps = trans_fams[fam], []

        def probe(k):
            mm = kern.run([mk(k)])[0]
            gm = G.grade(mm["tex"])
            steps.append(record(mm, gm, depth=k))
            return gm["rc"] == 0 and gm["pdf"]
        lo, hi = 150, 300
        if probe(lo) and not probe(hi):
            while hi - lo > 1:
                mid = (lo + hi) // 2
                if probe(mid):
                    lo = mid
                else:
                    hi = mid
        return {"steps": sorted(steps, key=lambda r: r["depth"])}

    trans = dict(zip(trans_fams, pmap(deepest, list(trans_fams))))
    print(f"[capacity] transients ({time.time() - t0:.0f}s)", flush=True)

    # ---- 4. usage at the other bounds ---------------------------------------
    names = undef_names(MAX_TOKENS - 10, S.members())
    runner = sorted(n for n, h in asig.items() if h["text"][0] == "run")[0]
    mathname = sorted(n for n, h in sig.items() if h["math"] == "noad")[0]
    s1d = json.loads(S.SIGNATURES.read_text())
    dz = DM.Dims(s1d["dims"], {n: v["dim"] for n, v in sig.items()}, asig)

    def to_bound(mk):
        """mk(k) cut within the dimension bound, with k as large as the token
        bound allows."""
        lo, hi = 0, MAX_TOKENS
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if kern.run([{"doc": dz.segment(S, mk(mid))}])[0]["verdict"] != "not_strict":
                lo = mid
            else:
                hi = mid - 1
        return dz.segment(S, mk(lo))
    usage_docs = {
        "tokens_text": to_bound(lambda k: S.doc(S.text("x" * k))),
        "tokens_math": to_bound(lambda k: S.doc(S.math("paren", *[S.cmd(mathname)] * k))),
        # an INSTRUMENT of the buffer (outside the fragment since C-104: the
        # account charges a space its dimensions even where TeX drops it)
        "longest_line": S.doc(*[S.space()] * (MAX_TOKENS - 2), S.cmd("q" * MAX_NAME)),
        "most_names": S.doc(S.cmd(runner), S.group(*[S.cmd(n) for n in names])),
    }
    um = kern.run([{"doc": d} for d in usage_docs.values()])
    usage_rec = {f: record(m, g) for f, m, g in
                 zip(usage_docs, um, pmap(lambda m: G.grade(m["tex"]), um))}

    # ---- 5. main memory (C-98) --------------------------------------------
    # The account is attested by the generators, per name and command (costs,
    # copy factors, the worst case at the bound and one past it); this file
    # records the account's constants and the margin they give, for the
    # design's table. check_strict_kernel.py recomputes all of it from the
    # generators' primary records.
    s1 = json.loads(S.SIGNATURES.read_text())
    a1 = json.loads(S.ARG_SIGNATURES.read_text())
    m0 = s1["memory"]["structural"]["BASE"]["used"]
    cap_words = s1["memory"]["structural"]["BASE"]["of"]
    worst = [(n, w, r["at"]["used"]) for n, d in a1["capacity"]["memory_bound"].items()
             if isinstance(d, dict) for w, r in d.items() if isinstance(r, dict) and "at" in r]
    memory = {"M0": m0, "capacity": cap_words, "max_mem": S.MAX_MEM,
              "token_cost": s1["token_cost"],
              "account": "used <= M0 + mem (Decide.mem <= max_mem)",
              "predicted_worst": m0 + S.MAX_MEM,
              "margin": round(cap_words / (m0 + S.MAX_MEM), 3),
              "maximiser_worst_measured": max(worst, key=lambda q: q[2]) if worst else None}

    out = {
        "schema": "lp-strict-capacity/2",
        "generator": "scripts/tools/measure_strict_capacity.py",
        "generator_version": GENERATOR_VERSION,
        "correction": "C-94, C-98, C-104",
        "oracle": oracle.provenance(),
        "source": S.source_block(),
        "kernel_extract_sha256": S.sha256_file(S.EXTRACT),
        "signatures_sha256": S.sha256_file(S.SIGNATURES),
        "arg_signatures_sha256": S.sha256_file(S.ARG_SIGNATURES),
        "bounds": {"max_groups": MAX_GROUPS, "max_tokens": MAX_TOKENS,
                   "max_name": MAX_NAME, "max_mem": S.MAX_MEM, "max_dim": DM.DIM_BOUND},
        "texmf": texmf(oracle),
        "frame_pairs": {"depth": pairs["depth"], "alphabet": pairs["alphabet"],
                        "n": len(pairs["pairs"])},
        "reuse": {"grades_reused": G.reused, "sources": G.sources},
        "transients": trans,
        "usage": usage_rec,
        "memory": memory,
        "pairs": recs,
        "seconds": round(time.time() - t0),
    }
    Path(args.out).write_text(json.dumps(out, indent=1) + "\n")
    print(f"[capacity] done ({out['seconds']}s): memory {memory}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
