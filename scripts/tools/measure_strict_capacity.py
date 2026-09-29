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

GENERATOR_VERSION = "1"
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


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--out", default=str(OUT))
    args = ap.parse_args()
    oracle = _oracle.get_oracle()
    kern = S.Kernel()
    asig = json.loads(S.ARG_SIGNATURES.read_text())
    groups = C.arg_groups(asig["arg_signatures"])
    pairs = kern.frame_pairs()
    t0 = time.time()

    def grade(tex: str) -> dict:
        return S.grade(oracle, tex, stats=True)

    # ---- 2. the pairs at the bound, past it, and pdfTeX's own overflow ----
    items = []
    for p in pairs["pairs"]:
        b, a = p["below"], p["above"]
        at = C.stream(pairs, b, a, MAX_GROUPS, groups)
        past = C.stream(pairs, b, a, MAX_GROUPS + 1, groups)
        if at is None or past is None:
            items.append({"below": b, "above": a, "error": "no stream reaches the bound"})
            continue
        items.append({"below": b, "above": a, "at": at, "past": past})
    reqs = [C.request(it[k][0]) for it in items if "at" in it for k in ("at", "past")]
    models = kern.run(reqs)
    k = 0
    for it in items:
        if "at" not in it:
            continue
        for key in ("at", "past"):
            it[key + "_model"] = models[k]
            k += 1

    def one(it):
        if "at" not in it:
            return it
        m = it["at_model"]
        g = grade(m["tex"])
        agree, why = S.agrees(m, g)
        rec = {"below": it["below"], "above": it["above"],
               "chain": it["at"][1],
               "at": {"peak": m["peak_groups"], "frames": m["peak_frames"],
                      "adjacent": C.adjacent(m["peak_frames"], it["below"], it["above"]),
                      "verdict": m["verdict"], "reason": m.get("reason"),
                      "sha256": hashlib.sha256(m["tex"].encode()).hexdigest(),
                      "oracle": [g["rc"], g["pdf"], g["error"], g["line"]],
                      "stats": g.get("stats", {}), "agree": agree, "why": why}}
        mp = it["past_model"]
        gp = grade(mp["tex"])
        rec["past"] = {"peak": mp["peak_groups"], "verdict": mp["verdict"],
                       "oracle": [gp["rc"], gp["pdf"], gp["error"], gp["line"]]}
        # pdfTeX's own overflow: the first failing peak, by bisection over the
        # target (every target is met exactly; costs are 1 or a measured g)
        lo, hi = MAX_GROUPS + 1, SEARCH_HI
        if gp["rc"] != 0:
            lo = MAX_GROUPS
        hs = C.stream(pairs, it["below"], it["above"], hi, groups)
        mh = kern.run([C.request(hs[0])])[0]
        gh = grade(mh["tex"])
        if gh["rc"] == 0:
            rec["overflow"] = {"first_fail": None, "searched_to": hi}
            return rec
        fail_err = gh["error"]
        while hi - lo > 1:
            mid = (lo + hi) // 2
            sm = C.stream(pairs, it["below"], it["above"], mid, groups)
            if sm is None:
                break
            mm = kern.run([C.request(sm[0])])[0]
            gm = grade(mm["tex"])
            if gm["rc"] == 0 and gm["pdf"]:
                lo = mid
            else:
                hi, fail_err = mid, gm["error"]
        rec["overflow"] = {"first_fail": hi, "last_ok": lo, "error": fail_err}
        return rec

    with ThreadPoolExecutor(args.workers) as ex:
        recs = []
        for i, r in enumerate(ex.map(one, items)):
            recs.append(r)
            if (i + 1) % 20 == 0:
                print(f"[capacity] pairs {i + 1}/{len(items)} ({time.time() - t0:.0f}s)",
                      flush=True)

    # ---- 3. transients: the deepest simple nesting each construct survives --
    x = S.text("x")

    def nest(k, inner):
        node = inner
        for _ in range(k):
            node = [S.group(*node)]
        return node

    # requests: a tree, or a token stream (\end{document} inside k open
    # braces, which a tree cannot express)
    trans_fams = {
        "paragraph_start": lambda k: {"doc": S.doc(*nest(k, [x]))},
        "display_bracket": lambda k: {"doc": S.doc(x, *nest(k, [S.math("bracket", x)]))},
        "page_break": lambda k: {"doc": S.doc(*nest(k, [n for _ in range(300)
                                                         for n in (x, S.par())]))},
        "end_document_open": lambda k: {"toks": [["open"]] * k + [["char", "x"], ["end"]]},
        "none_in_math": lambda k: {"doc": S.doc(S.math("paren", *nest(k, [x])))},
    }

    def deepest(fam):
        mk = trans_fams[fam]
        lo, hi = 150, 300
        ok = kern.run([mk(lo), mk(hi)])
        g_lo, g_hi = grade(ok[0]["tex"]), grade(ok[1]["tex"])
        if not (g_lo["rc"] == 0 and g_lo["pdf"]) or (g_hi["rc"] == 0):
            return {"error": "bracket search failed", "lo": g_lo["error"], "hi": g_hi["error"]}
        peak_lo, err = ok[0]["peak_groups"], g_hi["error"]
        while hi - lo > 1:
            mid = (lo + hi) // 2
            mm = kern.run([mk(mid)])[0]
            gm = grade(mm["tex"])
            if gm["rc"] == 0 and gm["pdf"]:
                lo, peak_lo = mid, mm["peak_groups"]
            else:
                hi, err = mid, gm["error"]
        return {"last_ok_peak": peak_lo, "error": err}

    with ThreadPoolExecutor(args.workers) as ex:
        trans = dict(zip(trans_fams, ex.map(deepest, list(trans_fams))))

    # ---- 4. usage at the other bounds -------------------------------------
    members = S.members()
    names = undef_names(MAX_TOKENS - 10, members)
    sig = json.loads(S.SIGNATURES.read_text())["signatures"]
    runner = sorted(n for n, h in asig["arg_signatures"].items() if h["text"][0] == "run")[0]
    mathname = sorted(n for n, h in sig.items() if h["math"] == "noad")[0]
    usage_docs = {
        "tokens_text": S.doc(S.text("x" * (MAX_TOKENS - 1))),
        "tokens_math": S.doc(S.math("paren", *[S.cmd(mathname)] * (MAX_TOKENS - 3))),
        "longest_line": S.doc(*[S.space()] * (MAX_TOKENS - 2), S.cmd("q" * MAX_NAME)),
        "most_names": S.doc(S.cmd(runner), S.group(*[S.cmd(n) for n in names])),
    }
    um = kern.run([{"doc": d} for d in usage_docs.values()])
    with ThreadPoolExecutor(args.workers) as ex:
        ug = list(ex.map(lambda m: grade(m["tex"]), um))
    usage_rec = {}
    for (fam, _), m, g in zip(usage_docs.items(), um, ug):
        agree, why = S.agrees(m, g)
        usage_rec[fam] = {"verdict": m["verdict"], "reason": m.get("reason"),
                          "ntoks": m["ntoks"], "peak": m["peak_groups"],
                          "bytes": len(m["tex"]),
                          "oracle": [g["rc"], g["pdf"], g["error"], g["line"]],
                          "agree": agree, "why": why, "stats": g.get("stats", {})}

    # ---- the capacity table --------------------------------------------------
    ok_pairs = [r for r in recs if "at" in r]
    capacity = max((r["overflow"]["first_fail"] - 1 for r in ok_pairs
                    if r.get("overflow", {}).get("first_fail")), default=None)
    t_max = max((capacity - v["last_ok_peak"] for v in trans.values()
                 if "last_ok_peak" in v), default=None)
    table = {}
    sources = [(f"pair {r['below']}>{r['above']}", r["at"]["stats"]) for r in ok_pairs] + \
        [(f"usage {f}", v["stats"]) for f, v in usage_rec.items()]
    for src, st in sources:
        for res, (used, of) in st.items():
            cur = table.get(res)
            if cur is None or used > cur["max_used"]:
                table[res] = {"max_used": used, "capacity": of, "at": src,
                              "fraction": round(used / of, 4) if of else None}
    out = {
        "schema": "lp-strict-capacity/1",
        "generator": "scripts/tools/measure_strict_capacity.py",
        "generator_version": GENERATOR_VERSION,
        "correction": "C-94",
        "oracle": oracle.provenance(),
        "source": S.source_block(),
        "kernel_extract_sha256": S.sha256_file(S.EXTRACT),
        "signatures_sha256": S.sha256_file(S.SIGNATURES),
        "arg_signatures_sha256": S.sha256_file(S.ARG_SIGNATURES),
        "bounds": {"max_groups": MAX_GROUPS, "max_tokens": MAX_TOKENS,
                   "max_name": MAX_NAME},
        "texmf": texmf(oracle),
        "frame_pairs": {"depth": pairs["depth"], "alphabet": pairs["alphabet"],
                        "n": len(pairs["pairs"])},
        "measured": {"grouping_capacity": capacity, "max_transient": t_max,
                     "margin": (capacity - t_max - MAX_GROUPS)
                     if capacity is not None and t_max is not None else None},
        "transients": trans,
        "usage": usage_rec,
        "table": table,
        "pairs": recs,
        "summary": {
            "pairs": len(recs),
            "at_bound_agree": sum(1 for r in ok_pairs if r["at"]["agree"]
                                  and r["at"]["peak"] == MAX_GROUPS and r["at"]["adjacent"]),
            "past_bound_outside": sum(1 for r in ok_pairs if r["past"]["verdict"] == "not_strict"
                                      and r["past"]["peak"] == MAX_GROUPS + 1),
            "overflow_in_window": sum(
                1 for r in ok_pairs if r.get("overflow", {}).get("first_fail")
                and capacity is not None and t_max is not None
                and capacity + 1 - t_max <= r["overflow"]["first_fail"] <= capacity + 1),
            "seconds": round(time.time() - t0),
        },
    }
    Path(args.out).write_text(json.dumps(out, indent=1) + "\n")
    print(f"[capacity] {out['summary']} capacity={capacity} max_transient={t_max}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
