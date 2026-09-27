#!/usr/bin/env python3
"""The generated differential of the strict kernel L_S0, v1 (ADR-012, M2 phase 1).

WHAT IT MEASURES. Trust layer (3) of the design (STRICT_TIER_DESIGN.md §0):
that the semantics `Runs` (proofs/Strict/Semantics.v) describes real pdflatex.
That is the premise `Faithful` of the bridge corollary; it cannot be proved,
only attested. This tool attests it by disagreement search:

  * it GENERATES documents of the fragment (random node trees, weighted toward
    the boundaries: mode switches, $/$$ adjacency, script nesting and double
    scripts, brace balance and stray braces, blank lines in math, undefined
    and attested control words, missing \\end{document});
  * the EXTRACTED Coq decider (`strict_decide.exe` over
    latex-parse/strict/strict_kernel_extracted.ml) gives each document's
    verdict, reason and location, and the EXTRACTED renderer gives the exact
    bytes;
  * the ONE oracle (`_oracle.py`, the pinned image) grades those bytes;
  * `_strict_s0.agrees` compares them: verdict, reason class (the pdfTeX
    message) and line. Any disagreement is an F-defect (design §E): either the
    semantics or the harness is wrong, and it is reported in full.

Results are reported per verdict class (READY, E0, E1, E3, E4, E5, E6) and
per `Runs` constructor (which rules each document's run used, as labelled by
the driver).

Two modes:
  --rules            the directed probe families of Semantics.v (a few
                     documents per constructor), written to
                     corpora/strict_s0/rule_probes.json
  --random N         N generated documents (seeded, reproducible), written to
                     corpora/strict_s0/differential_v1.json

Needs the oracle (docker and the pinned image); local or nightly, never in the
pure CI jobs (the OPEN-101 lesson). Usage:
    python3 scripts/tools/strict_differential.py --rules
    python3 scripts/tools/strict_differential.py --random 1000 --seed 1
"""
from __future__ import annotations

import argparse
import hashlib
import json
import random
import re
import sys
import time
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import _oracle  # noqa: E402
import _strict_s0 as S  # noqa: E402
from _strict_s0 import cmd, doc, group, par, script, space, stray, text  # noqa: E402

GENERATOR_VERSION = "1"
OUT_DIR = S.REPO / "corpora/strict_s0"
RULES = [
    "R_eof", "R_end_ok", "R_end_empty", "R_end_math", "R_char_text", "R_char_math",
    "R_space", "R_par_text", "R_par_math", "R_open_text", "R_open_math",
    "R_close_simple", "R_close_group", "R_close_shift", "R_close_top",
    "R_dollar_display_open", "R_dollar_inline_open", "R_dollar_inline_close",
    "R_dollar_display_close", "R_dollar_display_undef", "R_dollar_display_bad",
    "R_dollar_display_eof", "R_dollar_group", "R_mopen_inline", "R_mopen_inline_bad",
    "R_mclose_inline", "R_mclose_inline_bad", "R_mopen_display",
    "R_mopen_display_bad", "R_mclose_display", "R_mclose_display_bad",
    "R_script_text", "R_script_double", "R_script_char", "R_script_group",
    "R_cs_undefined", "R_cs_text_material", "R_cs_text_noop", "R_cs_text_fatal",
    "R_cs_math_noad", "R_cs_math_noop", "R_cs_math_fatal",
]


def dollar(*b): return S.math("dollar", *b)
def display(*b): return S.math("display", *b)
def paren(*b): return S.math("paren", *b)
def bracket(*b): return S.math("bracket", *b)
def sup(a): return script(True, a)
def sub(a): return script(False, a)


def _cls(h) -> str:
    return h if isinstance(h, str) else "fatal"


class Names:
    """Attested names by class (from the signature file) and undefined names
    (random letter strings and mutations of attested names, each checked to
    be OUTSIDE the closed world)."""

    def __init__(self, sig_path: Path, rng: random.Random):
        self.members = S.members()
        sig = json.loads(Path(sig_path).read_text())["signatures"]
        self.sigs = sig
        self.all = sorted(sig)
        self.text_ok = [n for n in self.all if _cls(sig[n]["text"]) != "fatal"]
        self.math_ok = [n for n in self.all if _cls(sig[n]["math"]) != "fatal"]
        self.by = defaultdict(list)
        for n in self.all:
            self.by["text_" + _cls(sig[n]["text"])].append(n)
            self.by["math_" + _cls(sig[n]["math"])].append(n)
        self.rng = rng
        letters = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
        pool = set()
        while len(pool) < 200:
            if self.all and rng.random() < 0.5:
                b = list(rng.choice(self.all))
                if len(b) > 2 and rng.random() < 0.5:
                    i = rng.randrange(len(b) - 1)
                    b[i], b[i + 1] = b[i + 1], b[i]
                else:
                    b.insert(rng.randrange(len(b) + 1), rng.choice(letters))
                c = "".join(b)
            else:
                c = "".join(rng.choice(letters) for _ in range(rng.randint(2, 9)))
            if c not in self.members:
                pool.add(c)
        self.undefined = sorted(pool)

    def first(self, key: str) -> str | None:
        return self.by[key][0] if self.by[key] else None


# ----------------------------------------------------------- directed ---

def rule_docs(nm: Names) -> list[tuple[str, dict]]:
    """(family, request): a request is {"doc": tree} or {"toks": stream}."""
    u = nm.undefined[0]
    x = text("x")
    fam: list[tuple[str, dict]] = [
        ("R_eof", doc(x, has_end=False)),
        ("R_eof", doc(has_end=False)),
        ("R_eof", doc(group(x), dollar(text("y")), has_end=False)),
        ("R_end_ok", doc(x)),
        ("R_end_ok", doc(group(x), space(), par())),
        ("R_end_empty", doc()),
        ("R_end_empty", doc(space(), par(), par(True))),
        ("R_end_empty", doc(group(group(space())))),
        ("R_end_math", doc(dollar())),
        ("R_end_math", doc(text("a"), dollar(), text("b"))),
        ("R_end_math", doc(dollar(x), dollar())),
        ("R_char_text", doc(text("Az09.,;:!?()/+-="))),
        ("R_char_math", doc(dollar(text("a+b=c-(d/e)")))),
        ("R_space", doc(space(), x, space(), space())),
        ("R_space", doc(dollar(space(), x, space()))),
        ("R_par_text", doc(x, par(), text("y"), par(True), text("z"))),
        ("R_par_text", doc(group(x, par(), text("y")))),
        ("R_par_math", doc(dollar(x, par()))),
        ("R_par_math", doc(display(x, par(True)))),
        ("R_par_math", doc(display(x, par()))),
        ("R_par_math", doc(dollar(group(par())))),
        ("R_par_math", doc(dollar(x, sup(group(par()))))),
        ("R_par_math", doc(dollar(x, space(), space(), par()))),
        ("R_open_text", doc(group(group(x)))),
        ("R_open_math", doc(dollar(x, sup(text("a")), group(), sup(text("b"))))),
        ("R_close_simple", doc(group(x), group())),
        ("R_close_group", doc(dollar(group(x), sup(text("a"))))),
        ("R_close_shift", doc(dollar(x, stray()))),
        ("R_close_shift", doc(display(stray()))),
        ("R_close_top", doc(stray())),
        ("R_close_top", doc(x, stray())),
        ("R_close_top", doc(group(stray()), x)),
        ("R_dollar_display_open", doc(display(x))),
        ("R_dollar_display_open", doc(text("a"), display(x), text("b"))),
        ("R_dollar_inline_open", doc(dollar(x))),
        ("R_dollar_inline_open", doc(dollar(space()))),
        ("R_dollar_inline_close", doc(dollar(x), dollar(text("y")))),
        ("R_dollar_inline_close", doc(paren(x, dollar()))),
        ("R_dollar_display_close", doc(display(x), display(text("y")))),
        ("R_dollar_display_close", doc(bracket(x, dollar()))),
        ("R_dollar_display_undef", doc(display(x, dollar(cmd(u))))),
        ("R_dollar_display_bad", doc(display(x, dollar(text("y"))))),
        ("R_dollar_display_bad", doc(display(x, dollar(space())))),
        ("R_dollar_display_bad", doc(display(x, dollar(group())))),
        ("R_dollar_display_bad", doc(display(x, dollar(par())))),
        ("R_dollar_display_bad", doc(bracket(dollar(x)))),
        ("R_dollar_group", doc(dollar(group(dollar(x))))),
        ("R_dollar_group", doc(dollar(x, sup(group(dollar()))))),
        ("R_dollar_group", doc(display(group(dollar())))),
        ("R_mopen_inline", doc(paren(x))),
        ("R_mopen_inline", doc(paren())),
        ("R_mopen_inline_bad", doc(dollar(paren(x)))),
        ("R_mopen_inline_bad", doc(display(paren()))),
        ("R_mclose_inline", doc(dollar(x, paren()))),
        ("R_mclose_inline_bad", doc(paren(dollar(), dollar()))),
        ("R_mopen_display", doc(bracket(x))),
        ("R_mopen_display", doc(text("a"), bracket(), text("b"))),
        ("R_mopen_display_bad", doc(dollar(bracket()))),
        ("R_mopen_display_bad", doc(display(bracket(x)))),
        ("R_mclose_display", doc(display(x, bracket()))),
        ("R_mclose_display_bad", doc(bracket(x, dollar(), bracket()))),
        ("R_mclose_display_bad", doc(display(group(bracket())))),
        ("R_script_text", doc(x, sup(text("a")))),
        ("R_script_text", doc(sub(group(x)))),
        ("R_script_text", doc(dollar(x), sup(text("a")))),
        ("R_script_double", doc(dollar(x, sup(text("a")), sup(text("b"))))),
        ("R_script_double", doc(dollar(x, sub(group(x)), sup(x), sub(x)))),
        ("R_script_double", doc(dollar(sup(group()), sup(group())))),
        ("R_script_double", doc(dollar(x, sup(text("a")), space(), sup(text("b"))))),
        ("R_script_char", doc(dollar(x, sup(text("a")), sub(text("b"))))),
        ("R_script_group", doc(dollar(x, sup(group(text("a"), sup(text("b"))))))),
        ("R_script_group", doc(display(sub(group()), sup(group(x))))),
        ("R_cs_undefined", doc(cmd(u))),
        ("R_cs_undefined", doc(dollar(x, cmd(u)))),
    ]
    # Token-level probes: rules of Runs that no node tree reaches, or reaches
    # only through another rule first. They run through the extracted [run]
    # from [init] (by run_sound/run_complete, exactly [Runs]).
    T = lambda *ts: {"toks": [list(t) if isinstance(t, tuple) else [t] for t in ts]}
    fam += [
        ("R_dollar_display_eof", T("dollar", "dollar", ("char", "x"), "dollar")),
        ("R_mclose_inline_bad", T("close_paren", "end")),
        ("R_mclose_inline_bad", T("dollar", "dollar", "close_paren", "dollar", "dollar", "end")),
        ("R_mclose_inline_bad", T("dollar", "dollar", "open", "close_paren", "close", "dollar", "dollar", "end")),
        ("R_mclose_inline_bad", T("dollar", "open", "close_paren", "close", "dollar", "end")),
        ("R_end_math", T("open_bracket", ("char", "x"), "end")),
        ("R_end_math", T("dollar", "open", ("char", "x"), "end")),
        ("R_end_ok", T("open", ("char", "x"), "end")),
        ("R_dollar_display_close", T("open_bracket", ("char", "x"), "dollar", "dollar", "end")),
        ("R_mclose_display", T("dollar", "dollar", ("char", "x"), "close_bracket", "end")),
        ("R_mclose_inline", T("dollar", ("char", "x"), "close_paren", "end")),
        ("R_dollar_inline_close", T("open_paren", ("char", "x"), "dollar", "end")),
        ("R_dollar_display_bad", T("open_bracket", ("char", "x"), "dollar", "close_bracket", "end")),
        ("R_dollar_display_bad", T("dollar", "dollar", ("char", "x"), "dollar", "end")),
        ("R_mclose_display_bad", T("close_bracket", "end")),
        ("R_mclose_display_bad", T("dollar", ("char", "x"), "close_bracket", "end")),
    ]
    for key, rule, mk in (
        ("text_material", "R_cs_text_material", lambda n: doc(cmd(n))),
        ("text_noop", "R_cs_text_noop", lambda n: doc(cmd(n), x)),
        ("text_fatal", "R_cs_text_fatal", lambda n: doc(text("a"), cmd(n))),
        ("math_noad", "R_cs_math_noad",
         lambda n: doc(dollar(x, sup(text("a")), cmd(n), sup(text("b"))))),
        ("math_noop", "R_cs_math_noop",
         lambda n: doc(dollar(x, sup(text("a")), cmd(n), sub(text("b"))))),
        ("math_fatal", "R_cs_math_fatal", lambda n: doc(dollar(x, cmd(n)))),
    ):
        for n in nm.by[key][:3]:
            fam.append((rule, mk(n)))
    return [(f, r if "toks" in r else {"doc": r}) for f, r in fam]


# ---------------------------------------------------------- generated ---

SAFE = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789.,;:!?()/+-="


class Gen:
    def __init__(self, rng: random.Random, nm: Names):
        self.r, self.nm = rng, nm

    def pick(self, weighted):
        tot = sum(w for w, _ in weighted)
        x = self.r.random() * tot
        for w, v in weighted:
            x -= w
            if x < 0:
                return v
        return weighted[-1][1]

    def word(self, lo=1, hi=3):
        return "".join(self.r.choice(SAFE if self.r.random() < 0.3 else SAFE[:52])
                       for _ in range(self.r.randint(lo, hi)))

    def name(self, mode: str, clean: bool) -> str:
        if not clean and self.r.random() < 0.2:
            return self.r.choice(self.nm.undefined)
        pool = (self.nm.text_ok if mode == "text" else self.nm.math_ok) if clean \
            else self.nm.all
        return self.r.choice(pool or self.nm.all)

    def seq(self, depth: int, mode: str, clean: bool, lo=0, hi=5) -> list:
        return [self.node(depth, mode, clean) for _ in range(self.r.randint(lo, hi))]

    def math_node(self, depth: int, clean: bool):
        kind = self.pick([(4, "dollar"), (2, "display"), (2, "paren"), (2, "bracket")])
        return S.math(kind, *self.seq(depth + 1, "math", clean, 0, 5))

    def node(self, depth: int, mode: str, clean: bool):
        deep = depth >= 3
        if mode == "text":
            ch = self.pick([
                (20, "text"), (7, "space"), (5, "par"), (0 if deep else 7, "group"),
                (0 if clean else 2, "stray"), (0 if deep else 18, "math"),
                (12, "cmd"), (0 if clean else 3, "script")])
        else:
            ch = self.pick([
                (18, "text"), (4, "space"), (0 if clean else 2, "par"),
                (0 if deep else 9, "group"), (0 if clean else 2, "stray"),
                (0 if deep or clean else 3, "math"), (12, "cmd"),
                (0 if deep else 20, "script")])
        if ch == "text":
            return text(self.word(1, 3 if mode == "text" else 2))
        if ch == "space":
            return space()
        if ch == "par":
            return par(self.r.random() < 0.3)
        if ch == "group":
            return group(*self.seq(depth + 1, mode, clean, 0, 4))
        if ch == "stray":
            return stray()
        if ch == "math":
            return self.math_node(depth, clean)
        if ch == "cmd":
            return cmd(self.name(mode, clean))
        # script: a character or a group argument
        up = self.r.random() < 0.5
        if self.r.random() < 0.6:
            return script(up, text(self.word(1, 2)))
        return script(up, group(*self.seq(depth + 1, "math", clean, 0, 3)))

    def document(self) -> dict:
        clean = self.r.random() < 0.4
        body = self.seq(0, "text", clean, 0, 6)
        if clean and self.r.random() < 0.5:
            body = [self.math_node(0, True) if self.r.random() < 0.6 else text(self.word())] + body
        return doc(*body, has_end=self.r.random() > 0.05)


# ------------------------------------------------------------- running ---

def run_all(requests: list[dict], sig_path: Path, workers: int, label: str):
    kern = S.Kernel(signatures=sig_path)
    models = kern.run(requests)
    oracle = _oracle.get_oracle()
    t0, done = time.time(), [0]

    def g(m):
        try:
            r = S.grade(oracle, m["tex"])
        except _oracle.OracleError as e:
            r = {"infra": str(e)[:300]}
        done[0] += 1
        if done[0] % 100 == 0:
            print(f"[{label}] graded {done[0]}/{len(models)} "
                  f"({time.time() - t0:.0f}s)", flush=True)
        return r

    with ThreadPoolExecutor(workers) as ex:
        grades = list(ex.map(g, models))
    return kern, oracle, models, grades


def tally(docs, models, grades, families=None):
    by_class = defaultdict(lambda: {"n": 0, "agree": 0})
    by_rule = {r: {"docs": 0, "agree": 0} for r in RULES}
    by_family = defaultdict(lambda: {"n": 0, "agree": 0, "exercised": 0})
    disagreements, records, infra = [], [], []
    for i, (d, m, g) in enumerate(zip(docs, models, grades)):
        if "infra" in g:
            infra.append({"i": i, "error": g["infra"]})
            continue
        ok, why = S.agrees(m, g)
        cls = S.verdict_class(m)
        by_class[cls]["n"] += 1
        by_class[cls]["agree"] += ok
        for r in m.get("rules", []):
            by_rule.setdefault(r, {"docs": 0, "agree": 0})
            by_rule[r]["docs"] += 1
            by_rule[r]["agree"] += ok
        rec = {"i": i, "class": cls, "agree": ok,
               "tex_sha256": hashlib.sha256(m["tex"].encode()).hexdigest()[:16],
               "oracle": [g["rc"], g["pdf"], g["error"], g["line"]]}
        if m["verdict"] == "not_ready":
            rec["model"] = [m["reason"], m["loc_tok"], m["loc_mode"], m["loc_line"]]
        if families is not None:
            f = families[i]
            by_family[f]["n"] += 1
            by_family[f]["agree"] += ok
            by_family[f]["exercised"] += f in m.get("rules", [])
            rec["family"] = f
            rec["doc"] = d
            rec["rules"] = m.get("rules", [])
        records.append(rec)
        if not ok:
            disagreements.append({"i": i, "why": why, "doc": d, "tex": m["tex"],
                                  "model": {k: m.get(k) for k in (
                                      "verdict", "reason", "loc", "loc_tok",
                                      "loc_mode", "loc_line", "rules")},
                                  "oracle": g})
    return by_class, by_rule, by_family, disagreements, records, infra


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--rules", action="store_true")
    ap.add_argument("--random", type=int, default=0)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--signatures", default=str(S.SIGNATURES))
    ap.add_argument("--out")
    args = ap.parse_args()
    sig_path = Path(args.signatures)
    nm = Names(sig_path, random.Random(args.seed))

    if args.rules:
        fam = rule_docs(nm)
        docs = [d for _, d in fam]  # requests
        families = [f for f, _ in fam]
        label, default_out = "rules", OUT_DIR / "rule_probes.json"
    elif args.random:
        gen = Gen(random.Random(args.seed), nm)
        docs = [{"doc": gen.document()} for _ in range(args.random)]
        families = None
        label, default_out = "random", OUT_DIR / "differential_v1.json"
    else:
        ap.error("give --rules or --random N")
    kern, oracle, models, grades = run_all(docs, sig_path, args.workers, label)
    not_strict = [i for i, m in enumerate(models) if m["verdict"] == "not_strict"]
    by_class, by_rule, by_family, dis, records, infra = tally(
        docs, models, grades, families)
    graded = sum(v["n"] for v in by_class.values())
    summary = {
        "documents": len(docs),
        "graded": graded,
        "agree": sum(v["agree"] for v in by_class.values()),
        "disagree": len(dis),
        "not_strict_generated": len(not_strict),
        "oracle_infrastructure_failures": len(infra),
        "oracle_timeouts": sum(1 for g in grades if g.get("timed_out")),
        "by_class": {k: by_class[k] for k in sorted(by_class)},
        "rules_never_exercised": [r for r in RULES if by_rule.get(r, {}).get("docs", 0) == 0],
    }
    out = {
        "schema": "lp-strict-differential/1",
        "generator": "scripts/tools/strict_differential.py",
        "generator_version": GENERATOR_VERSION,
        "mode": label,
        "seed": args.seed,
        "source": S.source_block(),
        "signatures_sha256": S.sha256_file(sig_path),
        "kernel_extract_sha256": S.sha256_file(S.EXTRACT),
        "oracle": oracle.provenance(),
        "agreement_rule": "_strict_s0.agrees: READY iff rc 0 and a PDF; E0 iff rc 0 "
                          "and no PDF; any other reason iff rc != 0, the first ! "
                          "message is in _strict_s0.expected_messages(reason, token, "
                          "mode), and the fatal token's line equals the oracle's l.N",
        "summary": summary,
        "by_rule": by_rule,
        "disagreements": dis,
        "infrastructure_failures": infra,
    }
    if families is not None:
        out["by_family"] = {f: by_family[f] for f in RULES if f in by_family}
        out["probes"] = records
    else:
        out["documents"] = records
    path = Path(args.out) if args.out else default_out
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(out, indent=1) + "\n")
    print(json.dumps(summary, indent=1))
    for d in dis[:20]:
        print("DISAGREE", d["i"], d["why"])
        print("   ", json.dumps(d["doc"]))
    return 1 if dis or infra else 0


if __name__ == "__main__":
    sys.exit(main())
