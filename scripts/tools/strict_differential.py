#!/usr/bin/env python3
"""The generated differential of the strict kernel L_S0, v2 (ADR-012, M2 phase 1).

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
                     documents per constructor), the BRANCH MATRIX (every
                     innermost frame x every token class x, for the tokens
                     whose step reads the next token, every follower class;
                     C-85) and the BOUND family (the structure at the
                     capacity bounds of Decide.v; C-86), written to
                     corpora/strict_s0/rule_probes.json
  --random N         N generated documents (seeded, reproducible), written to
                     corpora/strict_s0/differential_v2.json

WHAT THE RANDOM MODE'S NUMBER MEANS. Its upper bound on the disagreement rate
is a bound over the documents THIS GENERATOR draws (its version, weights and
seed), not over the fragment L_S0: a class of documents the generator never
draws is not bounded at all. Version 1 drew no `$` in display math followed by
a name and no name repeated, and its 1,200/1,200 coexisted with two classes of
wrong verdicts (C-85). Version 2 adds those shapes (a display-$ follower,
runs of one to three names repeated up to 300 times, deep brace nesting up to
the bound) in clean and in failing documents; any class it still does not
draw is equally unbounded.

Needs the oracle (docker and the pinned image); local or nightly, never in the
pure CI jobs (the OPEN-101 lesson). Usage:
    python3 scripts/tools/strict_differential.py --rules
    python3 scripts/tools/strict_differential.py --random 3000 --seed 2
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

GENERATOR_VERSION = "2"
OUT_DIR = S.REPO / "corpora/strict_s0"
DIFFERENTIAL = OUT_DIR / "differential_v2.json"
MAX_BRACE_DEPTH, MAX_TOKENS = S.MAX_BRACE_DEPTH, S.MAX_TOKENS
# Families whose documents are OUTSIDE the tier by design (recorded, never
# graded): the bound's other side, and the matrix cells membership excludes.
EXPECT_NOT_STRICT = {"BOUND-OUT", "MATRIX-OUT"}
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
    fam += bound_docs()
    fam += matrix_docs(nm)
    return [(f, r if "toks" in r else {"doc": r}) for f, r in fam]


def _nest(depth: int, inner: list) -> list:
    node = inner
    for _ in range(depth):
        node = [group(*node)]
    return node


def _script_nest(depth: int) -> list:
    node = [text("x")]
    for _ in range(depth):
        node = [text("x"), sup(group(*node))]
    return node


def bound_docs() -> list[tuple[str, dict]]:
    """The structure AT the capacity bounds of Decide.v (inside the tier,
    graded) and one past them (outside the tier, recorded as such; C-86)."""
    B, L = MAX_BRACE_DEPTH, MAX_TOKENS
    x = text("x")
    return [
        ("BOUND", doc(*_nest(B, [x]))),
        ("BOUND", doc(x, *_nest(B, [x]))),
        ("BOUND", doc(dollar(*_nest(B, [x])))),
        ("BOUND", doc(display(*_nest(B, [x])))),
        ("BOUND", doc(dollar(*_script_nest(B)))),
        ("BOUND", doc(*_nest(B, [dollar(x), par(), x]))),
        ("BOUND", doc(text("x" * (L - 1)))),
        ("BOUND", doc(paren(text("x" * (L - 3))))),
        ("BOUND", doc(*[m for _ in range(L // 3) for m in (dollar(x),)][: L // 3 - 1])),
        ("BOUND-OUT", doc(*_nest(B + 1, [x]))),
        ("BOUND-OUT", doc(dollar(*_script_nest(B + 1)))),
        ("BOUND-OUT", doc(text("x" * L))),
    ]


# The BRANCH MATRIX (C-85; check_strict_kernel.py check 7). One token prefix
# per innermost frame class and tail state, then the token under test, then
# (for the tokens whose step reads the next token) the follower, then the
# frames the model has open, closed, and \end{document} (strict_decide.ml
# "close"). The cell labels are strict_decide.ml's `branch_of`.
MATRIX_HEADS = {
    "top0": [],
    "top1": [("char", "p")],
    "simple": [("char", "p"), "open"],
    "inline-": ["open_paren", ("char", "q")],
    "inline+": ["open_paren", ("char", "q"), "sup", ("char", "a"), "sub", ("char", "b")],
    "display-": ["open_bracket", ("char", "q")],
    "display+": ["dollar", "dollar", ("char", "q"), "sup", ("char", "a"), "sub", ("char", "b")],
    "mgroup-": ["open_paren", "open", ("char", "q")],
    "mgroup+": ["open_paren", ("char", "q"), "sup", "open", ("char", "q"), "sup",
                ("char", "a"), "sub", ("char", "b")],
}
MATRIX_TOKENS = [("char", "x"), "space", ("par", False), ("par", True), "open", "close",
                 "dollar", "open_paren", "close_paren", "open_bracket",
                 "close_bracket", "sup", "sub", "end"]
READS_NEXT = {"dollar", "sup", "sub"}


def _mcls(beh) -> str:
    return beh if isinstance(beh, str) else "fatal." + beh[1]


def matrix_docs(nm: "Names") -> list[tuple[str, dict]]:
    sig, u = nm.sigs, nm.undefined[0]
    text_rep, math_rep, pair_rep = {}, {}, {}
    for n in sorted(sig):
        text_rep.setdefault(_mcls(sig[n]["text"]), n)
        math_rep.setdefault(_mcls(sig[n]["math"]), n)
        pair_rep.setdefault((_mcls(sig[n]["text"]), _mcls(sig[n]["math"])), n)
    followers = MATRIX_TOKENS + [("cs", u)] + [("cs", n) for n in pair_rep.values()] + [None]
    out = []

    def tok(t):
        return list(t) if isinstance(t, tuple) else [t]

    for hname, prefix in MATRIX_HEADS.items():
        math = hname[0] in "idm"
        cs_toks = [("cs", u)] + [("cs", n) for n in (math_rep if math else text_rep).values()]
        for t in MATRIX_TOKENS + cs_toks:
            tl = t if isinstance(t, str) else t[0]
            fl = followers if tl in READS_NEXT else ["-"]
            for f in fl:
                toks = [tok(q) for q in prefix] + [tok(t)]
                if f == "-":
                    close = tl != "end"
                elif f is None:
                    close = False  # end of file right after the token
                else:
                    toks.append(tok(f))
                    close = (f if isinstance(f, str) else f[0]) != "end"
                    if f in ("sup", "sub"):
                        # a script needs its argument (Decide.v scripts_ok)
                        toks.append(["char", "a"])
                req = {"toks": toks}
                if close:
                    req["close"] = True
                ft = f if isinstance(f, (str, type(None))) else f[0]
                outside = tl in ("sup", "sub") and ft not in ("char",) and \
                    not (ft == "open")
                out.append(("MATRIX-OUT" if outside else "MATRIX", req))
    return out


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
        out = []
        for _ in range(self.r.randint(lo, hi)):
            if self.r.random() < 0.06:
                out += self.run(mode, clean)
            else:
                out.append(self.node(depth, mode, clean))
        return out

    # Version 2 shapes (C-85): runs of one to three names repeated up to 300
    # times (a global resource shows only under repetition), with or without
    # a character between them.
    RUN_LENGTHS = [(30, 2), (20, 3), (15, 5), (12, 10), (8, 20), (6, 50),
                   (4, 100), (3, 200), (2, 300)]

    def run(self, mode: str, clean: bool) -> list:
        m = "text" if mode == "text" else "math"
        names = [self.name(m, clean) for _ in range(self.r.randint(1, 3))]
        k = self.pick(self.RUN_LENGTHS)
        sep = self.r.random() < 0.4
        out = []
        for i in range(k):
            out.append(cmd(names[i % len(names)]))
            if sep:
                out.append(text(self.word(1, 1)))
        return out

    def math_node(self, depth: int, clean: bool):
        kind = self.pick([(4, "dollar"), (2, "display"), (2, "paren"), (2, "bracket")])
        mode = "dmath" if kind in ("display", "bracket") else "math"
        return S.math(kind, *self.seq(depth + 1, mode, clean, 0, 5))

    def display_follower(self, clean: bool):
        """A `$` in display math and what follows it (Semantics.v
        display_bad_follower, the look-ahead version 1 never drew): a name,
        an undefined word, a character, a group, or nothing."""
        ch = self.pick([(6, "cmd"), (2, "undef"), (2, "text"), (1, "group"),
                        (1, "empty")])
        if ch == "cmd":
            first = [cmd(self.name("math", True))]
        elif ch == "undef":
            first = [cmd(self.r.choice(self.nm.undefined))]
        elif ch == "text":
            first = [text(self.word(1, 1))]
        elif ch == "group":
            first = [group(text(self.word(1, 1)))]
        else:
            first = []
        return S.math("dollar", *first, *self.seq(3, "math", clean, 0, 2))

    def nest(self, clean: bool):
        """Deep brace nesting, up to the bound of Decide.v (C-86)."""
        k = self.pick([(6, 10), (4, 50), (3, 120), (2, MAX_BRACE_DEPTH - 1)])
        inner = self.seq(3, "text", clean, 1, 3)
        node = inner
        for _ in range(k):
            node = [group(*node)]
        return node[0]

    def node(self, depth: int, mode: str, clean: bool):
        deep = depth >= 3
        if mode == "dmath" and not deep and self.r.random() < (0.05 if clean else 0.15):
            return self.display_follower(clean)
        if mode == "dmath":
            mode = "math"
        if mode == "text" and depth == 0 and self.r.random() < 0.02:
            return self.nest(clean)
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
            # inside a math brace group TeX is in non-display math
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
        if m["verdict"] == "not_strict":
            return {"not_strict": True}  # outside the tier: nothing to grade
        try:
            r = S.grade(oracle, m["tex"], timeout=300)
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
    outside = []
    for i, (d, m, g) in enumerate(zip(docs, models, grades)):
        if "infra" in g:
            infra.append({"i": i, "error": g["infra"]})
            continue
        f = families[i] if families is not None else None
        if "not_strict" in g:
            # Outside the tier. Expected for the families built to be outside
            # (recorded with their branches); anywhere else it is a harness
            # defect (the generator drew a non-strict document).
            if f in EXPECT_NOT_STRICT:
                outside.append({"i": i, "family": f, "doc": d,
                                "branches": m.get("branches", [])})
                continue
            g = {"rc": None, "pdf": None, "timed_out": False, "error": "", "line": None}
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
            by_family[f]["n"] += 1
            by_family[f]["agree"] += ok
            by_family[f]["exercised"] += f in m.get("rules", [])
            rec["family"] = f
            rec["doc"] = d
            rec["rules"] = m.get("rules", [])
            rec["branches"] = m.get("branches", [])
        records.append(rec)
        if not ok:
            disagreements.append({"i": i, "why": why, "doc": d, "tex": m["tex"],
                                  "model": {k: m.get(k) for k in (
                                      "verdict", "reason", "loc", "loc_tok",
                                      "loc_mode", "loc_line", "rules")},
                                  "oracle": g})
    return by_class, by_rule, by_family, disagreements, records, infra, outside


# =================================================================== BYTES ==
# M2 phase 2: the decision on the BYTES of a file (proofs/Strict/DecideBytes.v,
# extracted as latex-parse/strict/strict_bytes_extracted.ml and run through
# strict_decide.exe --bytes). Two modes:
#   --bytes-rules   the probe families of every constructor of the reader and
#                   the front matter (Lexer.v, Front.v), the bounds family, the
#                   phase-1 rule probes' rendered bytes re-laid out four ways
#                   (as rendered, lines joined, joined through comments, mixed
#                   line ends and padding), and the near-misses outside the
#                   fragment -> corpora/strict_s0/bytes_probes.json
#   --bytes N       N generated files, half re-laid-out phase-1 trees and half
#                   generated directly as byte strings, plus the near-misses
#                   -> corpora/strict_s0/bytes_differential.json
# Every verdict is the extracted decide_bytes'; every grade is the one
# oracle's; the agreement rule is phase 1's (_strict_s0.agrees: verdict, the
# pdfTeX message class for the reason, and the LINE).

import _strict_bytes as SB  # noqa: E402

BYTES_GENERATOR_VERSION = "1"
BYTES_PROBES = OUT_DIR / "bytes_probes.json"
BYTES_DIFFERENTIAL = OUT_DIR / "bytes_differential.json"
LEX_RULES = [
    "FL_directive", "FL_none",
    "Lines_nil", "Lines_lf", "Lines_crlf", "Lines_cr", "Lines_last",
    "LL_end", "LL_eol_new", "LL_eol_mid", "LL_eol_skip", "LL_space_skip",
    "LL_space_emit", "LL_comment", "LL_char", "LL_bgroup", "LL_egroup",
    "LL_math", "LL_sub", "LL_sup", "LL_hathat", "LL_word", "LL_word_hathat",
    "LL_sym", "LL_sym_hathat", "LL_nullcs", "LL_bad",
    "LX_nil", "LX_line", "LX_long",
    "P_prologue",
    "B_eof", "B_end", "B_space", "B_space_script", "B_par_line", "B_par_word",
    "B_word", "B_sym", "B_char", "B_open", "B_close", "B_math", "B_script",
]
P1_MODES = ["render", "tight", "comment", "mixed"]
HEX_MAX = 4096  # files up to this size are recorded byte for byte


def byte_names(nm: "Names") -> dict:
    sig = nm.sigs
    tm = next(n for n in sorted(sig) if sig[n]["text"] == "material"
              and sig[n]["math"] == "noad")
    mo = next(n for n in sorted(sig) if isinstance(sig[n]["text"], list)
              and sig[n]["math"] == "noad")
    return {"undefined": nm.undefined, "text_material": tm, "math_only": mo,
            "text_ok": nm.text_ok, "math_ok": nm.math_ok, "all": nm.all}


def bytes_rule_docs(nm: "Names", sig_path: Path, rng: random.Random):
    """(family, bytes, expected outside?) for --bytes-rules."""
    out = [(f, b, f in SB.OUTSIDE_FAMILIES)
           for f, b in SB.lexer_families(byte_names(nm), rng)]
    # the phase-1 rule probes, as the extracted renderer printed them, then
    # re-laid out: a phase-1 document outside the tier stays outside.
    # The phase-1 BOUND documents are not re-laid out: one token per line
    # doubles their kernel stream at the byte level (every line end is a
    # space token), so they are outside the byte-level bound; the bounds are
    # probed at the byte level by the family L0-bounds.
    p1 = [(f, r) for f, r in rule_docs(nm) if f not in ("BOUND", "BOUND-OUT")]
    models = S.Kernel(signatures=sig_path).run([r for _, r in p1])
    for m in models:
        tex = m["tex"].encode("ascii")
        outside = m["verdict"] == "not_strict"
        for mode in P1_MODES:
            out.append((f"P1-{mode.upper()}", SB.relayout(tex, rng, mode), outside))
    out += [("L0-NEAR", b, True) for _, b in SB.near_miss_docs(rng)]
    return out


def bytes_random_docs(nm: "Names", n: int, rng: random.Random, sig_path: Path):
    """(family, bytes, expected outside?) for --bytes N: n files in the
    fragment, half re-laid-out phase-1 trees and half generated directly, plus
    the near-misses. A generated file the extracted decider places outside is
    not graded and is replaced (the direct generator may draw a script without
    its argument or a ^^ on purpose); their number is reported."""
    gen, direct = Gen(rng, nm), SB.Direct(rng, byte_names(nm))
    tree_kern = S.Kernel(signatures=None)  # the renderer only
    bk = S.BytesKernel(signatures=sig_path)
    out, discarded = [], {"TREE": 0, "DIRECT": 0}
    while len(out) < n:
        need = n - len(out)
        batch = []
        trees = [gen.document() for _ in range((need + 1) // 2)]
        for m in tree_kern.run([{"doc": d} for d in trees]):
            mode = rng.choice(["tight", "comment", "mixed", "mixed"])
            batch.append((f"TREE-{mode.upper()}",
                          SB.relayout(m["tex"].encode("ascii"), rng, mode), False))
        batch += [("DIRECT", direct.document(), False) for _ in range(need // 2)]
        for (fam, b, e), m in zip(batch, bk.run([b for _, b, _ in batch])):
            if m["verdict"] == "not_strict":
                discarded[fam.split("-")[0]] += 1
            elif len(out) < n:
                out.append((fam, b, e))
    out += [("L0-NEAR", b, True) for _, b in SB.near_miss_docs(rng)]
    return out, discarded


def run_bytes(docs, sig_path: Path, workers: int, label: str):
    kern = S.BytesKernel(signatures=sig_path)
    models = kern.run([b for _, b, _ in docs])
    oracle = _oracle.get_oracle()
    t0, done = time.time(), [0]

    def g(pair):
        (fam, b, _), m = pair
        if m["verdict"] == "not_strict":
            return {"not_strict": True}
        try:
            r = S.grade_bytes(oracle, b, timeout=300)
        except _oracle.OracleError as e:
            r = {"infra": str(e)[:300]}
        done[0] += 1
        if done[0] % 50 == 0:
            print(f"[{label}] graded {done[0]} ({time.time() - t0:.0f}s)", flush=True)
        return r

    with ThreadPoolExecutor(workers) as ex:
        grades = list(ex.map(g, zip(docs, models)))
    return oracle, models, grades


def tally_bytes(docs, models, grades, keep_docs: bool):
    by_class = defaultdict(lambda: {"n": 0, "agree": 0})
    by_rule = {r: {"docs": 0, "agree": 0} for r in RULES}
    by_family = defaultdict(lambda: {"n": 0, "agree": 0, "exercised": 0, "outside": 0})
    lex_rule_docs = {r: {"graded_agree": 0, "outside": 0} for r in LEX_RULES}
    records, outside, dis, infra, unexpected = [], [], [], [], []
    explain_mismatch = []
    for i, ((fam, b, exp_out), m, g) in enumerate(zip(docs, models, grades)):
        sha = hashlib.sha256(b).hexdigest()
        rec = {"i": i, "family": fam, "sha256": sha, "nbytes": len(b)}
        if keep_docs and len(b) <= HEX_MAX:
            rec["hex"] = b.hex()
        # explain is None exactly on the decided files (Explain.v)
        if (m["verdict"] == "not_strict") != (m.get("explain") is not None):
            explain_mismatch.append({"i": i, "family": fam, "verdict": m["verdict"],
                                     "explain": m.get("explain")})
        if "infra" in g:
            infra.append({"i": i, "error": g["infra"]})
            continue
        lr = m.get("lex_rules", [])
        if "not_strict" in g:
            if exp_out:
                outside.append(dict(rec, explain=m.get("explain"), lex_rules=lr,
                                    lex_branches=m.get("lex_branches", [])))
                by_family[fam]["outside"] += 1
                by_family[fam]["exercised"] += fam in lr
                for r in lr:
                    if r in lex_rule_docs:
                        lex_rule_docs[r]["outside"] += 1
                continue
            unexpected.append(dict(rec, explain=m.get("explain")))
            g = {"rc": None, "pdf": None, "timed_out": False, "error": "", "line": None}
        elif exp_out:
            # built to be outside, decided: a defect of the reader or the family
            unexpected.append(dict(rec, verdict=m["verdict"]))
        ok, why = S.agrees(m, g)
        cls = S.verdict_class(m)
        by_class[cls]["n"] += 1
        by_class[cls]["agree"] += ok
        for r in m.get("rules", []):
            by_rule.setdefault(r, {"docs": 0, "agree": 0})
            by_rule[r]["docs"] += 1
            by_rule[r]["agree"] += ok
        if ok:
            for r in lr:
                if r in lex_rule_docs:
                    lex_rule_docs[r]["graded_agree"] += 1
        by_family[fam]["n"] += 1
        by_family[fam]["agree"] += ok
        by_family[fam]["exercised"] += fam in lr
        rec.update({"class": cls, "agree": ok,
                    "oracle": [g["rc"], g["pdf"], g["error"], g["line"]]})
        if m["verdict"] == "not_ready":
            rec["model"] = [m["reason"], m["loc_tok"], m["loc_mode"], m["loc_line"]]
        if keep_docs:
            rec.update({"lex_rules": lr, "lex_branches": m.get("lex_branches", []),
                        "rules": m.get("rules", []), "branches": m.get("branches", [])})
        records.append(rec)
        if not ok:
            dis.append({"i": i, "family": fam, "why": why,
                        "hex": b.hex() if len(b) <= HEX_MAX else None, "sha256": sha,
                        "model": {k: m.get(k) for k in ("verdict", "reason", "loc",
                                                        "loc_tok", "loc_mode", "loc_line",
                                                        "rules")},
                        "oracle": g})
    return (by_class, by_rule, by_family, lex_rule_docs, records, outside, dis, infra,
            unexpected, explain_mismatch)


def dump_records(out: dict) -> str:
    """The evidence file: one top-level key per line, and every element of a
    list of records on its own compact line (a byte-level file has thousands
    of records; indented JSON would multiply its size)."""
    keys = list(out)
    lines = ["{"]
    for i, k in enumerate(keys):
        v = out[k]
        end = "," if i < len(keys) - 1 else ""
        if isinstance(v, list) and v and isinstance(v[0], dict):
            lines.append(f" {json.dumps(k)}: [")
            lines += ["  " + json.dumps(r, separators=(",", ":")) + ("," if j < len(v) - 1 else "")
                      for j, r in enumerate(v)]
            lines.append(" ]" + end)
        else:
            lines.append(f" {json.dumps(k)}: {json.dumps(v)}{end}")
    return "\n".join(lines) + "\n}\n"


def main_bytes(args, nm: "Names", sig_path: Path) -> int:
    rng = random.Random(args.seed)
    discarded = None
    if args.bytes_rules:
        docs = bytes_rule_docs(nm, sig_path, rng)
        label, default_out, keep = "bytes-rules", BYTES_PROBES, True
    else:
        docs, discarded = bytes_random_docs(nm, args.bytes, rng, sig_path)
        label, default_out, keep = "bytes", BYTES_DIFFERENTIAL, False
    oracle, models, grades = run_bytes(docs, sig_path, args.workers, label)
    (by_class, by_rule, by_family, lex_rule_docs, records, outside, dis, infra,
     unexpected, explain_mismatch) = tally_bytes(docs, models, grades, keep)
    graded = sum(v["n"] for v in by_class.values())
    ready_n = by_class.get("READY", {}).get("n", 0)
    # the phase-1 rendered bytes: the tree decider and the bytes decider are
    # two proved-exact deciders of the same file; they must agree on verdict,
    # reason and line (the tree side's line is phase 1's harness computation).
    consistency = {"checked": 0, "agree": 0, "differ": []}
    if args.bytes_rules:
        p1 = [(f, r) for f, r in rule_docs(nm) if f not in ("BOUND", "BOUND-OUT")]
        tmodels = S.Kernel(signatures=sig_path).run([r for _, r in p1])
        renders = [(i, m) for i, (f, b, _) in enumerate(docs) if f == "P1-RENDER"
                   for m in [models[i]]]
        for (i, bm), tm in zip(renders, tmodels):
            consistency["checked"] += 1
            same = (bm["verdict"] == tm["verdict"] and bm.get("reason") == tm.get("reason")
                    and bm.get("loc_line") == tm.get("loc_line"))
            consistency["agree"] += same
            if not same:
                consistency["differ"].append({"i": i, "bytes": [bm["verdict"], bm.get("reason"), bm.get("loc_line")],
                                              "tree": [tm["verdict"], tm.get("reason"), tm.get("loc_line")]})
    summary = {
        "documents": len(docs),
        "graded": graded,
        "agree": sum(v["agree"] for v in by_class.values()),
        "disagree": len(dis),
        "not_strict_generated": len(unexpected),
        "outside_by_design": len(outside),
        "explain_mismatches": len(explain_mismatch),
        "oracle_infrastructure_failures": len(infra),
        "oracle_timeouts": sum(1 for g in grades if g.get("timed_out")),
        "by_class": {k: by_class[k] for k in sorted(by_class)},
        "rules_never_exercised": [r for r in RULES if by_rule.get(r, {}).get("docs", 0) == 0],
        "tree_bytes_consistency": {k: v for k, v in consistency.items() if k != "differ"},
    }
    if discarded is not None:
        summary["generated_outside_replaced"] = discarded
    if not dis and graded:
        summary["upper_bound_95"] = {
            "all": round(1 - 0.05 ** (1 / graded), 6),
            "ready": round(1 - 0.05 ** (1 / ready_n), 6) if ready_n else None,
            "scope": "the disagreement rate over files drawn by THIS generator "
                     "(version, weights, seed), not over L_S0: a class of files "
                     "the generator does not draw is not bounded (C-85)",
        }
    out = {
        "schema": "lp-strict-bytes/1",
        "generator": "scripts/tools/strict_differential.py",
        "generator_version": BYTES_GENERATOR_VERSION,
        "mode": label,
        "seed": args.seed,
        "source": S.source_block(),
        "signatures_sha256": S.sha256_file(sig_path),
        "lexical_sha256": S.sha256_file(S.LEXICAL),
        "bytes_extract_sha256": S.sha256_file(S.BYTES_EXTRACT),
        "kernel_extract_sha256": S.sha256_file(S.EXTRACT),
        "oracle": oracle.provenance(),
        "agreement_rule": "_strict_s0.agrees on the extracted decide_bytes' verdict: "
                          "READY iff rc 0 and a PDF; E0 iff rc 0 and no PDF; any other "
                          "reason iff rc != 0, the first ! message is in "
                          "_strict_s0.expected_messages(reason, token, mode), and the "
                          "reported line (DecideBytes.ReportedLine) equals the oracle's "
                          "l.N (both absent when the file ends)",
        "summary": summary,
        "by_rule": by_rule,
        "by_family": {f: by_family[f] for f in sorted(by_family)},
        "lex_rules": lex_rule_docs,
        "disagreements": dis,
        "unexpected_outside_or_inside": unexpected,
        "explain_mismatches": explain_mismatch,
        "tree_bytes_differences": consistency["differ"],
        "infrastructure_failures": infra,
        "outside": outside,
        "documents": records,
    }
    path = Path(args.out) if args.out else default_out
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(dump_records(out))
    print(json.dumps(summary, indent=1))
    for d in dis[:20]:
        print("DISAGREE", d["i"], d["family"], d["why"])
    for u in unexpected[:10]:
        print("UNEXPECTED", u)
    bad = dis or infra or unexpected or explain_mismatch or consistency["differ"]
    return 1 if bad else 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--rules", action="store_true")
    ap.add_argument("--random", type=int, default=0)
    ap.add_argument("--seed", type=int, default=2)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--signatures", default=str(S.SIGNATURES))
    ap.add_argument("--out")
    ap.add_argument("--bytes-rules", action="store_true",
                    help="M2 phase 2: the reader's probe families (bytes)")
    ap.add_argument("--bytes", type=int, default=0,
                    help="M2 phase 2: N generated files (bytes)")
    args = ap.parse_args()
    sig_path = Path(args.signatures)
    nm = Names(sig_path, random.Random(args.seed))
    if args.bytes_rules or args.bytes:
        return main_bytes(args, nm, sig_path)

    if args.rules:
        fam = rule_docs(nm)
        docs = [d for _, d in fam]  # requests
        families = [f for f, _ in fam]
        label, default_out = "rules", OUT_DIR / "rule_probes.json"
    elif args.random:
        gen = Gen(random.Random(args.seed), nm)
        docs = [{"doc": gen.document()} for _ in range(args.random)]
        families = None
        label, default_out = "random", DIFFERENTIAL
    else:
        ap.error("give --rules, --random N, --bytes-rules or --bytes N")
    kern, oracle, models, grades = run_all(docs, sig_path, args.workers, label)
    not_strict = [i for i, m in enumerate(models) if m["verdict"] == "not_strict"]
    by_class, by_rule, by_family, dis, records, infra, outside = tally(
        docs, models, grades, families)
    graded = sum(v["n"] for v in by_class.values())
    ready_n = by_class.get("READY", {}).get("n", 0)
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
        "outside_tier_by_design": len(outside),
    }
    if not dis and graded:
        # Exact one-sided 95% (Clopper-Pearson) upper bound for 0 failures in n.
        summary["upper_bound_95"] = {
            "all": round(1 - 0.05 ** (1 / graded), 6),
            "ready": round(1 - 0.05 ** (1 / ready_n), 6) if ready_n else None,
            "scope": "the disagreement rate over documents drawn by THIS generator "
                     "(version, weights, seed), not over L_S0: a class of documents "
                     "the generator does not draw is not bounded (C-85)",
        }
    out = {
        "schema": "lp-strict-differential/2",
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
        out["by_family"] = {f: by_family[f] for f in RULES + ["BOUND", "MATRIX"]
                            if f in by_family}
        out["probes"] = records
        out["outside_tier"] = outside
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
