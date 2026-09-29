#!/usr/bin/env python3
"""Generate the probe-attested signatures of the article contract for the
strict kernel L_S0 (ADR-012, milestone M2 phase 1).

WHAT A SIGNATURE IS. The kernel (proofs/Strict/Contract.v) needs, for each
defined control word a strict document may use, how it behaves when executed
in text and in math:

    text: material | noop | fatal E3
    math: noad | noop | fatal E3 | fatal E6

A defined name without a signature is OUTSIDE the tier (design §A.1.3); a
signature is never read from a definition (design §B.2: static arity
disagreed with behaviour on 30% of macros), only attested by probes.

WHAT A SIGNATURE CLAIMS (generator version 3, correction C-85). The kernel
uses a signature in EVERY context of the fragment, so a signature is a claim
about the name next to every token class, repeated any number of times, and
interleaved with every other admitted name. Version 2 attested the name in 15
contexts, one occurrence each, and two classes of name slipped through:

  * names that expansion sees through: the kernel's rule for `$` in display
    math reads the next token WITH expansion (tex.web §1197), and a macro that
    expands to nothing (`\\empty`, `\\iftrue`, `\\theenumiii`) is not the
    bad follower the rule assumes (false NOT-READY, 6 of 150 names);
  * names that consume a global resource: `\\tableofcontents` passes every
    single-occurrence probe and the 17th occurrence stops pdflatex with "No
    room for a new \\write" (false READY).

HOW IT IS ATTESTED (the rule this tool implements). Five stages; a name
leaves at the first stage it fails, with the evidence.

  0. INERTNESS RULE (no TeX run decides it, the oracle only reports the
     meaning). The name's `\\meaning` at body start is read from the pinned
     image (one oracle job for all candidates) and
     `check_strict_kernel.inertness_violation` is applied: conditionals,
     expansion control, prefixes (`\\immediate`), interaction-mode changers,
     I/O, tracing, code-table (catcode) changers, deferred execution,
     definitions, registers, names `\\let` to a structural character, and
     macros whose own expansion text holds one of the state-changing
     primitives, an unbalanced conditional, or nothing at all are rejected.
     The gate re-applies the same function to the recorded meaning of every
     admitted name.
  1. BASE probes (the 15 of version 2): X in text and in math next to the
     constructs the kernel models.
  2. For names some hypothesis still fits: the FOLLOWER family (X
     immediately followed by each token class of the fragment, in text and
     in math: every character of the fragment, space, blank line, \\par, {,
     }, $, $$, \\( \\) \\[ \\], ^, _, an undefined word, \\end{document}, end of
     file), the DISPLAY-FOLLOWER family (X right after a `$` in display math,
     the look-ahead of Semantics.v's `display_bad_follower`), and the
     REPETITION family (X 300 times in text, in math, alternating with a
     character, in 300 paragraphs, groups, formulas and displays; X at the
     kernel's nesting bound in text and math, alone and at every level; X
     repeated to the kernel's token bound in one paragraph and in one
     formula, Decide.v `max_tokens`, C-86).
  3. ADMISSION: exactly one of the 12 HYPOTHESES (text x math behaviour)
     makes the EXTRACTED kernel (`strict_decide.exe`, the Coq decider)
     agree with the oracle on every probe of stages 1-2, under the
     differential's own agreement rule (`_strict_s0.agrees`: verdict,
     reason class and line).
  4. INTERLEAVING: every admitted name is then run in seeded documents that
     interleave ALL admitted names (text-usable names in text, math-usable
     names in math and in display math, each document at least 300
     occurrences), graded against the kernel with the final signature set.
     A disagreeing document is reduced by delta debugging to a minimal set of
     names that still disagrees; every name of that set is rejected, and the
     stage repeats until every interleaving document agrees.

So a signature is, by construction, a claim the kernel has been seen to make
correctly about X in every probed context; nothing about X is hand-written.

CANDIDATES. Control words (ASCII letters only: the fragment's names) defined
in the article configuration's closed world at body start (the kernel file
updated by corpora/contracts/article.json), minus the three names the grammar
itself gives structure to (`par`, `begin`, `end`). A deterministic sample: the
first N by sha256 of the name (`--n`, default 400). Selection by rule.

GRADE REUSE. `--reuse FILE` takes the grades of byte-identical documents from
a previous signature file graded by the SAME oracle (every provenance field
equal, else the tool refuses): the version-2 file's 6,000 base-probe grades
are the version-3 stage-1 grades, since the base probes and the renderer did
not change. The output records how many grades were reused and from which
file (sha256).

OUTPUT. corpora/contracts/strict/article-s0-signatures.json (schema
lp-strict-signatures/2). Needs the oracle (docker and the pinned image):
    python3 scripts/tools/gen_strict_signatures.py [--n 400] [--workers 4]
        [--reuse corpora/contracts/strict/article-s0-signatures.json]
"""
from __future__ import annotations

import argparse
import hashlib
import json
import random
import re
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import _oracle  # noqa: E402
import _strict_s0 as S  # noqa: E402
import check_strict_kernel as CK  # noqa: E402

# Version 4 (C-92): stage 0's meaning closure follows robust commands
# (`\protect \X  ` to the inner name "X "); nothing else changed, and every
# probe grade of version 3 is reused (--reuse).
# Version 5 (C-94, C-96): the nesting families sit at the TeX-GROUP bound (a
# formula is a group: R-NEST-MATH is $ and 199 braces, no longer 200); stage
# 0 reads expansion texts by TeX's printing rules, every reading, and follows
# expl3 names and active characters (check_strict_kernel.body_readings); a
# reuse source is a committed file (REV:path), recorded with its commit.
GENERATOR_VERSION = "5"
STRUCTURAL = CK.STRUCTURAL
# Two control words outside the closed world (checked in main()).
UNDEF_A, UNDEF_B = "lpqundefa", "lpqundefb"

TEXT_H = ("material", "noop", ["fatal", "E3"])
MATH_H = ("noad", "noop", ["fatal", "E3"], ["fatal", "E6"])
HYPOTHESES = [{"text": t, "math": m} for t in TEXT_H for m in MATH_H]

# The kernel's bounds (proofs/Strict/Decide.v, C-86); check_strict_kernel.py
# checks these equal the Coq definitions.
MAX_GROUPS = CK.MAX_GROUPS
MAX_TOKENS = CK.MAX_TOKENS
REPEAT = 300
# Every character of the fragment (Decide.v safe_char), in a fixed order.
SAFE_CHARS = ("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
              "0123456789.,;:!?()/+-=")


def _dollar(*b): return S.math("dollar", *b)
def _display(*b): return S.math("display", *b)
def _paren(*b): return S.math("paren", *b)
def _bracket(*b): return S.math("bracket", *b)
def _sup(a): return S.script(True, a)
def _sub(a): return S.script(False, a)


def _T(*ts, close=False) -> dict:
    """A token-level request (strict_decide.ml `tok_of`)."""
    r = {"toks": [list(t) if isinstance(t, tuple) else [t] for t in ts]}
    if close:
        r["close"] = True
    return r


def base_probes(x: str) -> dict[str, dict]:
    """Stage 1: the 15 probes of generator version 2, unchanged (so their
    grades can be reused byte for byte)."""
    c = S.cmd(x)
    t = S.text
    return {
        "T-ALONE": S.doc(c),
        "T-MID": S.doc(t("a"), c, t("b")),
        "T-GROUP": S.doc(S.group(c), t("x")),
        "T-PAR": S.doc(c, S.par(), t("x")),
        "T-DOLLAR": S.doc(c, _dollar(t("x"))),
        "T-SUP": S.doc(t("a"), c, _sup(t("b"))),
        "T-SPACE": S.doc(c, S.space(), c, S.par(True)),
        "M-ALONE": S.doc(_dollar(c)),
        "M-MID": S.doc(_dollar(t("a"), c, t("b"))),
        "M-GROUP": S.doc(_dollar(S.group(c))),
        "M-RESET": S.doc(_dollar(t("x"), _sup(t("a")), c, _sup(t("b")))),
        "M-SUB": S.doc(_dollar(c, _sub(t("a"))), t("y")),
        "M-DISPLAY": S.doc(_display(c, t("z"))),
        "T-UNDEF": S.doc(c, S.cmd(UNDEF_A), S.cmd(UNDEF_B)),
        "M-PAR": S.doc(_dollar(c, S.par(), t("x"))),
    }


def _nest(depth: int, inner: list) -> list:
    node = inner
    for _ in range(depth):
        node = [S.group(*node)]
    return node


def _nest_each(depth: int, c) -> list:
    node = [c, S.text("x")]
    for _ in range(depth):
        node = [c, S.group(*node)]
    return node


def stage2_probes(x: str) -> dict[str, dict]:
    """Stage 2: follower, display-follower and repetition families."""
    c = S.cmd(x)
    t = S.text
    a = t("a")
    chars_t = [n for ch in SAFE_CHARS for n in (c, t(ch))]
    p: dict[str, dict] = {
        # --- FOLLOWER, text: X immediately followed by each token class.
        # (X then a blank line, $, ^, an undefined word, \end{document}, a
        # space: base probes T-PAR, T-DOLLAR, T-SUP, T-UNDEF, T-ALONE,
        # T-SPACE.)
        "FT-CHARS": S.doc(*chars_t),
        "FT-OPEN": S.doc(c, S.group(t("x"))),
        "FT-CLOSE": S.doc(a, c, S.stray()),
        "FT-PAR": S.doc(c, S.par(True), t("x")),
        "FT-DISPLAY": S.doc(c, _display(t("x"))),
        "FT-MOPEN": S.doc(c, _paren(t("x"))),
        "FT-BOPEN": S.doc(c, _bracket(t("x"))),
        "FT-MCLOSE": _T(("char", "a"), ("cs", x), "close_paren", "end"),
        "FT-BCLOSE": _T(("char", "a"), ("cs", x), "close_bracket", "end"),
        "FT-SUB": S.doc(a, c, _sub(t("b"))),
        "FT-EOF": S.doc(a, c, has_end=False),
        # --- FOLLOWER, math. (X then $, ^, _, a blank line, }: base probes
        # M-ALONE, M-RESET, M-SUB, M-PAR, M-GROUP.)
        "FM-CHARS": S.doc(_dollar(*chars_t)),
        "FM-OPEN": S.doc(_dollar(c, S.group(t("x")))),
        "FM-CLOSE": S.doc(_dollar(a, c, S.stray())),
        "FM-PAR": S.doc(_dollar(c, S.par(True), t("x"))),
        "FM-SPACE": S.doc(_dollar(c, S.space(), c)),
        "FM-MOPEN": S.doc(_dollar(c, _paren())),
        "FM-BOPEN": S.doc(_dollar(c, _bracket())),
        "FM-MCLOSE": S.doc(_paren(a, c)),
        "FM-BCLOSE": S.doc(_bracket(a, c)),
        "FM-UNDEF": S.doc(_dollar(c, S.cmd(UNDEF_A), S.cmd(UNDEF_B))),
        "FM-DDOLLAR": S.doc(_display(t("z"), c)),
        "FM-GDOLLAR": S.doc(_dollar(S.group(c, _dollar()))),
        "FM-END": _T("dollar", ("char", "a"), ("cs", x), "end"),
        "FM-EOF": _T("dollar", ("char", "a"), ("cs", x)),
        # --- DISPLAY-FOLLOWER: X right after a $ in display math, the
        # position Semantics.v's display_bad_follower reads WITH expansion.
        "D-FOLLOW-DOLLAR": S.doc(_display(t("z"), _dollar(c)), _dollar()),
        "D-FOLLOW-CHAR": S.doc(_display(t("z"), _dollar(c, t("x")))),
        "D-FOLLOW-BRACKET": S.doc(_bracket(t("z"), _dollar(c))),
        "D-FOLLOW-GROUP": S.doc(_display(t("z"), _dollar(c, S.group(t("x"))))),
        # --- REPETITION (global resources: \write streams, list depth, the
        # condition stack, memory; C-85/C-86).
        "R-TEXT": S.doc(*([c] * REPEAT), t("x")),
        "R-TEXT-ALT": S.doc(*[n for _ in range(REPEAT) for n in (c, t("x"))]),
        "R-PARS": S.doc(*[n for _ in range(REPEAT) for n in (c, t("x"), S.par())]),
        "R-GROUPS": S.doc(*[S.group(c, t("x")) for _ in range(REPEAT)]),
        "R-MATH": S.doc(_dollar(*([c] * REPEAT))),
        "R-MATH-ALT": S.doc(_dollar(*[n for _ in range(REPEAT) for n in (c, t("x"))])),
        "R-FORMULAS": S.doc(*[_dollar(c, t("x")) for _ in range(REPEAT)]),
        "R-DISPLAYS": S.doc(*[_display(c, t("x")) for _ in range(REPEAT)]),
        # at the TeX-group bound (Decide.v max_groups, C-94): the formula is
        # one of the groups
        "R-NEST-TEXT": S.doc(*_nest(MAX_GROUPS, [c, t("x")])),
        "R-NEST-MATH": S.doc(_dollar(*_nest(MAX_GROUPS - 1, [c, t("x")]))),
        "R-NEST-EACH-TEXT": S.doc(*_nest_each(MAX_GROUPS, c)),
        "R-NEST-EACH-MATH": S.doc(_dollar(*_nest_each(MAX_GROUPS - 1, c))),
        # at the token bound (Decide.v max_tokens): the whole document one
        # paragraph / one formula of X
        "R-BIG-TEXT": S.doc(*([c] * (MAX_TOKENS - 2)), t("x")),
        "R-BIG-MATH": S.doc(_paren(*([c] * (MAX_TOKENS - 3)))),
    }
    return p


def candidates(n: int) -> list[str]:
    names = [m for m in S.members()
             if re.fullmatch(r"[A-Za-z]+", m) and m not in STRUCTURAL]
    names.sort(key=lambda m: hashlib.sha256(m.encode()).hexdigest())
    return names[:n]


# ------------------------------------------------------------- meanings ---

def dump_meanings(oracle, names: list[str]) -> dict[str, str]:
    r"""`\meaning` of every name at body start, from the pinned image. One
    job; the document is a generator tool, not a graded probe. Every name is
    given by the hex of its bytes (`\pdfunescapehex`), so a name of any
    characters -- expl3's `_` and `:`, spaces, backslashes, non-ASCII -- is
    read exactly (C-96: the name set used to be restricted to letters and @,
    so the closure could not follow expl3 code). `\ifcsname` reads a name
    without defining it (an undefined name is reported as `undefined`, and
    \csname would have made it \relax). A key "active:<code>" is the meaning
    of that ACTIVE character (written in ^^ notation, which makes it one).
    Meanings are written with \immediate\write, \newlinechar -1, to a file
    (no line wrapping) and read back byte for byte (UTF-8, surrogateescape);
    an unreadable or incomplete dump is an oracle failure."""
    lines = [r"\documentclass{article}", r"\newwrite\lpqmw",
             r"\immediate\openout\lpqmw=lpqmeanings.txt\relax",
             r"\begin{document}", r"\newlinechar=-1\relax"]
    for i, n in enumerate(names):
        if n.startswith(CK.ACTIVE_PREFIX):
            code = int(n[len(CK.ACTIVE_PREFIX):])
            if not 0 < code < 256:
                raise ValueError(f"meaning dump: bad active character {n!r}")
            lines.append(r"\immediate\write\lpqmw{LPQ:%d:\meaning ^^%02x}" % (i, code))
            continue
        if not n:
            raise ValueError("meaning dump: the empty name")
        h = n.encode("utf-8", "surrogateescape").hex()
        lines.append(r"\immediate\write\lpqmw{LPQ:%d:\ifcsname\pdfunescapehex{%s}"
                     r"\endcsname\expandafter\meaning\csname\pdfunescapehex{%s}"
                     r"\endcsname\else undefined\fi}" % (i, h, h))
    lines += [r"\immediate\write\lpqmw{LPQEND}", r"\immediate\closeout\lpqmw",
              r"\end{document}"]
    with oracle.tempdir("lp-strict-meanings-") as td:
        td = Path(td)
        (td / "m.tex").write_text("\n".join(lines) + "\n", encoding="ascii")
        rc, out, to = oracle.run_engine(
            td, _oracle.ENGINE_PDFLATEX, ["-interaction=nonstopmode", "-halt-on-error", "m.tex"],
            _oracle.oracle_tex_vars(td), 300)
        f = td / "lpqmeanings.txt"
        text = (f.read_bytes().decode("utf-8", "surrogateescape") if f.is_file() else "")
    if rc != 0 or to or not text.rstrip().endswith("LPQEND"):
        raise _oracle.OracleError(f"meaning dump failed: rc={rc} timed_out={to}")
    got = {}
    for line in text.split("\n"):
        m = re.match(r"^LPQ:(\d+):(.*)$", line, re.S)
        if m:
            got[names[int(m.group(1))]] = m.group(2)
    missing = [n for n in names if n not in got]
    if missing:
        raise _oracle.OracleError(f"meaning dump misses {missing[:5]}")
    return got


def meaning_closure(oracle, names: list[str], world: set[str] | None = None,
                    active=None) -> dict[str, str]:
    """The meanings of `names` and of every name and active character that
    their expansion texts may hold, by every reading
    (check_strict_kernel.body_readings, C-96), transitively: dumped round by
    round until no new name appears."""
    world = CK.closed_world(S.REPO) if world is None else world
    active = CK.active_chars(S.REPO) if active is None else active
    meanings = {}
    todo = sorted(set(names))
    while todo:
        for i in range(0, len(todo), 4000):
            meanings.update(dump_meanings(oracle, todo[i:i + 4000]))
        new = set()
        for v in list(meanings.values()):
            t = CK.expansion_text(v)
            if t is not None:
                new |= CK.body_readings(t, world, active)[0]
        todo = sorted(new - set(meanings))
    return meanings


# ---------------------------------------------------------------- grading ---

class Grader:
    """Grades rendered documents once each (keyed by the sha256 of the
    bytes), with grades optionally seeded from a previous signature file of
    the same oracle."""

    def __init__(self, oracle, workers: int):
        self.oracle, self.workers = oracle, workers
        self.cache: dict[str, dict] = {}
        self.reused = 0
        self.graded = 0

    @staticmethod
    def key(tex: str) -> str:
        return hashlib.sha256(tex.encode()).hexdigest()

    def grade_all(self, texs: list[str], label: str) -> list[dict]:
        todo = sorted({self.key(t): t for t in texs if self.key(t) not in self.cache}.items())
        t0, done = time.time(), [0]

        def g(kt):
            k, tex = kt
            r = S.grade(self.oracle, tex, timeout=300)
            done[0] += 1
            if done[0] % 200 == 0:
                print(f"[signatures:{label}] graded {done[0]}/{len(todo)} "
                      f"({time.time() - t0:.0f}s)", flush=True)
            return k, r

        with ThreadPoolExecutor(self.workers) as ex:
            for k, r in ex.map(g, todo):
                self.cache[k] = r
        self.graded += len(todo)
        return [self.cache[self.key(t)] for t in texs]


def seed_from(grader: Grader, kern, spec: str, oracle) -> dict:
    """Seed the grades of a previous signature file COMMITTED to the
    repository (S.committed_source: REV:path or a tracked, unmodified path;
    LOW-2 of the C-94 review)."""
    text, src = S.committed_source(spec)
    old = json.loads(text)
    prov, cur = old.get("oracle", {}), oracle.provenance()
    diff = sorted(k for k in set(prov) | set(cur) if prov.get(k) != cur.get(k))
    if diff:
        raise SystemExit(f"--reuse {spec}: graded by another oracle ({diff} differ)")
    fams = old["probes"]
    reqs, keys = [], []
    for x, ev in old["evidence"].items():
        for f, g in ev.items():
            if f not in fams:
                continue
            d = json.loads(json.dumps(fams[f]).replace('"X"', json.dumps(x)))
            reqs.append(d if "toks" in d else {"doc": d})
            keys.append(g)
    outs = kern.run(reqs)
    for o, g in zip(outs, keys):
        rc, pdf, err, line = g
        grader.cache[Grader.key(o["tex"])] = {
            "rc": rc, "pdf": pdf, "passes": None, "timed_out": rc == -1,
            "error": err, "line": line}
    grader.reused = len(outs)
    return {**src, "generator_version": old.get("generator_version"),
            "grades_reused": len(outs)}


def fit(kern, x: str, reqs: dict[str, dict], grades: dict[str, dict],
        hyps: list[dict]) -> tuple[list[dict], dict]:
    """The hypotheses (of `hyps`) under which the extracted kernel agrees with
    every grade; and, per rejected hypothesis, the first probe it misses."""
    fams = list(reqs)
    preq = [dict(r if "toks" in r else {"doc": r}, signatures={x: h})
            for h in hyps for r in (reqs[f] for f in fams)]
    preds = kern.run(preq)
    fits, miss = [], {}
    k = 0
    for h in hyps:
        ok = True
        for f in fams:
            a, why = S.agrees(preds[k], grades[f])
            k += 1
            if not a and ok:
                ok = False
                miss[json.dumps(h)] = f"{f}: {why}"
        if ok:
            fits.append(h)
    return fits, miss


def render_all(kern, reqs: list[dict]) -> list[str]:
    return [o["tex"] for o in kern.run([r if "toks" in r else {"doc": r} for r in reqs])]


# ----------------------------------------------------------- interleaving ---

def interleave_docs(names_t: list[str], names_m: list[str], seed: int) -> list[tuple[str, dict]]:
    """Seeded documents interleaving the given names: in text (with and
    without characters between, and across paragraphs), in inline math, in
    display math; each at least REPEAT occurrences."""
    rng = random.Random(seed)
    out = []

    def cycle(pool, k):
        if not pool:
            return []
        seq = []
        while len(seq) < k:
            p = list(pool)
            rng.shuffle(p)
            seq += p
        return seq[:max(k, len(pool))]

    t, c = S.text, S.cmd
    if names_t:
        seq = cycle(names_t, REPEAT)
        out.append(("I-TEXT", S.doc(*[c(n) for n in seq], t("x"))))
        seq = cycle(names_t, REPEAT)
        out.append(("I-TEXT-ALT", S.doc(*[m for n in seq for m in (c(n), t("x"))])))
        seq = cycle(names_t, REPEAT)
        body = []
        for i, n in enumerate(seq):
            body += [c(n), t("x")] + ([S.par()] if i % 7 == 6 else [])
        out.append(("I-TEXT-PARS", S.doc(*body)))
        seq = cycle(names_t, REPEAT)
        out.append(("I-TEXT-GROUPS", S.doc(*[S.group(c(a), c(b), t("x"))
                                             for a, b in zip(seq[::2], seq[1::2])])))
    if names_m:
        seq = cycle(names_m, REPEAT)
        out.append(("I-MATH", S.doc(_dollar(*[c(n) for n in seq]))))
        seq = cycle(names_m, REPEAT)
        out.append(("I-MATH-ALT", S.doc(_dollar(*[m for n in seq for m in (c(n), t("x"))]))))
        seq = cycle(names_m, REPEAT)
        out.append(("I-DISPLAY", S.doc(_display(*[c(n) for n in seq]))))
        seq = cycle(names_m, REPEAT)
        out.append(("I-FORMULAS", S.doc(*[_dollar(c(a), c(b)) for a, b in zip(seq[::2], seq[1::2])])))
    return out


def ddmin(items: list, test) -> list:
    """Zeller's delta debugging: a 1-minimal sublist on which `test` holds
    (the caller knows it holds on `items`)."""
    n = 2
    while len(items) >= 2:
        chunk = -(-len(items) // n)
        subsets = [items[i:i + chunk] for i in range(0, len(items), chunk)]
        for sub in subsets:
            if test(sub):
                items, n = sub, 2
                break
        else:
            for sub in subsets:
                comp = [q for q in items if q not in sub]
                if comp and test(comp):
                    items, n = comp, max(n - 1, 2)
                    break
            else:
                if n >= len(items):
                    break
                n = min(len(items), 2 * n)
    return items


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=400)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--out", default=str(S.SIGNATURES))
    ap.add_argument("--reuse", help="a previous signature file of the same oracle, "
                    "COMMITTED (REV:path, or a tracked unmodified path)")
    ap.add_argument("--interleave-seeds", type=int, default=3)
    args = ap.parse_args()

    oracle = _oracle.get_oracle()
    # phase-1 names only: the one-argument commands (slice A) are attested by
    # gen_strict_arg_signatures.py, against this file's final set
    kern = S.Kernel(signatures=None, arg_signatures=None)
    names = candidates(args.n)
    if {UNDEF_A, UNDEF_B} & S.members():
        raise SystemExit("the look-ahead probes' undefined names are defined")
    grader = Grader(oracle, args.workers)
    reuse = seed_from(grader, kern, args.reuse, oracle) if args.reuse else None
    if reuse:
        print(f"[signatures] reused {reuse['grades_reused']} grades from {reuse['file']}",
              flush=True)

    # 0. inertness rule over the meanings at body start
    world, active = CK.closed_world(S.REPO), CK.active_chars(S.REPO)
    meanings = meaning_closure(oracle, names, world, active)
    prims = S.primitives()
    rejected: dict[str, str] = {}
    for x in names:
        v = CK.inertness_violation(x, meanings, prims, world, active)
        if v:
            rejected[x] = f"stage 0 (inertness rule): {v}"
    print(f"[signatures] stage 0: {len(rejected)} of {len(names)} not inert", flush=True)

    # 1. base probes, all candidates (the rule-rejected too: their evidence is
    # recorded, and it costs nothing when reused)
    fam1 = list(base_probes("X"))
    r1 = [base_probes(x)[f] for x in names for f in fam1]
    g1 = grader.grade_all(render_all(kern, r1), "base")
    evidence: dict[str, dict] = {}
    grades_of: dict[str, dict[str, dict]] = {}
    for i, x in enumerate(names):
        gx = dict(zip(fam1, g1[i * len(fam1):(i + 1) * len(fam1)]))
        grades_of[x] = gx
    fits1 = {}
    for x in names:
        f, miss = fit(kern, x, base_probes(x), grades_of[x], HYPOTHESES)
        fits1[x] = (f, miss)
    alive = [x for x in names if x not in rejected and fits1[x][0]]
    for x in names:
        if x not in rejected and not fits1[x][0]:
            ex_ = sorted(fits1[x][1].items())[0]
            rejected[x] = f"stage 1 (base probes): no hypothesis fits; e.g. {ex_[0]} fails {ex_[1]}"
    print(f"[signatures] stage 1: {len(alive)} names still fit", flush=True)

    # 2. follower, display-follower and repetition families
    fam2 = list(stage2_probes("X"))
    r2 = [stage2_probes(x)[f] for x in alive for f in fam2]
    g2 = grader.grade_all(render_all(kern, r2), "stage2")
    signatures: dict[str, dict] = {}
    for i, x in enumerate(alive):
        grades_of[x].update(zip(fam2, g2[i * len(fam2):(i + 1) * len(fam2)]))
        allp = {**base_probes(x), **stage2_probes(x)}
        f, miss = fit(kern, x, allp, grades_of[x], fits1[x][0])
        if len(f) == 1:
            signatures[x] = f[0]
        elif not f:
            ex_ = sorted(miss.items())[0]
            rejected[x] = f"stage 2 (follower/display/repetition probes): no hypothesis fits; e.g. {ex_[0]} fails {ex_[1]}"
        else:
            rejected[x] = f"ambiguous: {len(f)} hypotheses fit"
    print(f"[signatures] stage 3 (admission): {len(signatures)} admitted", flush=True)

    # 4. interleaving, to a fixpoint
    import tempfile
    fd, tmpname = tempfile.mkstemp(prefix="lp-strict-sig-", suffix=".json")
    import os
    os.close(fd)
    sig_tmp = Path(tmpname)
    rounds = []

    def ktmp(sigs):
        body = {"source": S.source_block(), "signatures": sigs}
        sig_tmp.write_text(json.dumps(body))
        return S.Kernel(signatures=sig_tmp, arg_signatures=None)

    def usable(sigs):
        nt = sorted(n for n, h in sigs.items() if not isinstance(h["text"], list))
        nm = sorted(n for n, h in sigs.items() if not isinstance(h["math"], list))
        return nt, nm

    def run_docs(sigs, docs):
        k = ktmp(sigs)
        models = k.run([{"doc": d} for _, d in docs])
        grades = grader.grade_all([m["tex"] for m in models], "interleave")
        return [(f, m, g, S.agrees(m, g)) for (f, _), m, g in zip(docs, models, grades)]

    try:
        while True:
            nt, nm = usable(signatures)
            docs = [d for s in range(args.interleave_seeds) for d in interleave_docs(nt, nm, s)]
            res = run_docs(signatures, docs)
            bad = [(f, m, g, why) for f, m, g, (ok, why) in res if not ok]
            rounds.append({"documents": len(res), "disagree": len(bad),
                           "families": sorted({f for f, *_ in res})})
            print(f"[signatures] stage 4 round {len(rounds)}: {len(res)} documents, "
                  f"{len(bad)} disagree", flush=True)
            if not bad:
                break
            # delta debugging on the name set of the first disagreeing family
            fam, _, _, why = bad[0]
            seed = next(s for s in range(args.interleave_seeds)
                        if any(f == fam for f, _ in interleave_docs(nt, nm, s)))
            pool = nt if fam.startswith("I-TEXT") else nm

            def fails(sub):
                subt = sub if pool is nt else []
                subm = sub if pool is nm else []
                d = [x for x in interleave_docs(subt, subm, seed) if x[0] == fam]
                if not d:
                    return False
                sigs = {n: signatures[n] for n in sub}
                return not run_docs(sigs, d)[0][3][0]

            cur = ddmin(list(pool), fails)
            if len(cur) > 3:
                raise SystemExit(f"stage 4: {fam} disagrees but delta debugging "
                                 f"stopped at {len(cur)} names ({why}); refusing to "
                                 f"reject them all (not reproducible?)")
            for x in cur:
                rejected[x] = (f"stage 4 (interleaving, {fam}): the minimal disagreeing "
                               f"set is {sorted(cur)}; first disagreement: {why}")
                signatures.pop(x, None)
            rounds[-1]["rejected"] = sorted(cur)
    finally:
        if sig_tmp.exists():
            sig_tmp.unlink()

    for x in names:
        evidence[x] = {f: [g["rc"], g["pdf"], g["error"], g["line"]]
                       for f, g in grades_of[x].items()}
    summary = {"candidates": len(names), "admitted": len(signatures),
               "rejected": len(rejected),
               "rejected_by_stage": {k: sum(1 for v in rejected.values() if v.startswith(k))
                                     for k in ("stage 0", "stage 1", "stage 2", "ambiguous", "stage 4")},
               "documents_graded_now": grader.graded,
               "grades_reused": grader.reused,
               "oracle_timeouts": sum(1 for g in grader.cache.values() if g["timed_out"])}
    by = {}
    for h in signatures.values():
        key = f"{h['text'] if isinstance(h['text'], str) else 'fatal ' + h['text'][1]}/" \
              f"{h['math'] if isinstance(h['math'], str) else 'fatal ' + h['math'][1]}"
        by[key] = by.get(key, 0) + 1
    summary["admitted_by_class"] = dict(sorted(by.items()))
    out = {
        "schema": "lp-strict-signatures/2",
        "generator": "scripts/tools/gen_strict_signatures.py",
        "generator_version": GENERATOR_VERSION,
        "source": S.source_block(),
        "oracle": oracle.provenance(),
        "kernel_extract_sha256": S.sha256_file(S.EXTRACT),
        "selection": {"rule": "control words (ASCII letters) of the closed world "
                              "minus par/begin/end, sorted by sha256(name), first n",
                      "n": args.n},
        "bounds": {"max_groups": MAX_GROUPS, "max_tokens": MAX_TOKENS,
                   "repeat": REPEAT},
        "reuse": reuse,
        "probes": {**base_probes("X"), **stage2_probes("X")},
        "probe_stages": {"1": fam1, "2": fam2},
        "hypotheses": HYPOTHESES,
        "admission_rule": "stage 0: check_strict_kernel.inertness_violation(meaning) is "
                          "None; stages 1-3: exactly one hypothesis makes the extracted "
                          "decider agree (_strict_s0.agrees) with the oracle on every "
                          "probe of stages 1 and 2; stage 4: every interleaving document "
                          "of the admitted set agrees",
        "summary": summary,
        "interleaving": {"seeds": args.interleave_seeds, "rounds": rounds},
        "signatures": dict(sorted(signatures.items())),
        "rejected": dict(sorted(rejected.items())),
        "meanings": dict(sorted(meanings.items())),
        "evidence": dict(sorted(evidence.items())),
    }
    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    Path(args.out).write_text(json.dumps(out, indent=1, sort_keys=False) + "\n")
    print(json.dumps(summary, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
