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
import _strict_capacity as C_  # noqa: E402
import _strict_dims as DM  # noqa: E402
import check_strict_kernel as CK  # noqa: E402

# Version 4 (C-92): stage 0's meaning closure follows robust commands
# (`\protect \X  ` to the inner name "X "); nothing else changed, and every
# probe grade of version 3 is reused (--reuse).
# Version 5 (C-94, C-96): the nesting families sit at the TeX-GROUP bound (a
# formula is a group: R-NEST-MATH is $ and 199 braces, no longer 200); stage
# 0 reads expansion texts by TeX's printing rules, every reading, and follows
# expl3 names and active characters (check_strict_kernel.body_readings); a
# reuse source is a committed file (REV:path), recorded with its commit.
# Version 7 (C-104): the DIMENSION account (stage D: every surviving name's
# dimensions measured from TeX's own box dumps, the boundary constants over
# every pair, the structural table; the repetition families are stage 2b,
# cut into paragraphs and formulas within the dimension bound; stage 3c adds
# every name at the dimension bound); memory costs are SLOPES over three
# counts past the base's high-water mark, in five contexts, plus the
# boundary constants (a letter's hyphenation, the inter-atom excess); every
# memory record carries pdfTeX's report; the round-1 review's documents are
# recorded (memory.review).
GENERATOR_VERSION = "7"
DIMS_EVIDENCE = S.REPO / "corpora/strict_s0/dims_s0.json"
MEMN = 4000
# the first count of a context with scripts (five tokens a unit; its material
# is past the base's high-water mark at 1,000 units already, which the gate
# checks, and the binary gate re-runs every document)
MEMN_SCRIPT = 1000
MEM_MAX_COUNT = 100000   # occurrences in one memory document at most
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
        self.dev_cache: Path | None = None

    @staticmethod
    def key(tex: str) -> str:
        return hashlib.sha256(tex.encode()).hexdigest()

    def grade_all(self, texs: list[str], label: str, stats: bool = False) -> list[dict]:
        """Every document's grade; with `stats`, a cached grade without
        pdfTeX's statistics (a reused one) is graded again (C-104: a memory
        record never lacks pdfTeX's report)."""
        todo = sorted({self.key(t): t for t in texs if self.key(t) not in self.cache
                       or (stats and "stats" not in self.cache[self.key(t)])}.items())
        t0, done = time.time(), [0]

        def g(kt):
            k, tex = kt
            r = S.grade(self.oracle, tex, timeout=300, stats=True)
            done[0] += 1
            if done[0] % 200 == 0:
                print(f"[signatures:{label}] graded {done[0]}/{len(todo)} "
                      f"({time.time() - t0:.0f}s)", flush=True)
            return k, r

        with ThreadPoolExecutor(self.workers) as ex:
            for k, r in ex.map(g, todo):
                self.cache[k] = r
        self.graded += len(todo)
        if self.dev_cache is not None and todo:
            self.dev_cache.write_text(json.dumps(self.cache))
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
    # the memory records keep pdfTeX's statistics: their grades are reused
    # WITH them (C-104)
    n_mem = seed_records(grader, old.get("memory", {}))
    grader.reused = len(outs) + n_mem
    return {**src, "generator_version": old.get("generator_version"),
            "grades_reused": len(outs) + n_mem}


def seed_records(grader: Grader, tree) -> int:
    """Seed the grades of every record of `tree` that carries its bytes'
    sha256, the oracle tuple and pdfTeX's statistics."""
    n = 0

    def walk(x):
        nonlocal n
        if isinstance(x, dict):
            if "sha256" in x and "oracle" in x and x.get("stats"):
                rc, pdf, err, line = x["oracle"]
                grader.cache[x["sha256"]] = {"rc": rc, "pdf": pdf, "passes": None,
                                             "timed_out": rc == -1, "error": err,
                                             "line": line, "stats": x["stats"]}
                n += 1
            for v in x.values():
                walk(v)
        elif isinstance(x, list):
            for v in x:
                walk(v)
    walk(tree)
    return n


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


def sig_kernel(tmpdir: Path, sigs: dict, token_cost: int, dtable: dict):
    """The extracted decider under a provisional signature set (every name
    with its cost and dim) and the structural dimension table."""
    p = tmpdir / f"sig-{len(sigs)}-{hashlib.sha256(json.dumps(sigs, sort_keys=True).encode()).hexdigest()[:12]}.json"
    p.write_text(json.dumps({"source": S.source_block(), "signatures": sigs,
                             "token_cost": token_cost, "dims": dtable}))
    return S.Kernel(signatures=p, arg_signatures=None)


def largest_all(kern, builds: list, hi: int) -> list[int]:
    """For each build(k), the largest k in [0, hi] whose document the model
    places inside the fragment (a binary search over all of them at once:
    one decider run a round)."""
    lo = [0] * len(builds)
    top = [hi] * len(builds)
    while True:
        todo = [i for i in range(len(builds)) if lo[i] < top[i]]
        if not todo:
            return lo
        mids = {i: (lo[i] + top[i] + 1) // 2 for i in todo}
        ms = kern.run([{"doc": builds[i](mids[i])} for i in todo])
        for i, m in zip(todo, ms):
            if m["verdict"] != "not_strict":
                lo[i] = mids[i]
            else:
                top[i] = mids[i] - 1


def _write_json(path: Path, obj) -> Path:
    path.write_text(json.dumps(obj))
    return path


def measure_dims(oracle, workers: int, text_names, math_names, text_cmds=(), math_cmds=(),
                 log=print):
    """Stage D (C-104): the dimension measurement of the names (each in the
    modes it does not stop in), with the fragment's characters and the
    text font's codes; a name whose items stop an instrument run is found by
    measuring each name alone and returned in `bad`."""
    run = lambda tex: DM.run_log(oracle, tex)  # noqa: E731
    bad: dict[str, str] = {}
    tn, mn = list(text_names), list(math_names)
    try:
        m = DM.measure(run, DM.plan_for(tn, mn, list(text_cmds), list(math_cmds)),
                       workers=workers)
        return m, bad
    except DM.DumpError as e:
        log(f"[signatures] stage D: {e}; measuring each name alone", flush=True)

    def alone(n):
        try:
            DM.measure(run, DM.Plan(
                {n: DM.snippet("name", n)} if n in tn else {},
                {n: DM.snippet("name", n)} if n in mn else {}, [], [], []))
            return n, None
        except DM.DumpError as e:
            return n, str(e)
    with ThreadPoolExecutor(workers) as ex:
        for n, why in ex.map(alone, sorted(set(tn) | set(mn))):
            if why:
                bad[n] = why
    tn = [n for n in tn if n not in bad]
    mn = [n for n in mn if n not in bad]
    m = DM.measure(run, DM.plan_for(tn, mn, list(text_cmds), list(math_cmds)),
                   workers=workers)
    return m, bad


def rep_depth(dims: DM.Dims, build, hi: int) -> int:
    """The largest k <= hi whose document build(k) is within the dimension
    bound by the account (nested families: the depth the bound allows)."""
    start = dims.tok("par", False)
    lo = 0
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if start + dims.nodes(build(mid)["body"], False) <= DM.DIM_BOUND:
            lo = mid
        else:
            hi = mid - 1
    return lo


def rep_probes(x: str, dims: DM.Dims) -> dict[str, dict]:
    """Stage 2b (C-104): the REPETITION families of stage2_probes, inside the
    fragment: a family whose document holds more than the dimension bound in
    one segment is cut into paragraphs (a formula into formulas, between
    noads) by `Dims.segment`, and the nesting families go as deep as the group
    bound AND the dimension bound allow. A family within the bound is the
    same document as before (its grade is reused)."""
    c, t = S.cmd(x), S.text
    p = stage2_probes(x)
    out = {}
    for f, d in p.items():
        if f in ("R-NEST-TEXT", "R-NEST-EACH-TEXT"):
            mk = (lambda k: S.doc(*_nest(k, [c, t("x")]))) if f == "R-NEST-TEXT" else \
                (lambda k: S.doc(*_nest_each(k, c)))
            out[f] = mk(rep_depth(dims, mk, MAX_GROUPS))
        elif f in ("R-NEST-MATH", "R-NEST-EACH-MATH"):
            mk = (lambda k: S.doc(_dollar(*_nest(k, [c, t("x")])))) if f == "R-NEST-MATH" \
                else (lambda k: S.doc(_dollar(*_nest_each(k, c))))
            out[f] = mk(rep_depth(dims, mk, MAX_GROUPS - 1))
        elif f in ("R-BIG-TEXT", "R-BIG-MATH"):
            # to the token bound AFTER the cut (its paragraph breaks and
            # formula delimiters are tokens too)
            mk = (lambda k: dims.segment(S, S.doc(*([c] * k), t("x")))) if f == "R-BIG-TEXT" \
                else (lambda k: dims.segment(S, S.doc(_paren(*([c] * k)))))
            lo, hi = 0, MAX_TOKENS
            while lo < hi:
                mid = (lo + hi + 1) // 2
                if C_._ulen(mk(mid)["body"]) + 1 <= MAX_TOKENS:
                    lo = mid
                else:
                    hi = mid - 1
            out[f] = mk(lo)
        elif "body" in d:
            out[f] = dims.segment(S, d)
        else:
            out[f] = d  # a token-level request: a few tokens, never near the bound
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=400)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--out", default=str(S.SIGNATURES))
    ap.add_argument("--dims-out", default=str(DIMS_EVIDENCE))
    ap.add_argument("--reuse", help="a previous signature file of the same oracle, "
                    "COMMITTED (REV:path, or a tracked unmodified path)")
    ap.add_argument("--interleave-seeds", type=int, default=3)
    ap.add_argument("--dev-cache", help="DEBUGGING ONLY: a local grade store read and "
                    "written across runs; refused with the committed --out (a local "
                    "store is never a reuse source of the evidence, LOW-2)")
    args = ap.parse_args()
    if args.dev_cache and Path(args.out).resolve() == S.SIGNATURES.resolve():
        raise SystemExit("--dev-cache is refused with the committed output")

    import tempfile
    tmpdir = Path(tempfile.mkdtemp(prefix="lp-strict-sig-"))
    oracle = _oracle.get_oracle()
    zero = _write_json(tmpdir / "zero-dims.json", {"dims": DM.zero_table()})
    # S. the memory costs of the structural tokens (C-98, C-104): each
    # structural shape at three token counts past the base's high-water mark,
    # and the base document; a token's cost is the largest slope of pdfTeX's
    # report per token (or report per token), rounded up, plus one. The
    # boundary constants: a letter's memory in a hyphenated word, and the
    # largest inter-atom excess over the eight classes of atom.
    kern0 = S.Kernel(signatures=None, arg_signatures=None, token_cost=0, dims=zero)
    struct = C_.structural_docs(S)
    grader0 = Grader(oracle, args.workers)
    if args.dev_cache:
        dc = Path(args.dev_cache)
        if dc.is_file():
            grader0.cache.update(json.loads(dc.read_text()))
        grader0.dev_cache = dc
    grader = grader0
    reuse0 = None
    if args.reuse:
        text0, _src0 = S.committed_source(args.reuse)
        seed_records(grader0, json.loads(text0).get("memory", {}))
    empty_sig = _write_json(tmpdir / "empty-sig.json",
                            {"source": S.source_block(), "signatures": {}, "token_cost": 0,
                             "dims": DM.zero_table()})

    def struct_models(kern_tree, sigfile):
        """(model, tex) of each structural document: a tree through the tree
        decider, the hyphenation instrument's bytes through the bytes decider
        (the account over the same tokens a file gives)."""
        trees = [{"doc": d} for _, d, ex in struct if not ex.get("bytes")]
        tm = iter(kern_tree.run(trees))
        bs = [C_.hyph_bytes(ex["units"]) for _, _, ex in struct if ex.get("bytes")]
        bm = iter(S.BytesKernel(signatures=sigfile, arg_signatures=None).run(bs))
        bb = iter(bs)
        out = []
        for _, _, ex in struct:
            if ex.get("bytes"):
                m = dict(next(bm))
                m["tex"] = next(bb).decode("ascii")
            else:
                m = next(tm)
            out.append(m)
        return out
    sm = struct_models(kern0, empty_sig)
    sg = grader0.grade_all([m["tex"] for m in sm], "structural", stats=True)
    memory = {"structural": {f: C_.memory_record(m, g, **ex)
                             for (f, _, ex), m, g in zip(struct, sm, sg)}}
    m0_ = memory["structural"]["BASE"]["used"]
    for f, _, ex in list(struct[1:]):
        name, k1 = f[2:].split("@")[0], ex["units"]
        r = memory["structural"][f]
        if not C_._ok(r):
            continue
        for k in C_.more_levels(r, m0_, k1, k1, 10 ** 6):
            d = None if ex.get("bytes") else C_.structural_doc(S, name, k)
            struct.append((f"S:{name}@{k}", d, {**ex, "units": k}))
    sm = struct_models(kern0, empty_sig)
    sg = grader0.grade_all([m["tex"] for m in sm], "structural2", stats=True)
    memory = {"structural": {f: C_.memory_record(m, g, **ex)
                             for (f, _, ex), m, g in zip(struct, sm, sg)}}
    # every model record is re-counted under the FINAL signatures at the end
    # (the costs are measured after the documents are): (record, request)
    remodel = [(memory["structural"][f], {"doc": d}) for f, d, _ in struct if d is not None]
    remodel_bytes = [(memory["structural"][f], C_.hyph_bytes(ex["units"]))
                     for f, d, ex in struct if d is None]
    M0 = memory["structural"]["BASE"]["used"]
    token_cost = C_.token_cost(memory["structural"])
    memory["token_cost"] = token_cost
    cp = C_.class_pair_docs()
    cpg = grader0.grade_all([tex for _, tex, _ in cp], "class-pairs", stats=True)
    memory["class_pairs"] = {f: C_.raw_record(tex, g, **ex)
                             for (f, tex, ex), g in zip(cp, cpg)}
    boundary = C_.boundary_constants(memory["structural"], memory["class_pairs"])
    memory["boundary"] = boundary
    print(f"[signatures] stage S: base {M0} words, token cost {token_cost}, "
          f"boundary {boundary}", flush=True)
    kern = S.Kernel(signatures=None, arg_signatures=None, token_cost=token_cost, dims=zero)
    names = candidates(args.n)
    if {UNDEF_A, UNDEF_B} & S.members():
        raise SystemExit("the look-ahead probes' undefined names are defined")
    reuse = seed_from(grader, kern, args.reuse, oracle) if args.reuse else reuse0
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

    # 2a. follower and display-follower families (the repetition families,
    # whose documents reach the bounds, are stage 2b's: they need the
    # dimensions)
    fam2 = list(stage2_probes("X"))
    fam2a = [f for f in fam2 if not f.startswith("R-")]
    r2 = [stage2_probes(x)[f] for x in alive for f in fam2a]
    g2 = grader.grade_all(render_all(kern, r2), "stage2a")
    fits2 = {}
    for i, x in enumerate(alive):
        grades_of[x].update(zip(fam2a, g2[i * len(fam2a):(i + 1) * len(fam2a)]))
        allp = {**base_probes(x), **{f: stage2_probes(x)[f] for f in fam2a}}
        f, miss = fit(kern, x, allp, grades_of[x], fits1[x][0])
        if f:
            fits2[x] = f
        else:
            ex_ = sorted(miss.items())[0]
            rejected[x] = f"stage 2 (follower/display/repetition probes): no hypothesis fits; e.g. {ex_[0]} fails {ex_[1]}"
    alive2 = [x for x in alive if x in fits2]
    print(f"[signatures] stage 2a: {len(alive2)} names still fit", flush=True)

    # D. the dimension account (C-104): each surviving name measured in the
    # modes its grades show it does not stop in (T-ALONE / M-ALONE compile),
    # with the characters and the text font's codes; the boundary constants
    # over every pair; the structural table.
    tn = [x for x in alive2 if grades_of[x]["T-ALONE"]["rc"] == 0]
    mn = [x for x in alive2 if grades_of[x]["M-ALONE"]["rc"] == 0]
    dmeas, dbad = measure_dims(oracle, args.workers, tn, mn)
    for x, why in dbad.items():
        rejected[x] = f"stage D (dimensions): its instrument does not run: {why}"
    alive2 = [x for x in alive2 if x not in dbad]
    dd = DM.derive(dmeas)
    dtable = DM.table(dd)
    dim_of = {x: [DM.up(dd["items"][x][0]) if x in tn else 0,
                  DM.up(dd["items"][x][1]) if x in mn else 0] for x in alive2}
    dfile = _write_json(tmpdir / "dims.json", {"dims": dtable})
    kern = S.Kernel(signatures=None, arg_signatures=None, token_cost=token_cost, dims=dfile)
    print(f"[signatures] stage D: {len(tn)} text / {len(mn)} math names measured; "
          f"B_text {dd['B_text']:.3f}pt, B_math {dd['B_math']:.3f}pt, script "
          f"{dd['script']:.3f}pt", flush=True)

    # 2b. the repetition families inside the fragment (rep_probes), then
    # admission over every family of stages 1 and 2
    def hyp_dim(x, hs):
        return [{**h, "dim": dim_of[x]} for h in hs]
    # (every stage-2 family: a follower document can pass the dimension
    # bound too, e.g. FM-CHARS of a wide name; within the bound it is the
    # same document and its grade is reused)
    rp_of = {x: rep_probes(x, DM.Dims(dtable, {x: dim_of[x]})) for x in alive2}
    r2b = [rp_of[x][f] for x in alive2 for f in fam2]
    g2b = grader.grade_all(render_all(kern, r2b), "stage2b")
    signatures: dict[str, dict] = {}
    for i, x in enumerate(alive2):
        grades_of[x].update(zip(fam2, g2b[i * len(fam2):(i + 1) * len(fam2)]))
        allp = {**base_probes(x), **rp_of[x]}
        f, miss = fit(kern, x, allp, grades_of[x], hyp_dim(x, fits2[x]))
        if len(f) == 1:
            signatures[x] = {k: v for k, v in f[0].items() if k != "dim"}
        elif not f:
            ex_ = sorted(miss.items())[0]
            rejected[x] = f"stage 2 (follower/display/repetition probes): no hypothesis fits; e.g. {ex_[0]} fails {ex_[1]}"
        else:
            rejected[x] = f"ambiguous: {len(f)} hypotheses fit"
    print(f"[signatures] stage 3 (admission): {len(signatures)} admitted", flush=True)
    for x in alive2:
        if x in rejected:
            print(f"[signatures]   rejected {x}: {rejected[x][:300]}", flush=True)
    if not signatures:
        raise SystemExit("no name admitted")

    # C. the memory cost of every admitted name (C-98, C-104): the name
    # repeated in text, in a formula and in a display, and with a sub- and a
    # superscript in both (a noad), each at three counts, the second and third
    # past the base's high-water mark; its cost is name_cost: the largest
    # slope (or report per occurrence) over the other tokens' cost, rounded up,
    # plus one, plus its boundaries (letters x H_text, atoms x B_math).
    def ctx_doc(x, ctx, k):
        return C_.name_mem_doc(S, x, ctx, k)

    def contexts(x):
        h = signatures[x]
        out = []
        if not isinstance(h["text"], list):
            out.append("TEXT")
        if not isinstance(h["math"], list):
            out += ["MATH", "DISPLAY"]
            if h["math"] == "noad":
                out += ["MSCRIPT", "DSCRIPT"]
        return out

    memory["names"] = {}

    def grade_mem(jobs, label):
        ms = kern.run([{"doc": ctx_doc(x, ctx, k), "signatures": {x: signatures[x]}}
                       for x, ctx, k in jobs])
        gs = grader.grade_all([m["tex"] for m in ms], label, stats=True)
        for (x, ctx, k), m, g in zip(jobs, ms, gs):
            r = C_.memory_record(m, g, count=k)
            memory["names"].setdefault(x, {})[f"R-MEM-{ctx}@{k}"] = r
            remodel.append((r, {"doc": ctx_doc(x, ctx, k)}))
    def unit_dim(x, ctx):
        return dim_of[x][1] + (2 * (dtable["script"][1] + dtable["char"]["x"][1])
                               if ctx == "DSCRIPT" else 0)
    def k1_of(ctx):
        return MEMN_SCRIPT if ctx == "MSCRIPT" else MEMN
    grade_mem([(x, ctx, k1_of(ctx)) for x in sorted(signatures) for ctx in contexts(x)
               if ctx not in ("DISPLAY", "DSCRIPT")]
              + [(x, ctx, k) for x in sorted(signatures) for ctx in contexts(x)
                 if ctx in ("DISPLAY", "DSCRIPT")
                 for k in C_.display_levels(unit_dim(x, ctx), MEM_MAX_COUNT)], "costs1")
    jobs = []
    for x in sorted(signatures):
        for ctx in contexts(x):
            if ctx in ("DISPLAY", "DSCRIPT"):
                continue
            r = memory["names"][x][f"R-MEM-{ctx}@{k1_of(ctx)}"]
            if not C_._ok(r):
                continue
            jobs += [(x, ctx, k) for k in C_.more_levels(r, M0, k1_of(ctx), k1_of(ctx),
                                                          MEM_MAX_COUNT)]
    grade_mem(jobs, "costs2")
    dmath = {x: dd["atoms"].get(x, 0) for x in signatures}
    for x in sorted(signatures):
        try:
            c = C_.name_cost(memory["names"].get(x, {}), M0, token_cost,
                             dd["letters"].get(x, 0) if x in tn else 0,
                             dmath[x] if x in mn else 0, boundary)
        except ValueError as e:
            rejected[x] = f"stage C (memory): {e}"
            signatures.pop(x)
            continue
        signatures[x] = {**signatures[x], "cost": token_cost if c is None else c,
                         "dim": dim_of[x], "atoms": dmath[x] if x in mn else 0,
                         "letters": dd["letters"].get(x, 0) if x in tn else 0}

    # the round-1 review's memory documents (C-104): graded here, so the
    # gate checks pdfTeX's report against the account on them for good
    review = {}
    rv = [(f, n, (lambda d=d: d)) for f, n, d in C_.review_docs(S) if n in signatures]
    ktmp0 = sig_kernel(tmpdir, signatures, token_cost, dtable)
    ms = ktmp0.run([{"doc": mk()} for _, _, mk in rv])
    gs = grader.grade_all([m["tex"] for m in ms], "review", stats=True)
    for (f, _, mk), m, g in zip(rv, ms, gs):
        review[f] = C_.memory_record(m, g)
        remodel.append((review[f], {"doc": mk()}))
    memory["review"] = review

    # 3c. every admitted name at the MEMORY bound and at the DIMENSION bound,
    # inside the fragment (C-98, C-104): at the memory bound, the name
    # repeated as often as the fragment allows (paragraphs or formulas of as
    # many as the dimension bound allows), graded, and once more, outside;
    # at the dimension bound, one paragraph / formula / display of as many
    # as the dimension bound allows, graded, with pdfTeX's own measure of
    # the box, and once more, outside.
    ktmp0 = sig_kernel(tmpdir, signatures, token_cost, dtable)
    dims_all = DM.Dims(dtable, {x: signatures[x]["dim"] for x in signatures})

    capdocs = []
    searches = []  # (x, family, build): the largest k inside the fragment
    for x in sorted(signatures):
        h = signatures[x]
        for where in ("TEXT", "MATH"):
            if isinstance(h["text" if where == "TEXT" else "math"], list):
                continue
            searches.append((x, f"R-CAP-{where}",
                             lambda k, x=x, where=where: C_.cap_doc(S, dims_all, x, where, k)))
        for where in ("TEXT", "MATH", "DISPLAY"):
            if isinstance(h["text" if where == "TEXT" else "math"], list):
                continue
            if h["dim"][0 if where == "TEXT" else 1] == 0:
                continue  # no dimensions: no dimension bound to reach
            searches.append((x, f"R-DIM-{where}",
                             lambda k, x=x, where=where: C_.dim_doc(S, x, where, k)))
    for (x, f, build), k in zip(searches, largest_all(ktmp0, [b for _, _, b in searches],
                                                      MAX_TOKENS)):
        capdocs.append((x, f, build(k), True, k))
        capdocs.append((x, f"{f}-PAST", build(k + 1), False, k + 1))
    capm = ktmp0.run([{"doc": d} for _, _, d, _, _ in capdocs])
    atm = [(i, m) for i, (m, q) in enumerate(zip(capm, capdocs)) if q[3]]
    capg = dict(zip([i for i, _ in atm],
                    grader.grade_all([m["tex"] for _, m in atm], "bounds", stats=True)))
    # pdfTeX's own measure of each dimension-bound document's material (an
    # instrument: the same material in one box, its width, height and depth)
    inst = {}
    for i, (x, f, d, at, cnt) in enumerate(capdocs):
        if at and f.startswith("R-DIM-"):
            snip = DM.snippet("name", x) * cnt
            ds = "\\displaystyle " if f == "R-DIM-DISPLAY" else ""
            box = snip if f == "R-DIM-TEXT" else "$" + ds + snip + "$"
            inst[i] = (DM.HEAD + "\\setbox0\\hbox{" + box + "}\\typeout{BOXDIM:\\the\\wd0:"
                       "\\the\\ht0:\\the\\dp0}\n\\end{document}\n")
    ilogs = {}
    with ThreadPoolExecutor(args.workers) as ex:
        for i, lg in zip(inst, ex.map(lambda t: DM.run_log(oracle, t), inst.values())):
            ilogs[i] = lg
    memory["cap"], dimcap = {}, {}
    for i, ((x, f, _, at, cnt), m) in enumerate(zip(capdocs, capm)):
        r = C_.memory_record(m, capg.get(i), count=cnt)
        if i in ilogs:
            mm = re.search(r"BOXDIM:(-?[\d.]+)pt:(-?[\d.]+)pt:(-?[\d.]+)pt", ilogs[i])
            r["box"] = [float(v) for v in mm.groups()] if mm else None
            import hashlib as _h
            r["box_tex_sha256"] = _h.sha256(inst[i].encode()).hexdigest()
        (dimcap if f.startswith("R-DIM-") else memory["cap"]).setdefault(x, {})[f] = r
        remodel.append((r, {"doc": capdocs[i][2]}))
    for x in list(signatures):
        for f, r in {**memory["cap"].get(x, {}), **dimcap.get(x, {})}.items():
            if f.endswith("-PAST"):
                if r["verdict"] != "not_strict":
                    rejected[x] = f"stage 3c ({f}): one past the bound is {r['verdict']}"
                    signatures.pop(x, None)
                    break
                continue
            m_ = next(m for (xx, ff, _, _, _), m in zip(capdocs, capm) if xx == x and ff == f)
            ok, why = S.agrees(m_, capg[[i for i, q in enumerate(capdocs)
                                        if q[0] == x and q[1] == f][0]])
            over = C_._ok(r) and r["used"] > M0 + r["mem"]
            box = r.get("box")
            wide = f.startswith("R-DIM-") and (box is None or sum(abs(v) for v in box) > r["dim"])
            if not ok or over or wide:
                rejected[x] = (f"stage 3c ({f}): {why}; {r.get('used')} words against "
                               f"{M0 + r['mem']}; box {box} against the account {r['dim']}")
                signatures.pop(x, None)
                break
    print(f"[signatures] stage C/3c: costs of {len(signatures)} names, max "
          f"{max(h['cost'] for h in signatures.values())}; {len(signatures)} admitted",
          flush=True)

    # 4. interleaving, to a fixpoint (each document cut within the dimension
    # bound, C-104)
    rounds = []

    def ktmp(sigs):
        return sig_kernel(tmpdir, sigs, token_cost, dtable)

    def usable(sigs):
        nt = sorted(n for n, h in sigs.items() if not isinstance(h["text"], list))
        nm = sorted(n for n, h in sigs.items() if not isinstance(h["math"], list))
        return nt, nm

    def run_docs(sigs, docs):
        k = ktmp(sigs)
        dz = DM.Dims(dtable, {n: sigs[n]["dim"] for n in sigs})
        models = k.run([{"doc": dz.segment(S, d)} for _, d in docs])
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
    except BaseException:
        import shutil
        shutil.rmtree(tmpdir, ignore_errors=True)
        raise

    # the records of rejected names go; every other model record is counted
    # again under the final signatures (its bytes are the same: the renderer
    # does not read the contract)
    for part in (memory["names"], memory["cap"], dimcap):
        for x in list(part):
            if x not in signatures:
                del part[x]
    keep = {id(r) for part in (memory["names"], memory["cap"], dimcap)
            for rs in part.values() for r in rs.values()}
    keep |= {id(r) for r in memory["structural"].values()}
    keep |= {id(r) for f, r in memory["review"].items()}
    memory["review"] = {f: r for f, r in memory["review"].items()
                        if f.split("-")[2] in signatures}
    remodel = [(r, q) for r, q in remodel if id(r) in keep]
    kfin = sig_kernel(tmpdir, signatures, token_cost, dtable)
    sfin = tmpdir / "final-sig.json"
    sfin.write_text(json.dumps({"source": S.source_block(), "signatures": signatures,
                                "token_cost": token_cost, "dims": dtable}))
    for (r, b), m in zip(remodel_bytes, S.BytesKernel(signatures=sfin, arg_signatures=None)
                         .run([b for _, b in remodel_bytes])):
        m = dict(m, tex=b.decode("ascii"))
        remodel.append((r, None))
        r.update({"ntoks": m["ntoks"], "held": m.get("held"), "mem": m.get("mem"),
                  "dim": m.get("dim"), "verdict": m["verdict"]})
    remodel = [(r, q) for r, q in remodel if q is not None]
    for (r, _), m in zip(remodel, kfin.run([q for _, q in remodel])):
        if hashlib.sha256(m["tex"].encode()).hexdigest() != r["sha256"]:
            raise SystemExit("remodel: a record's bytes changed under the final signatures")
        r.update({"ntoks": m["ntoks"], "held": m.get("held"), "mem": m.get("mem"),
                  "dim": m.get("dim"), "verdict": m["verdict"]})
    import shutil
    shutil.rmtree(tmpdir, ignore_errors=True)

    for x in names:
        evidence[x] = {f: [g["rc"], g["pdf"], g["error"], g["line"]]
                       for f, g in grades_of[x].items()}
    summary = {"candidates": len(names), "admitted": len(signatures),
               "rejected": len(rejected),
               "rejected_by_stage": {k: sum(1 for v in rejected.values() if v.startswith(k))
                                     for k in ("stage 0", "stage 1", "stage 2", "ambiguous",
                                               "stage D", "stage C", "stage 3c", "stage 4")},
               "documents_graded_now": grader.graded,
               "grades_reused": grader.reused,
               "oracle_timeouts": sum(1 for g in grader.cache.values() if g["timed_out"])}
    by = {}
    for h in signatures.values():
        key = f"{h['text'] if isinstance(h['text'], str) else 'fatal ' + h['text'][1]}/" \
              f"{h['math'] if isinstance(h['math'], str) else 'fatal ' + h['math'][1]}"
        by[key] = by.get(key, 0) + 1
    summary["admitted_by_class"] = dict(sorted(by.items()))
    dpath = Path(args.dims_out)
    dpath.parent.mkdir(parents=True, exist_ok=True)
    dpath.write_text(json.dumps({"schema": "lp-strict-dims/1",
                                 "generator": "scripts/tools/gen_strict_signatures.py",
                                 "generator_version": GENERATOR_VERSION,
                                 "oracle": oracle.provenance(),
                                 "measurement": dmeas}, indent=0) + "\n")
    dsha = S.sha256_file(dpath)
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
        "token_cost": token_cost,
        "memory": memory,
        # C-104: the dimension account. The structural table the loader reads
        # (strict_decide.ml set_sdims), the constants, and the measurement's
        # primary record in its own file (TeX's box dumps, the characters'
        # dimensions, the layout parameters, the noads), by sha256; the gate
        # re-derives every number from it (_strict_dims.derive).
        "dims": dtable,
        "dims_derivation": {"B_text": dd["B_text"], "B_math": dd["B_math"],
                            "script": dd["script"], "open": dd["open"],
                            "space": dd["space"], "par": dd["par"],
                            "display": dd["display"], "inline": dd["inline"],
                            "max_dim": DM.DIM_BOUND,
                            "evidence": {"file": (str(dpath.resolve().relative_to(S.REPO))
                                                  if dpath.resolve().is_relative_to(S.REPO)
                                                  else str(dpath)),
                                         "sha256": dsha},
                            "text_names": tn, "math_names": mn},
        "dim_bound": dimcap,
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
