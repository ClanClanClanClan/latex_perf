#!/usr/bin/env python3
"""Generate the probe-attested signatures of the article contract's
ONE-ARGUMENT COMMANDS for the strict kernel (ADR-012 step 2, slice A).

WHAT A SIGNATURE IS (proofs/Strict/Contract.v, [asig]). A control word that
reads one undelimited macro argument, given as the brace group right after the
name. The kernel needs, per name:

    long:  long | short_inner | short_outer
    text:  ["now", R] | ["after", R] | ["run", material, P]
    math:  ["now", R] | ["after", R] | ["run", P]
           with R a reason (E3, E5, E6) and P in {text, text_restricted, math}

(Semantics.v: [R_arg_*], [Stops], [Scans]). pdfTeX reads the whole argument
before it runs any of it, so an error raised inside the argument is reported
where the file reader stands: the closing brace of the outermost argument. A
signature is never read from a definition (design §B.2), only attested.

HOW IT IS ATTESTED. Five stages, as gen_strict_signatures.py (phase 1); a name
leaves at the first stage it fails, with the evidence.

  0. RULE R-INERT (check_strict_kernel.inertness_violation), over the meanings
     at body start of the name and of everything its expansion reaches,
     robust commands' inner names included (C-92).
  1. BASE probes (families A-T-*, A-M-*): the name with an argument in text
     and in math, the argument holding each construct whose behaviour the
     hypotheses distinguish (an undefined name, a paragraph break, a blank
     line, $$, \\[ \\], $, a script, an unclosed formula, the name itself),
     every token on its own line so the LINE of every fatal separates "at the
     name", "at the break" and "at the closing brace".
  2. FOLLOWER, DISPLAY-FOLLOWER and REPETITION families (A-FT-*, A-FM-*,
     A-D-FOLLOW, A-R-*): the command followed by every token class in text and
     in math; right after a $ in display math (Semantics.display_bad_follower);
     300 times in text, in math, alternating, across paragraphs, groups,
     formulas and displays; nested 200 deep (the kernel's brace bound: every
     level of the command opens TeX groups of its own, C-86) in text and in
     math; repeated to the token bound, and with an argument of the token
     bound's size.
  3. ADMISSION: exactly one hypothesis (HYPOTHESES) makes the EXTRACTED
     decider agree with the oracle (_strict_s0.agrees: verdict, message class,
     line) on every probe of stages 1 and 2.
  4. INTERLEAVING: seeded documents interleaving all admitted names with each
     other (nested) and with the phase-1 names, in text and math, graded
     against the kernel with the final signature sets; a disagreement is
     reduced by delta debugging and its minimal set rejected, to a fixpoint.

CANDIDATES (a rule, not a list). The control words (ASCII letters) of the
article closed world, minus par/begin/end, minus the names phase 1 admitted,
whose meaning at body start -- through one robust wrapper `\\protect \\X  `,
to the meaning of "X " -- is a macro whose parameter text is exactly `#1`. The
parameter text is a HINT (design §B.2: static arity is not behaviour), used to
choose which names to probe; it is never an attestation. Commands that read
their argument through another macro (the math alphabets \\mathrm, \\mathbf:
`\\use@mathgroup`, then `\\math@egroup`) or through TeX's math scanner (math
accents, \\sqrt, \\overline) are not candidates of this rule.

GRADE REUSE: `--reuse FILE` seeds the grades of byte-identical documents from a
previous file of the same oracle (every provenance field equal).

OUTPUT: corpora/contracts/strict/article-s1-arg-signatures.json (schema
lp-strict-arg-signatures/1). Needs the oracle:
    python3 scripts/tools/gen_strict_arg_signatures.py [--workers 6] [--reuse F]
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import random
import re
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import _oracle  # noqa: E402
import _strict_capacity as C  # noqa: E402
import _strict_s0 as S  # noqa: E402
import check_strict_kernel as CK  # noqa: E402
import gen_strict_signatures as G  # noqa: E402

# Version 2 (C-94, C-96): a run behaviour carries the TeX GROUPS the command
# holds open while its argument runs, MEASURED (stage G: the deepest brace
# nesting inside the argument that pdfTeX survives, against the body's
# measured capacity); the nesting families sit at the TeX-group bound; stage
# 3b grades every frame-kind pair the model can stack with the command, at
# the bound (A-CAP-*); stage 0 reads expansion texts by every reading
# (check_strict_kernel.body_readings); reuse sources are committed files.
GENERATOR_VERSION = "2"
OUT = S.ARG_SIGNATURES
UNDEF = "lpqundefa"
MAX_GROUPS, MAX_TOKENS = CK.MAX_GROUPS, CK.MAX_TOKENS
REPEAT = 300
SAFE_CHARS = G.SAFE_CHARS

REASONS = ("E3", "E5", "E6")
PAYS = ("text", "text_restricted", "math")
LONGS = ("long", "short_inner", "short_outer")


def hypotheses() -> list[dict]:
    texts = ([["now", r] for r in REASONS] + [["after", r] for r in REASONS]
             + [["run", m, p] for m in (True, False) for p in PAYS])
    maths = ([["now", r] for r in REASONS] + [["after", r] for r in REASONS]
             + [["run", p] for p in PAYS])
    out = []
    for t in texts:
        for m in maths:
            # a command that stops before reading its argument in both modes
            # never reads it: its longness is not observable, only "long" is
            # a hypothesis then
            longs = ["long"] if (t[0] == "now" and m[0] == "now") else LONGS
            for lg in longs:
                out.append({"long": lg, "text": t, "math": m})
    return out


HYPOTHESES = hypotheses()


# ------------------------------------------------------------- the probes ---

t, c, g, sp, par = S.text, S.cmd, S.group, S.space, S.par


def _dollar(*b): return S.math("dollar", *b)
def _display(*b): return S.math("display", *b)
def _paren(*b): return S.math("paren", *b)
def _bracket(*b): return S.math("bracket", *b)
def _sup(a): return S.script(True, a)
def _sub(a): return S.script(False, a)


def A(x: str, *payload) -> list:
    """The command with its argument: two nodes."""
    return [c(x), g(*payload)]


def base_probes(x: str) -> dict[str, dict]:
    y = t("y")
    return {
        # text
        "A-T-ALONE": S.doc(*A(x, t("x"))),
        "A-T-EMPTY": S.doc(*A(x)),
        "A-T-SPACE": S.doc(*A(x, sp())),
        "A-T-MID": S.doc(t("a"), sp(), *A(x, t("x")), sp(), t("b")),
        "A-T-PAR": S.doc(t("a"), par(True), *A(x, t("x"))),
        "A-T-GROUP": S.doc(g(*A(x, t("x")))),
        "A-T-UNDEF": S.doc(*A(x, t("a"), c(UNDEF), t("b"))),
        "A-T-PARARG": S.doc(*A(x, t("a"), par(True), t("b"))),
        "A-T-BLANKARG": S.doc(*A(x, t("a"), par(False), t("b"))),
        "A-T-PARLATE": S.doc(*A(x, c(UNDEF), t("a"), par(True), t("b"))),
        "A-T-DD": S.doc(*A(x, _display(y))),
        "A-T-BRK": S.doc(*A(x, _bracket(y))),
        "A-T-BRKOPEN": S.doc(*A(x, {"raw": ["open_bracket"]}, y)),
        "A-T-DOLLAR": S.doc(*A(x, _dollar(y))),
        "A-T-SUP": S.doc(*A(x, y, _sup(t("2")))),
        "A-T-SHIFT": S.doc(*A(x, {"raw": ["dollar"]}, y)),
        "A-T-NEST": S.doc(*A(x, *A(x, y))),
        "A-T-NESTPAR": S.doc(*A(x, t("a"), *A(x, y, par(True)), c(UNDEF))),
        "A-T-STRAY": S.doc(*A(x, y), S.stray()),
        "A-T-NOEND": S.doc(*A(x, y), has_end=False),
        # math
        "A-M-ALONE": S.doc(_dollar(*A(x, t("x")))),
        "A-M-EMPTY": S.doc(_dollar(*A(x))),
        "A-M-SCRIPTS": S.doc(_dollar(*A(x, t("x")), _sup(t("a")), _sup(t("b")))),
        "A-M-TAIL": S.doc(_dollar(y, _sup(t("a")), *A(x, t("x")), _sup(t("b")))),
        "A-M-DOLLAR": S.doc(_dollar(*A(x, _dollar(y)))),
        "A-M-SUP": S.doc(_dollar(*A(x, y, _sup(t("2"))))),
        "A-M-UNDEF": S.doc(_dollar(*A(x, t("a"), c(UNDEF), t("b")))),
        "A-M-PARARG": S.doc(_dollar(*A(x, t("a"), par(True), t("b")))),
        "A-M-DD": S.doc(_dollar(*A(x, _display(y)))),
        "A-M-BRK": S.doc(_dollar(*A(x, _bracket(y)))),
        "A-M-DISPLAY": S.doc(_display(*A(x, t("x")))),
        "A-M-GROUP": S.doc(_dollar(g(*A(x, t("x"))))),
        "A-M-SCRIPTARG": S.doc(_dollar(y, _sup(g(*A(x, t("x")))))),
        "A-M-NEST": S.doc(_dollar(*A(x, *A(x, y)))),
        "A-M-PAREN": S.doc(_paren(*A(x, t("x")))),
        "A-M-BRACKETS": S.doc(_bracket(*A(x, t("x")))),
    }


FOLLOWERS = {
    "CHARS": [t(SAFE_CHARS)], "OPEN": [g(t("z"))], "CLOSE": [S.stray()],
    "PAR": [par(True)], "BLANK": [par(False)], "DOLLAR": [_dollar(t("z"))],
    "DISPLAY": [_display(t("z"))], "MOPEN": [_paren(t("z"))],
    "BOPEN": [_bracket(t("z"))], "SUP": [_sup(t("z"))], "UNDEF": [c(UNDEF)],
    "SPACE": [sp(), t("z")], "SELF": None,
}


def stage2_probes(x: str, gt: int = 1, gm: int = 1) -> dict[str, dict]:
    """Stage 2's families; the nesting families depend on the command's
    measured groups in text (gt) and math (gm): they sit at the TeX-group
    bound (C-94). The recorded templates are those of g = 1."""
    y = t("y")
    p: dict[str, dict] = {}
    for k, f in FOLLOWERS.items():
        f = A(x, y) if f is None else f
        p[f"A-FT-{k}"] = S.doc(*A(x, y), *f)
        # in math the follower stays in the formula; the formula is then closed
        mf = {"DOLLAR": [{"raw": ["dollar"]}], "DISPLAY": [{"raw": ["dollar"]}, {"raw": ["dollar"]}],
              "PAR": [par(True)], "BLANK": [par(False)], "MOPEN": [{"raw": ["open_paren"]}],
              "BOPEN": [{"raw": ["open_bracket"]}]}.get(k, f)
        p[f"A-FM-{k}"] = S.doc(_dollar(*A(x, y), *mf))
    p["A-FT-END"] = S.doc(*A(x, y))
    p["A-FT-EOF"] = S.doc(*A(x, y), has_end=False)
    p["A-FM-MCLOSE"] = S.doc(_paren(*A(x, y)))
    p["A-FM-BCLOSE"] = S.doc(_bracket(*A(x, y)))
    p["A-D-FOLLOW"] = S.doc(_display(t("x"), {"raw": ["dollar"]}, *A(x, y), {"raw": ["dollar"]}))
    # repetition
    one = A(x, y)
    p["A-R-TEXT"] = S.doc(*(one * REPEAT))
    p["A-R-TEXT-ALT"] = S.doc(*[n for _ in range(REPEAT) for n in (*one, t("z"))])
    p["A-R-PARS"] = S.doc(*[n for _ in range(REPEAT) for n in (*one, par(False))])
    p["A-R-GROUPS"] = S.doc(*[g(*one) for _ in range(REPEAT)])
    p["A-R-MATH"] = S.doc(_dollar(*(one * REPEAT)))
    p["A-R-FORMULAS"] = S.doc(*[_dollar(*one) for _ in range(REPEAT)])
    p["A-R-DISPLAYS"] = S.doc(*[_display(*one) for _ in range(REPEAT)])
    # nesting to the TeX-group bound (Decide.v max_groups, C-94): as many
    # levels of the command as its groups allow; in math the formula is one
    # of the groups (an inner level runs from the argument's mode, so it
    # costs gt or gm: the larger is taken, and the exact bound for every
    # combination is stage 3b's)
    def nest(k):
        inner = [y]
        for _ in range(k):
            inner = A(x, *inner)
        return inner
    p["A-R-NEST-TEXT"] = S.doc(*nest(MAX_GROUPS // max(gt, 1)))
    p["A-R-NEST-MATH"] = S.doc(_dollar(*A(x, *nest((MAX_GROUPS - 1 - gm)
                                                    // max(gt, gm, 1)))))
    # to the token bound: the command with a one-character argument (4 tokens)
    k = (MAX_TOKENS - 4) // 4
    p["A-R-BIG-TEXT"] = S.doc(*(one * k))
    p["A-R-BIG-MATH"] = S.doc(_paren(*(one * k)))
    # an argument of the token bound's size
    p["A-R-BIG-ARG"] = S.doc(*A(x, t("y" * (MAX_TOKENS - 4))))
    return p


def _req(d: dict) -> dict:
    """A probe as a request: trees, except the few that need a raw token (an
    unbalanced delimiter inside an argument) -- those are token streams."""
    s = json.dumps(d)
    if '"raw"' not in s:
        return {"doc": d}
    return {"toks": _toks_of_doc(d)}


def _toks_of_doc(d: dict) -> list:
    out: list = []

    def node(n):
        if isinstance(n, dict) and "raw" in n:
            out.append(n["raw"])
            return
        k = n[0]
        if k == "text":
            out.extend(["char", ch] for ch in n[1])
        elif k == "space":
            out.append(["space"])
        elif k == "par":
            out.append(["par", n[1]])
        elif k == "group":
            out.append(["open"])
            for m in n[1]:
                node(m)
            out.append(["close"])
        elif k == "stray":
            out.append(["close"])
        elif k == "math":
            o, cl = {"dollar": ([["dollar"]], [["dollar"]]),
                     "display": ([["dollar"], ["dollar"]], [["dollar"], ["dollar"]]),
                     "paren": ([["open_paren"]], [["close_paren"]]),
                     "bracket": ([["open_bracket"]], [["close_bracket"]])}[n[1]]
            out.extend(o)
            for m in n[2]:
                node(m)
            out.extend(cl)
        elif k == "script":
            out.append(["sup" if n[1] else "sub"])
            node(n[2])
        elif k == "cmd":
            out.append(["cs", n[1]])
        else:
            raise ValueError(k)
    for n in d["body"]:
        node(n)
    if d["has_end"]:
        out.append(["end"])
    return out


# --------------------------------------------------------------- selection ---

def candidates(meanings: dict[str, str], admitted1: set[str]) -> list[str]:
    """The selection rule; check_strict_kernel.arg_candidates is its one
    implementation (the gate re-applies it to the recorded meanings)."""
    return CK.arg_candidates(meanings, admitted1)


def all_words() -> list[str]:
    return sorted(m for m in S.members() if re.fullmatch(r"[A-Za-z]+", m))


# ----------------------------------------------------------------- fitting ---

def with_g(h: dict, gt: int, gm: int) -> dict:
    """A hypothesis with the command's TeX groups in its run behaviours
    (the loader refuses a run behaviour without them, C-94)."""
    h = json.loads(json.dumps(h))
    if h["text"][0] == "run":
        h["text"] = h["text"][:3] + [gt]
    if h["math"][0] == "run":
        h["math"] = h["math"][:2] + [gm]
    return h


def fit(kern, x: str, reqs: dict[str, dict], grades: dict[str, dict],
        hyps: list[dict], gt: int = 1, gm: int = 1) -> tuple[list[dict], dict]:
    """The hypotheses under which the extracted kernel agrees with every
    grade. Before stage G has measured the command's groups, gt = gm = 1
    stands in: no probe of stage 1 comes near the group bound, so the
    groups cannot change a verdict there (they only decide membership)."""
    fams = list(reqs)
    preq = [dict(_req(reqs[f]), arg_signatures={x: with_g(h, gt, gm)})
            for h in hyps for f in fams]
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
    return [o["tex"] for o in kern.run([_req(r) for r in reqs])]


def seed_from(grader, kern, spec: str, oracle) -> dict:
    """Seed the grades of a previous argument-signature file COMMITTED to the
    repository (S.committed_source; LOW-2 of the C-94 review)."""
    text, src = S.committed_source(spec)
    old = json.loads(text)
    prov, cur = old.get("oracle", {}), oracle.provenance()
    diff = sorted(k for k in set(prov) | set(cur) if prov.get(k) != cur.get(k))
    if diff:
        raise SystemExit(f"--reuse {spec}: graded by another oracle ({diff} differ)")
    fams = old["probes"]
    reqs, keys = [], []
    for x, ev in old["evidence"].items():
        for f, gr in ev.items():
            if f not in fams:
                continue
            d = json.loads(json.dumps(fams[f]).replace('"X"', json.dumps(x)))
            reqs.append(_req(d))
            keys.append(gr)
    outs = kern.run(reqs) if reqs else []
    for o, gr in zip(outs, keys):
        rc, pdf, err, line = gr
        grader.cache[G.Grader.key(o["tex"])] = {
            "rc": rc, "pdf": pdf, "passes": None, "timed_out": rc == -1,
            "error": err, "line": line}
    grader.reused = len(outs)
    return {**src, "generator_version": old.get("generator_version"),
            "grades_reused": len(outs)}


# -------------------------------------------------------------- capacity ---

def _braces(j: int, inner: list) -> list:
    node = inner
    for _ in range(j):
        node = [g(*node)]
    return node


def measure_groups(grader, kern, names: list[str], hi: int = 300) -> dict:
    """Stage G (C-94). K: the body's grouping capacity, as the formula plus
    the deepest brace nesting in it that pdfTeX survives. For each command
    and mode, the deepest brace nesting inside its argument that pdfTeX
    survives, jmax; the command's groups are then K - jmax in text and
    K - 1 - jmax in math (the formula is one). None when the argument does
    not run there (the command alone does not compile). Bisection, all
    commands in lockstep; every document is graded by the one oracle."""
    fams = {("K", "math"): lambda j: S.doc(_dollar(*_braces(j, [t("x")])))}
    for x in names:
        fams[(x, "text")] = (lambda x_: lambda j: S.doc(*A(x_, *_braces(j, [t("x")]))))(x)
        fams[(x, "math")] = (lambda x_: lambda j: S.doc(_dollar(*A(x_, *_braces(j, [t("x")])))))(x)
    keys = sorted(fams)

    def ok_all(pts):
        texs = render_all(kern, [fams[k](j) for k, j in pts])
        grs = grader.grade_all(texs, "groups")
        return [gr["rc"] == 0 and gr["pdf"] for gr in grs], grs

    lo_ok, _ = ok_all([(k, 0) for k in keys])
    hi_ok, hi_gr = ok_all([(k, hi) for k in keys])
    state = {}
    for k, a, b, gr in zip(keys, lo_ok, hi_ok, hi_gr):
        if not a:
            state[k] = None
        elif b:
            raise SystemExit(f"stage G: {k} survives {hi} braces: the search range is wrong")
        else:
            state[k] = [0, hi, gr["error"]]
    while True:
        todo = [k for k in keys if state[k] and state[k][1] - state[k][0] > 1]
        if not todo:
            break
        mids = [(k, (state[k][0] + state[k][1]) // 2) for k in todo]
        oks, grs = ok_all(mids)
        for (k, m), ok, gr in zip(mids, oks, grs):
            if ok:
                state[k][0] = m
            else:
                state[k][1], state[k][2] = m, gr["error"]
    if state[("K", "math")] is None:
        raise SystemExit("stage G: a formula alone does not compile")
    K = state[("K", "math")][0] + 1
    groups = {}
    for x in names:
        jt, jm = state[(x, "text")], state[(x, "math")]
        groups[x] = {"text": None if jt is None else K - jt[0],
                     "math": None if jm is None else K - 1 - jm[0],
                     "jmax_text": None if jt is None else jt[0],
                     "jmax_math": None if jm is None else jm[0],
                     "overflow_text": None if jt is None else jt[2],
                     "overflow_math": None if jm is None else jm[2]}
    return {"K": K, "K_overflow": state[("K", "math")][2], "groups": groups,
            "rule": "K = 1 + the deepest brace nesting pdfTeX survives inside $...$; "
                    "a command's groups = K - jmax in text, K - 1 - jmax in math, jmax "
                    "the deepest brace nesting it survives inside the command's argument"}


# ------------------------------------------------------------ interleaving ---

def payload_mode(h: dict, where: str) -> str | None:
    """The mode a command's argument runs in when the command is used in
    `where` (text or math); None when it does not run there."""
    b = h["text"] if where == "text" else h["math"]
    return CK.run_pay(b, where) if b[0] == "run" else None


def interleave_docs(sigs: dict[str, dict], w_t: list[str], w_m: list[str],
                    seed: int) -> list[tuple[str, dict]]:
    """Seeded documents interleaving the admitted one-argument commands with
    each other (nested up to three deep, each inner command chosen among the
    names that run in its host argument's mode) and with the phase-1 names
    (inside the arguments, in the argument's mode), at least REPEAT commands
    per document."""
    rng = random.Random(seed)
    run_t = sorted(n for n, h in sigs.items() if payload_mode(h, "text"))
    run_m = sorted(n for n, h in sigs.items() if payload_mode(h, "math"))
    out = []

    def fill(mode: str, depth: int) -> list:
        where = "math" if mode == "math" else "text"
        pool, ws = (run_m, w_m) if where == "math" else (run_t, w_t)
        parts = [t("q")]
        if ws:
            parts.append(c(rng.choice(ws)))
        if depth < 3 and pool and rng.random() < 0.6:
            z = rng.choice(pool)
            parts += A(z, *fill(payload_mode(sigs[z], where), depth + 1))
        parts.append(t("w"))
        return parts

    def seq(pool):
        s = []
        while len(s) < max(REPEAT, len(pool)):
            q = list(pool)
            rng.shuffle(q)
            s += q
        return s

    if run_t:
        body = []
        for i, x in enumerate(seq(run_t)):
            body += A(x, *fill(payload_mode(sigs[x], "text"), 1))
            body += [sp()] + ([par(False)] if i % 11 == 10 else [])
        out.append(("I-A-TEXT", S.doc(*body)))
    if run_m:
        body = []
        for x in seq(run_m):
            body += A(x, *fill(payload_mode(sigs[x], "math"), 1)) + [t("r")]
        out.append(("I-A-MATH", S.doc(_dollar(*body))))
        body = []
        for x in seq(run_m)[:REPEAT]:
            body.append(_display(*A(x, *fill(payload_mode(sigs[x], "math"), 1)), t("p")))
        out.append(("I-A-DISPLAYS", S.doc(*body)))
    return out


# ------------------------------------------------------------------- main ---

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--workers", type=int, default=6)
    ap.add_argument("--out", default=str(OUT))
    ap.add_argument("--reuse", help="a previous argument-signature file of the same "
                    "oracle, COMMITTED (REV:path, or a tracked unmodified path)")
    ap.add_argument("--interleave-seeds", type=int, default=3)
    ap.add_argument("--only", help="comma-separated candidate names (debugging; "
                    "the output is then not the rule's and the gate refuses it)")
    args = ap.parse_args()

    oracle = _oracle.get_oracle()
    sig1 = json.loads(S.SIGNATURES.read_text())
    admitted1 = set(sig1["signatures"])
    kern = S.Kernel(arg_signatures=None)
    if UNDEF in S.members():
        raise SystemExit("the probes' undefined name is defined")
    grader = G.Grader(oracle, args.workers)
    reuse = seed_from(grader, kern, args.reuse, oracle) if args.reuse else None

    # the selection rule, over the whole closed world's meanings
    words = all_words()
    wm = G.dump_meanings(oracle, words)
    rob = sorted(n for n in words if wm[n] == f"macro:->\\protect \\{n}  ")
    wm.update(G.dump_meanings(oracle, [n + " " for n in rob]))
    names = candidates(wm, admitted1)
    if args.only:
        names = [n for n in names if n in set(args.only.split(","))]
    print(f"[arg-signatures] {len(names)} candidates by the selection rule", flush=True)

    # 0. inertness rule
    world, active = CK.closed_world(S.REPO), CK.active_chars(S.REPO)
    meanings = G.meaning_closure(oracle, names, world, active)
    prims = S.primitives()
    rejected: dict[str, str] = {}
    for x in names:
        v = CK.inertness_violation(x, meanings, prims, world, active)
        if v:
            rejected[x] = f"stage 0 (inertness rule): {v}"
    alive0 = [x for x in names if x not in rejected]
    print(f"[arg-signatures] stage 0: {len(rejected)} of {len(names)} not inert", flush=True)

    # 1. base probes of the inert names
    fam1 = list(base_probes("X"))
    r1 = [base_probes(x)[f] for x in alive0 for f in fam1]
    g1 = grader.grade_all(render_all(kern, r1), "base")
    grades_of: dict[str, dict[str, dict]] = {}
    for i, x in enumerate(alive0):
        grades_of[x] = dict(zip(fam1, g1[i * len(fam1):(i + 1) * len(fam1)]))
    fits1 = {x: fit(kern, x, base_probes(x), grades_of[x], HYPOTHESES) for x in alive0}
    alive = [x for x in alive0 if fits1[x][0]]
    for x in alive0:
        if not fits1[x][0]:
            ex_ = sorted(fits1[x][1].items())[0]
            rejected[x] = f"stage 1 (base probes): no hypothesis fits; e.g. {ex_[0]} fails {ex_[1]}"
    print(f"[arg-signatures] stage 1: {len(alive)} names still fit", flush=True)

    # G. the TeX groups each surviving command holds open while its argument
    # runs, per mode (C-94): the deepest brace nesting inside the argument
    # that pdfTeX survives, against the body's capacity K measured here the
    # same way (a formula and braces in it). A command whose argument does
    # not run in a mode has no count there (1 stands in; no run hypothesis
    # of that mode can fit it).
    cap = measure_groups(grader, kern, alive)
    gt_of = {x: cap["groups"][x]["text"] or 1 for x in alive}
    gm_of = {x: cap["groups"][x]["math"] or 1 for x in alive}
    print(f"[arg-signatures] stage G: capacity K = {cap['K']}; groups "
          f"{ {x: (cap['groups'][x]['text'], cap['groups'][x]['math']) for x in alive} }",
          flush=True)

    # 2. follower, display-follower, repetition families (the nesting ones
    # at the group bound for the command's measured groups)
    fam2 = list(stage2_probes("X"))
    r2 = [stage2_probes(x, gt_of[x], gm_of[x])[f] for x in alive for f in fam2]
    g2 = grader.grade_all(render_all(kern, r2), "stage2")
    signatures: dict[str, dict] = {}
    for i, x in enumerate(alive):
        grades_of[x].update(zip(fam2, g2[i * len(fam2):(i + 1) * len(fam2)]))
        allp = {**base_probes(x), **stage2_probes(x, gt_of[x], gm_of[x])}
        f, miss = fit(kern, x, allp, grades_of[x], fits1[x][0], gt_of[x], gm_of[x])
        if len(f) == 1:
            signatures[x] = with_g(f[0], gt_of[x], gm_of[x])
        elif not f:
            ex_ = sorted(miss.items())[0]
            rejected[x] = f"stage 2 (follower/display/repetition probes): no hypothesis fits; e.g. {ex_[0]} fails {ex_[1]}"
        else:
            rejected[x] = f"ambiguous: {len(f)} hypotheses fit: {f}"
    print(f"[arg-signatures] stage 3 (admission): {len(signatures)} admitted", flush=True)

    # 4. interleaving
    fd, tmpname = tempfile.mkstemp(prefix="lp-strict-asig-", suffix=".json")
    os.close(fd)
    tmp = Path(tmpname)
    rounds = []
    w_t = sorted(n for n, h in sig1["signatures"].items() if not isinstance(h["text"], list))
    w_m = sorted(n for n, h in sig1["signatures"].items() if not isinstance(h["math"], list))

    def ktmp(sigs):
        tmp.write_text(json.dumps({"source": S.source_block(), "arg_signatures": sigs}))
        return S.Kernel(arg_signatures=tmp)

    def run_docs(sigs, docs):
        k = ktmp(sigs)
        models = k.run([_req(d) for _, d in docs])
        grades = grader.grade_all([m["tex"] for m in models], "interleave")
        return [(f, m, gr, S.agrees(m, gr)) for (f, _), m, gr in zip(docs, models, grades)]

    context: dict = {}

    def stage4() -> None:
        while True:
            docs = [d for s in range(args.interleave_seeds)
                    for d in interleave_docs(signatures, w_t, w_m, s)]
            if not docs:
                rounds.append({"documents": 0, "disagree": 0, "families": []})
                break
            res = run_docs(signatures, docs)
            bad = [(f, m, gr, why) for f, m, gr, (ok, why) in res if not ok]
            rounds.append({"documents": len(res), "disagree": len(bad),
                           "families": sorted({f for f, *_ in res})})
            print(f"[arg-signatures] stage 4 round {len(rounds)}: {len(res)} documents, "
                  f"{len(bad)} disagree", flush=True)
            if not bad:
                break
            fam, _, _, why = bad[0]
            seed = next(s for s in range(args.interleave_seeds)
                        if any(f == fam for f, _ in interleave_docs(signatures, w_t, w_m, s)))
            pool = sorted(signatures)

            def fails(sub):
                sigs = {n: signatures[n] for n in sub}
                d = [q for q in interleave_docs(sigs, w_t, w_m, seed) if q[0] == fam]
                if not d:
                    return False
                return not run_docs(sigs, d)[0][3][0]

            cur = G.ddmin(list(pool), fails)
            if len(cur) > 3:
                raise SystemExit(f"stage 4: {fam} disagrees but delta debugging stopped "
                                 f"at {len(cur)} names ({why})")
            for x in cur:
                rejected[x] = (f"stage 4 (interleaving, {fam}): the minimal disagreeing "
                               f"set is {sorted(cur)}; first disagreement: {why}")
                signatures.pop(x, None)
            rounds[-1]["rejected"] = sorted(cur)

    # 5. CONTEXT: an argument can put the phase-1 names in a mode phase 1
    # never probed them in (restricted horizontal mode: an hbox; text inside
    # math). Every phase-1 name is run inside a carrier of each such mode; a
    # disagreement means the phase-1 signature does not hold there, and every
    # command whose argument runs in that mode leaves. Returns whether a name
    # left (stage 4 then runs again on the smaller set).
    def stage5() -> bool:
        if True:
            carriers = {}
            for n in sorted(signatures, key=lambda q: hashlib.sha256(q.encode()).hexdigest()):
                h = signatures[n]
                for where in ("text", "math"):
                    pm = payload_mode(h, where)
                    if pm and pm != "math" and not (where == "text" and pm == "text"):
                        carriers.setdefault((where, pm), n)
            cdocs = []
            for (where, pm), n in sorted(carriers.items()):
                for w in sorted(sig1["signatures"]):
                    tag = f"C-{where}-{pm}"
                    if where == "text":
                        cdocs.append((tag, w, S.doc(*A(n, t("a"), c(w), t("b")))))
                        cdocs.append((tag, w, S.doc(*A(n, c(w)))))
                    else:
                        cdocs.append((tag, w, S.doc(_dollar(*A(n, t("a"), c(w), t("b"))))))
                        cdocs.append((tag, w, S.doc(_dollar(y_ := t("y"), *A(n, c(w)), y_))))
            context.clear()
            if not cdocs:
                context.update({"carriers": {}, "documents": 0, "disagree": 0})
                return False
            res = run_docs(signatures, [(tag, d) for tag, _, d in cdocs])
            bad_modes: dict[str, list] = {}
            per_name: dict[str, list] = {}
            for (tag, w, _), (_, m, gr, (ok, why)) in zip(cdocs, res):
                per_name.setdefault(w, []).append([tag, gr["rc"], gr["pdf"], gr["error"],
                                                   gr["line"], ok])
                if not ok:
                    bad_modes.setdefault(tag, []).append(f"{w}: {why}")
            context.update({"carriers": {f"{a}/{b}": n for (a, b), n in carriers.items()},
                            "documents": len(res),
                            "disagree": sum(len(v) for v in bad_modes.values()),
                            "failures": {k: v[:20] for k, v in bad_modes.items()},
                            "evidence": per_name})
            print(f"[arg-signatures] stage 5 (context): {len(res)} documents, "
                  f"{context['disagree']} disagree", flush=True)
            if not bad_modes:
                return False
            for tag, fails_ in bad_modes.items():
                _, where, pm = tag.split("-", 2)
                for n in list(signatures):
                    if payload_mode(signatures[n], where) == pm:
                        rejected[n] = (f"stage 5 (context {where}/{pm}): phase-1 names are not "
                                       f"attested in that mode; e.g. {fails_[0]}")
                        signatures.pop(n)
            return True

    # 3b. CAPACITY (C-94): every frame-kind pair the extracted model can
    # stack with an admitted command (strict_decide.exe --frame-pairs under
    # the admitted set), as a stream repeating the pair to exactly the group
    # bound: the model must decide it and agree with pdfTeX; one group past
    # it, the model must place it outside the fragment. A command in a
    # failing pair leaves, and the stage repeats on the smaller set.
    capacity_rounds = []

    def stage3b() -> None:
        while signatures:
            k = ktmp(signatures)
            pairs = k.frame_pairs()
            groups = C.arg_groups(signatures)
            items = []
            for p_ in pairs["pairs"]:
                who = sorted({lab[4:].split(":", 1)[1].rsplit("/", 1)[0]
                              for lab in (p_["below"], p_["above"]) if lab.startswith("arg.")})
                if not who:
                    continue
                at = C.stream(pairs, p_["below"], p_["above"], MAX_GROUPS, groups)
                past = C.stream(pairs, p_["below"], p_["above"], MAX_GROUPS + 1, groups)
                items.append((p_["below"], p_["above"], who, at, past))
            bad: dict[str, str] = {}
            reqs = []
            for b_, a_, who, at, past in items:
                if at is None or past is None:
                    for x in who:
                        bad.setdefault(x, f"{b_}>{a_}: no stream reaches the bound")
                    continue
                reqs += [C.request(at[0]), C.request(past[0])]
            models = k.run(reqs)
            ats = models[0::2]
            grs = grader.grade_all([m["tex"] for m in ats], "capacity")
            i = 0
            for b_, a_, who, at, past in items:
                if at is None or past is None:
                    continue
                m, mp, gr = ats[i], models[2 * i + 1], grs[i]
                i += 1
                ok, why = S.agrees(m, gr)
                if not (m["peak_groups"] == MAX_GROUPS and C.adjacent(m["peak_frames"], b_, a_)):
                    ok, why = False, f"the stream peaks at {m['peak_groups']} without the pair"
                if not (mp["verdict"] == "not_strict" and mp["peak_groups"] == MAX_GROUPS + 1):
                    ok, why = False, f"one group past the bound: {mp['verdict']} {mp['peak_groups']}"
                for x in who:
                    grades_of[x][f"A-CAP:{b_}>{a_}"] = gr
                    if not ok:
                        bad.setdefault(x, f"{b_}>{a_}: {why}")
            capacity_rounds.append({"pairs": len(items), "rejected": sorted(bad)})
            print(f"[arg-signatures] stage 3b (capacity): {len(items)} pairs, "
                  f"{len(bad)} commands fail", flush=True)
            if not bad:
                return
            for x, why in bad.items():
                rejected[x] = f"stage 3b (capacity, A-CAP): {why}"
                signatures.pop(x, None)

    try:
        stage3b()
        while True:
            stage4()
            if not stage5():
                break
    finally:
        if tmp.exists():
            tmp.unlink()

    evidence = {x: {f: [gr["rc"], gr["pdf"], gr["error"], gr["line"]]
                    for f, gr in grades_of[x].items()} for x in grades_of}
    by: dict[str, int] = {}
    for h in signatures.values():
        key = f"{h['long']}|{'.'.join(map(str, h['text']))}|{'.'.join(map(str, h['math']))}"
        by[key] = by.get(key, 0) + 1
    summary = {"candidates": len(names), "admitted": len(signatures),
               "rejected": len(rejected),
               "rejected_by_stage": {k: sum(1 for v in rejected.values() if v.startswith(k))
                                     for k in ("stage 0", "stage 1", "stage 2", "ambiguous",
                                               "stage 3b", "stage 4", "stage 5")},
               "documents_graded_now": grader.graded, "grades_reused": grader.reused,
               "oracle_timeouts": sum(1 for gr in grader.cache.values() if gr["timed_out"]),
               "admitted_by_class": dict(sorted(by.items()))}
    out = {
        "schema": "lp-strict-arg-signatures/1",
        "generator": "scripts/tools/gen_strict_arg_signatures.py",
        "generator_version": GENERATOR_VERSION,
        "source": S.source_block(),
        "oracle": oracle.provenance(),
        "kernel_extract_sha256": S.sha256_file(S.EXTRACT),
        "signatures_sha256": S.sha256_file(S.SIGNATURES),
        "selection": {"rule": "check_strict_kernel.arg_candidates: control words (ASCII "
                              "letters) of the closed world minus par/begin/end, minus "
                              "the names of the phase-1 signature file, whose meaning at "
                              "body start (through one robust wrapper, to the meaning of "
                              "the inner name) is a macro with parameter text exactly #1",
                      "only": args.only, "names": names},
        # every closed-world control word's meaning at body start (and the
        # inner meaning of every robust one): the gate re-applies the rule
        "selection_meanings": dict(sorted(wm.items())),
        "bounds": {"max_groups": MAX_GROUPS, "max_tokens": MAX_TOKENS,
                   "repeat": REPEAT},
        "capacity": {**cap, "stage3b_rounds": capacity_rounds},
        "reuse": reuse,
        "probes": {**base_probes("X"), **stage2_probes("X")},
        "probe_stages": {"1": fam1, "2": fam2},
        "hypotheses": HYPOTHESES,
        "admission_rule": "stage 0: check_strict_kernel.inertness_violation(meaning) is "
                          "None; stages 1-3: exactly one hypothesis makes the extracted "
                          "decider agree (_strict_s0.agrees) with the oracle on every "
                          "probe of stages 1 and 2 (with the command's TeX groups measured "
                          "by stage G); stage 3b: every frame-kind pair the model stacks "
                          "with the command agrees at the group bound and is outside the "
                          "fragment one group past it (A-CAP-*); stage 4: every "
                          "interleaving document of the admitted set agrees",
        "summary": summary,
        "interleaving": {"seeds": args.interleave_seeds, "rounds": rounds},
        "context": context,
        "arg_signatures": dict(sorted(signatures.items())),
        "rejected": dict(sorted(rejected.items())),
        "meanings": dict(sorted(meanings.items())),
        "evidence": dict(sorted(evidence.items())),
    }
    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    Path(args.out).write_text(json.dumps(out, indent=1) + "\n")
    print(json.dumps(summary, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
