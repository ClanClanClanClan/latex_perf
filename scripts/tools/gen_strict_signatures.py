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

HOW IT IS ATTESTED (the rule this tool implements). For each candidate name X
the tool builds the PROBES below, 15 small documents using X in text and in
math next to the constructs the kernel models (a paragraph break, a group, a
formula, a script), and grades each once with the ONE oracle (the pinned
image, `_oracle.py`). Then, for each of the 12 HYPOTHESES (every text x math
behaviour above), it asks the EXTRACTED kernel (`strict_decide.exe`, the Coq
decider itself) what it predicts for every probe if X had that signature. X is
admitted with hypothesis H iff H is the ONLY hypothesis whose predictions
agree with the oracle on all 15 probes, under the differential's own
agreement rule (`_strict_s0.agrees`: verdict, reason class and line). So a
signature is, by construction, a claim the kernel has been seen to make
correctly about X in every probed context; nothing about X is hand-written,
and a name no hypothesis explains (it takes an argument, looks ahead, errors
elsewhere, changes catcodes, ...) is rejected with the evidence.

CANDIDATES. Control words (ASCII letters only: the fragment's names) defined
in the article configuration's closed world at body start (the kernel file
updated by corpora/contracts/article.json), minus the three names the grammar
itself gives structure to (`par`: the explicit paragraph break; `begin`,
`end`: \\begin{document} and \\end{document}). A deterministic sample: the
first N by sha256 of the name (`--n`, default 400). Selection is by rule,
never by hand.

OUTPUT. corpora/contracts/strict/article-s0-signatures.json (schema
lp-strict-signatures/1): the source files' hashes, the oracle's provenance,
the probes, the admitted signatures, the rejected names with the reason, and
per name the oracle's grade of every probe.

Needs the oracle (docker and the pinned image). Usage:
    python3 scripts/tools/gen_strict_signatures.py [--n 400] [--workers 4]
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
import _strict_s0 as S  # noqa: E402

GENERATOR_VERSION = "2"
STRUCTURAL = {"par", "begin", "end"}
# Two control words outside the closed world (checked in main()).
UNDEF_A, UNDEF_B = "lpqundefa", "lpqundefb"

TEXT_H = ("material", "noop", ["fatal", "E3"])
MATH_H = ("noad", "noop", ["fatal", "E3"], ["fatal", "E6"])
HYPOTHESES = [{"text": t, "math": m} for t in TEXT_H for m in MATH_H]


def probes(x: str) -> dict[str, dict]:
    c = S.cmd(x)
    t, dollar, display = S.text, (lambda *b: S.math("dollar", *b)), (lambda *b: S.math("display", *b))
    sup, sub = (lambda a: S.script(True, a)), (lambda a: S.script(False, a))
    return {
        "T-ALONE": S.doc(c),
        "T-MID": S.doc(t("a"), c, t("b")),
        "T-GROUP": S.doc(S.group(c), t("x")),
        "T-PAR": S.doc(c, S.par(), t("x")),
        "T-DOLLAR": S.doc(c, dollar(t("x"))),
        "T-SUP": S.doc(t("a"), c, sup(t("b"))),
        "T-SPACE": S.doc(c, S.space(), c, S.par(True)),
        "M-ALONE": S.doc(dollar(c)),
        "M-MID": S.doc(dollar(t("a"), c, t("b"))),
        "M-GROUP": S.doc(dollar(S.group(c))),
        "M-RESET": S.doc(dollar(t("x"), sup(t("a")), c, sup(t("b")))),
        "M-SUB": S.doc(dollar(c, sub(t("a"))), t("y")),
        "M-DISPLAY": S.doc(display(c, t("z"))),
        # Look-ahead probes (generator version 2, C-84): a command that
        # expands or reads a token AFTER its neighbour (\expandafter) passes
        # every probe above, and shows only in the LINE of an error raised by
        # what follows it. Two undefined control words after X: the first
        # must be the one reported. A blank line after X in math: the
        # paragraph break's own line must be the one reported.
        "T-UNDEF": S.doc(c, S.cmd(UNDEF_A), S.cmd(UNDEF_B)),
        "M-PAR": S.doc(dollar(c, S.par(), t("x"))),
    }


def candidates(n: int) -> list[str]:
    import re
    names = [m for m in S.members()
             if re.fullmatch(r"[A-Za-z]+", m) and m not in STRUCTURAL]
    names.sort(key=lambda m: hashlib.sha256(m.encode()).hexdigest())
    return names[:n]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=400)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--out", default=str(S.SIGNATURES))
    args = ap.parse_args()

    oracle = _oracle.get_oracle()
    kern = S.Kernel(signatures=None)
    names = candidates(args.n)
    if {UNDEF_A, UNDEF_B} & S.members():
        raise SystemExit("the look-ahead probes' undefined names are defined")
    families = list(probes("X").keys())
    print(f"[signatures] {len(names)} candidates x {len(families)} probes", flush=True)

    # 1. Render every probe (the extracted renderer) and grade it once.
    reqs = [{"doc": probes(x)[f]} for x in names for f in families]
    rendered = kern.run(reqs)
    t0 = time.time()
    done = [0]

    def g(o):
        r = S.grade(oracle, o["tex"])
        done[0] += 1
        if done[0] % 200 == 0:
            print(f"[signatures] graded {done[0]}/{len(rendered)} "
                  f"({time.time() - t0:.0f}s)", flush=True)
        return r

    with ThreadPoolExecutor(args.workers) as ex:
        grades = list(ex.map(g, rendered))

    # 2. Predictions of the extracted kernel under every hypothesis.
    preq = [{"doc": probes(x)[f], "signatures": {x: h}}
            for x in names for h in HYPOTHESES for f in families]
    preds = kern.run(preq)

    signatures, rejected, evidence = {}, {}, {}
    k = 0
    for i, x in enumerate(names):
        gx = grades[i * len(families):(i + 1) * len(families)]
        evidence[x] = {f: [gr["rc"], gr["pdf"], gr["error"], gr["line"]]
                       for f, gr in zip(families, gx)}
        fits = []
        first_miss = {}
        for h in HYPOTHESES:
            ok = True
            for f, gr in zip(families, gx):
                p = preds[k]
                k += 1
                a, why = S.agrees(p, gr)
                if not a and ok:
                    ok = False
                    first_miss[json.dumps(h)] = f"{f}: {why}"
            if ok:
                fits.append(h)
        if len(fits) == 1:
            signatures[x] = fits[0]
        elif not fits:
            ex_ = sorted(first_miss.items())[0]
            rejected[x] = f"no hypothesis fits; e.g. {ex_[0]} fails {ex_[1]}"
        else:
            rejected[x] = f"ambiguous: {len(fits)} hypotheses fit"

    summary = {"candidates": len(names), "admitted": len(signatures),
               "rejected": len(rejected), "probes_graded": len(grades),
               "oracle_timeouts": sum(1 for gr in grades if gr["timed_out"])}
    by = {}
    for h in signatures.values():
        key = f"{h['text'] if isinstance(h['text'], str) else 'fatal ' + h['text'][1]}/" \
              f"{h['math'] if isinstance(h['math'], str) else 'fatal ' + h['math'][1]}"
        by[key] = by.get(key, 0) + 1
    summary["admitted_by_class"] = dict(sorted(by.items()))
    out = {
        "schema": "lp-strict-signatures/1",
        "generator": "scripts/tools/gen_strict_signatures.py",
        "generator_version": GENERATOR_VERSION,
        "source": S.source_block(),
        "oracle": oracle.provenance(),
        "kernel_extract_sha256": S.sha256_file(S.EXTRACT),
        "selection": {"rule": "control words (ASCII letters) of the closed world "
                              "minus par/begin/end, sorted by sha256(name), first n",
                      "n": args.n},
        "probes": {f: d for f, d in probes("X").items()},
        "hypotheses": HYPOTHESES,
        "admission_rule": "admitted iff exactly one hypothesis makes the extracted "
                          "decider agree (_strict_s0.agrees) with the oracle on "
                          "every probe",
        "summary": summary,
        "signatures": dict(sorted(signatures.items())),
        "rejected": dict(sorted(rejected.items())),
        "evidence": dict(sorted(evidence.items())),
    }
    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    Path(args.out).write_text(json.dumps(out, indent=1, sort_keys=False) + "\n")
    print(json.dumps(summary, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
