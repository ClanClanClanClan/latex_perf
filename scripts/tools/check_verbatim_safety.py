#!/usr/bin/env python3
"""check_verbatim_safety.py — protected-region (verbatim/comment/url) corruption gate.

A fix producer must NEVER rewrite bytes the author wrote *literally*: inside a
`verbatim`/`lstlisting`/`minted` environment, an inline `\\verb|..|` /
`\\lstinline|..|`, a `%` line comment, or a `\\url{..}` target. Replacing a
literal U+2212 with `-`, deleting a control byte, collapsing spaces, or rewriting
`\\frac` inside such a region changes content the user deliberately typed — a
silent corruption the lint-output differential cannot see (it only checks which
rules fire and how many times, never what `--apply-fixes` *produces*).

Most CHAR/CJK/ENC/TYPO character-replacement producers predate the P3 exempt
layer and had this bug (30 confirmed in the v27.1.4 audit). The fix routed each
through `Validators_common.mk_result_with_fix_exempt`, which drops any edit whose
offset falls in a verbatim/comment/url/math range. This gate locks that in: it
plants a battery of every known producer trigger between unique sentinels inside
each protected-region kind, runs `--apply-fixes` (pilot AND default), and asserts
the bytes between the sentinels are byte-identical afterwards. Any producer —
existing or newly added — that corrupts a protected region fails the gate.

Exit 0 if every protected region is preserved, 1 otherwise (listing each
corrupted region with a before/after diff so the offending bytes are obvious).
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
import tempfile

# A battery of byte sequences that fix producers are known to replace / delete /
# collapse / insert-around. The point is breadth: if ANY producer fires inside a
# protected region, the bytes between the sentinels change and the gate trips.
# Grouped by family with a comment naming representative rule(s).
BATTERY = (
    b"ctl\x01here "  # CHAR-005 control U+0001
    b"bell\x07 bs\x08 ff\x0c del\x7f "  # CHAR-006/007/008/009
    b"zwj\xe2\x80\x8d lri\xe2\x81\xa6 lrm\xe2\x80\x8e bom\xef\xbb\xbf "  # CHAR-012/013/014, ENC-002/020
    b"cp1252\x91\x92\x93\x94 "  # ENC-004 Windows-1252 C1 bytes
    b"cjkcomma\xef\xbc\x8c cjkperiod\xef\xbc\x8e ideospace\xe3\x80\x80 "  # CJK-001/002/008
    b"cjkpunct\xe3\x80\x81\xe3\x80\x82 middot\xe3\x83\xbb "  # CHAR-016, CJK-014/015
    b"fwA\xef\xbc\xa1 fwB\xef\xbc\xa2 ligfi\xef\xac\x81 ligfl\xef\xac\x82 "  # CHAR-017/018
    b"minus\xe2\x88\x92 times\xc3\x97 "  # CHAR-019 / MATH-083, TYPO-061
    b"dash--range ellipsis... quotes''or`` "  # TYPO-002/026, TYPO-005, TYPO-004
    b"angle<x>y amp&z "  # TYPO-052, TYPO-023
    b"spaces   here trailing  \ttab\there "  # SPC-*/TYPO-018 whitespace
    b"mathfrac$\\frac{a}{b}$ prime$\\alpha''$ "  # MATH-014 / SCRIPT-016 (math inside verbatim)
)

# Each protected region: (name, prefix_before_battery, suffix_after_battery).
# Sentinels SREG_A .. bracket the battery so we can extract its exact bytes from
# the (possibly offset-shifted) output without tracking edit positions.
REGIONS = [
    ("verbatim-env", b"\\begin{verbatim}\nSREG_VA ", b" SREG_VB\n\\end{verbatim}\n"),
    ("lstlisting", b"\\begin{lstlisting}\nSREG_LA ", b" SREG_LB\n\\end{lstlisting}\n"),
    ("inline-verb", b"text \\verb|SREG_IA ", b" SREG_IB| more\n"),
    ("comment", b"%% SREG_CA ", b" SREG_CB\n"),
    ("url", b"see \\url{http://x/SREG_UA", b"SREG_UB} ok\n"),
]


def build_torture() -> bytes:
    out = [b"\\documentclass{article}\n"]
    for _name, pre, suf in REGIONS:
        out.append(pre + BATTERY + suf)
    return b"".join(out)


def cli(repo: str) -> str:
    return os.path.join(repo, "_build/default/latex-parse/src/validators_cli.exe")


def apply_fixes(binp: str, data: bytes, env) -> bytes:
    with tempfile.NamedTemporaryFile("wb", suffix=".tex", delete=False) as t:
        t.write(data)
        tp = t.name
    try:
        r = subprocess.run([binp, "--apply-fixes", tp], capture_output=True, env=env)
        # drop the leading "# profile=..." banner lines
        lines = [ln for ln in r.stdout.split(b"\n") if not ln.startswith(b"# ")]
        return b"\n".join(lines)
    finally:
        os.unlink(tp)


def between(data: bytes, a: bytes, b: bytes):
    i = data.find(a)
    j = data.find(b, i + len(a)) if i >= 0 else -1
    if i < 0 or j < 0:
        return None
    return data[i + len(a) : j]


def check(binp: str, env, label: str, violations: list) -> None:
    src = build_torture()
    out = apply_fixes(binp, src, env)
    for name, pre, suf in REGIONS:
        # sentinels are the first token after pre and last before suf
        sa = pre.split()[-1]
        sb = suf.split()[0]
        want = between(src, sa, sb)
        got = between(out, sa, sb)
        if want is None:
            continue
        # VERB-002 (catalog convert_tabs) is the ONE producer sanctioned to edit
        # verbatim-environment content: it replaces each hard tab with 4 spaces.
        # Allow EXACTLY that transform inside verbatim/lstlisting/minted env
        # bodies; everywhere else (inline \verb, % comment, \url) the protected
        # bytes must stay byte-identical. Any other change in any region — or a
        # non-tab change in an env body — still trips the gate.
        expected = want
        if name in ("verbatim-env", "lstlisting"):
            expected = want.replace(b"\t", b"    ")
        if got is None:
            violations.append(f"[{label}] {name}: region vanished (sentinels {sa!r}/{sb!r} missing in output)")
        elif got != expected:
            violations.append(
                f"[{label}] {name}: protected content CORRUPTED\n"
                f"      before: {expected!r}\n      after : {got!r}"
            )


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=".")
    ns = ap.parse_args()
    binp = cli(ns.repo)
    if not os.path.isfile(binp):
        subprocess.run(
            ["opam", "exec", "--", "dune", "build", "latex-parse/src/validators_cli.exe"],
            cwd=ns.repo, check=False,
        )
    if not os.path.isfile(binp):
        print("[verbatim-safety] FAIL: validators_cli.exe not built", file=sys.stderr)
        return 1

    violations: list = []
    pilot = dict(os.environ, L0_VALIDATORS="pilot")
    default = dict(os.environ)
    default.pop("L0_VALIDATORS", None)
    check(binp, pilot, "pilot", violations)
    check(binp, default, "default", violations)

    if violations:
        print(
            f"[verbatim-safety] FAIL: {len(violations)} protected-region corruption(s). "
            f"A fix producer rewrote literal bytes inside verbatim/\\verb/comment/url. "
            f"Route its fix through Validators_common.mk_result_with_fix_exempt "
            f"(or filter offsets by is_in_exempt_range):",
            file=sys.stderr,
        )
        for v in violations:
            print(f"  {v}", file=sys.stderr)
        return 1
    print(
        "[verbatim-safety] PASS: all verbatim / lstlisting / \\verb / comment / url "
        "regions byte-preserved under --apply-fixes (pilot + default)."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
