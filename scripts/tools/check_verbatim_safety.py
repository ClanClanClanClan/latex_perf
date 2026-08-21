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

R7-3 widened the gate past the verbatim family. `\\input{name}` and
`\\usepackage{name}` are NOT author-verbatim — nobody typed them to be shown
literally — but they are still bytes TeX reads as an identifier, and a typography
fix inside one asks TeX for a file that does not exist. Those regions are
withheld a layer later, by `Fix_guard`, so a failure on them points at the guard
rather than at a producer's exempt wiring.

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
    # v27.1.7 — triggers the audit found my v27.1.4 battery had MISSED:
    b"semi ; colon : tildes~~here "  # SPC-016 (space-;), SPC-021 (space-:), SPC-028 (~~)
    b"endash a\xe2\x80\x93z dots \\dots here "  # TYPO-026 (en-dash), SPC-025 (space-\\dots)
    b"url http://ex.test/page here "  # TYPO-039 (bare URL → \\url wrap)
    b"sec \\section{} here "  # STRUCT-002 (empty \\section → \\section{Untitled})
    b"ideomath $g\xe3\x80\x80h$ cjkmath $g\xe3\x80\x81h$ "  # CJK-008/015 (U+3000/U+3001 in $..$)
    # v27.1.13 — math OPERATORS inside a $..$ that sits in a protected region: a
    # math producer whose gate is context-blind find_math_ranges would rewrite
    # these (CHEM-005/MATH-046/SCRIPT-006 leaked before vcu_exempt). Must stay
    # byte-identical inside verbatim/comment/url.
    b"chemarr $a->b$ ldotsrel $a,\\ldots,b$ deg $5\xc2\xb0$ middot $a\xc2\xb7b$ le $a<=b$ "
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
    # R7-3 region 3: load-bearing ARGUMENTS. These are not protected by the P3
    # exempt layer at all — the author did not write them verbatim, they are
    # simply bytes TeX reads as an identifier rather than as prose. They are
    # withheld one layer later, by Fix_guard, so a failure here means the GUARD
    # has a hole, not that a producer needs mk_result_with_fix_exempt.
    # Planting the whole battery inside them is the point: the fixture corpus
    # proves the region against TYPO-002, this proves it against every producer
    # family at once. The battery's braces are balanced, so the argument's own
    # closing brace is still found.
    ("include-filename", b"\\input{SREG_FA", b"SREG_FB}\n"),
    ("package-spec", b"\\usepackage{SREG_PA", b"SREG_PB}\n"),
    # R7-3 region 4: cross-reference KEY arguments. TeX turns a key into a
    # \csname, so a rewritten byte changes which label is referenced and a
    # \text synthesised inside one is a hard error -- measured in
    # corpora/apply_fixes/adv_label_key.tex, where the fixer took pdflatex 0 -> 1
    # while --compile-check said READY on both sides. Note the region protects
    # the KEY GROUP only, never the whole command, so this plants the battery
    # inside the braces exactly as the two argument regions above do.
    ("xref-key", b"\\label{SREG_KA", b"SREG_KB}\n"),
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
    # NON-VACUITY. Every assertion below is "these bytes did not change", which
    # a fixer that produced nothing at all would satisfy perfectly. A CLI that
    # failed to run, a profile that enabled no producer, or a future refactor
    # that stopped the battery triggering would all read as a clean PASS. So
    # require positive evidence that the fixer fired somewhere OUTSIDE the
    # protected regions before trusting that it left the inside alone.
    if out == src:
        violations.append(
            f"[{label}] VACUOUS: --apply-fixes changed nothing anywhere in the "
            f"torture document, so byte-preservation inside the protected "
            f"regions proves nothing. The fixer is not running, or no producer "
            f"in this profile matches the battery.")
        return
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
            f"A fix producer rewrote bytes it must not touch. For a verbatim / "
            f"\\verb / comment / url region, route the fix through "
            f"Validators_common.mk_result_with_fix_exempt (or filter offsets by "
            f"is_in_exempt_range). For include-filename / package-spec, the "
            f"producer is not at fault — Fix_guard has a hole:",
            file=sys.stderr,
        )
        for v in violations:
            print(f"  {v}", file=sys.stderr)
        return 1
    # Name the regions from REGIONS rather than a hardcoded list, so adding one
    # cannot leave the success line claiming less than was actually checked.
    print(
        f"[verbatim-safety] PASS: {len(REGIONS)} regions byte-preserved under "
        f"--apply-fixes (pilot + default): "
        f"{', '.join(name for name, _pre, _suf in REGIONS)}."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
