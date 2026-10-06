#!/usr/bin/env python3
"""b2sim.py SRC_ML_DIR OUT_ML_DIR: PROFILING ONLY (spike H.5 stage 1, the B1/B2 measurement of
H5-heap-design.md §5, candidate B). Copies an extracted tree and beta-reduces every use of
ExtrOcamlNatInt's realizer of `match` on a nat:

    (fun fO fS n -> if n=0 then fO () else fS (n-1)) (fun P0 -> A) (fun P1 -> B) N
 => (let n__b2 = N in if n__b2 = 0 then (let P0 = () in A) else (let P1 = n__b2 - 1 in B))

This is what candidate B2's Coq restructuring achieves in the compiled code: the successor branch
is no longer a heap closure whose environment (holding the state) stays live across the
branch's non-tail calls; its variables get ocamlopt's precise per-call-site liveness. It is a
pure beta-reduction (A and B are evaluated exactly when the realizer would evaluate them), so the
program computes the same function; the measured runs are compared byte for byte with the pinned
binary all the same. Every site found is rewritten, and the number rewritten is asserted equal to
the number of occurrences of the realizer's text in each file. Never a model build.
"""
import re, shutil, sys
from pathlib import Path

REAL = "(fun fO fS n -> if n=0 then fO () else fS (n-1))"


def skip_ws(s, i):
    while i < len(s) and s[i] in " \t\r\n":
        i += 1
    return i


def group_end(s, i):
    """s[i] == '(' : index just past the matching ')', skipping strings, chars and comments."""
    assert s[i] == "(", s[i:i + 40]
    depth = 0
    while i < len(s):
        c = s[i]
        if s.startswith("(*", i):
            d = 1; i += 2
            while d:
                if s.startswith("(*", i): d += 1; i += 2
                elif s.startswith("*)", i): d -= 1; i += 2
                else: i += 1
            continue
        if c == '"':
            i += 1
            while s[i] != '"':
                i += 2 if s[i] == "\\" else 1
            i += 1; continue
        if c == "'" and not (s[i - 1].isalnum() or s[i - 1] == "_"):
            m = re.match(r"'(\\(\d{3}|x[0-9a-fA-F]{2}|.)|[^\\])'", s[i:])
            if m:
                i += m.end(); continue
        if c == "(": depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    raise ValueError("unbalanced")


def rewrite(s):
    out, pos, n = [], 0, 0
    while True:
        k = s.find(REAL, pos)
        if k < 0:
            out.append(s[pos:]); return "".join(out), n
        out.append(s[pos:k])
        i = skip_ws(s, k + len(REAL))
        args = []
        for _ in range(2):
            j = group_end(s, i)
            m = re.match(r"\(fun\s+([A-Za-z_][A-Za-z0-9_']*)\s*->", s[i:j])
            assert m, s[i:i + 80]
            args.append((m.group(1), s[i + m.end():j - 1]))
            i = skip_ws(s, j)
        if s[i] == "(":
            j = group_end(s, i)
        else:
            m = re.match(r"[A-Za-z_][A-Za-z0-9_'.]*", s[i:]); assert m, s[i:i + 40]
            j = i + m.end()
        num = s[i:j]
        (p0, a), (p1, b) = args
        (a, na), (b, nb) = rewrite(a), rewrite(b)   # nested matches inside either branch
        num, nn = rewrite(num)
        n += na + nb + nn
        out.append(f"(let n__b2 = {num} in if n__b2 = 0 then (let {p0} = () in {a}) "
                   f"else (let {p1} = n__b2 - 1 in {b}))")
        pos, n = j, n + 1


def main():
    src, dst = Path(sys.argv[1]), Path(sys.argv[2])
    dst.mkdir(parents=True, exist_ok=True)
    total = 0
    for f in sorted(src.iterdir()):
        if f.suffix not in (".ml", ".mli"):
            continue
        s = f.read_text()
        want = s.count(REAL)
        if want:
            s, got = rewrite(s)
            assert got == want and REAL not in s, (f.name, want, got)
            total += got
            print(f"{f.name}: {got} sites")
        (dst / f.name).write_text(s)
    print(f"total {total} sites")


if __name__ == "__main__":
    main()
