#!/usr/bin/env python3
"""The FMA sites in do_matrixtransform (utils.c:1494-1495, r78081), reached from
\\pdfsetmatrix (graphicx's pdftex.def issues it for every \\rotatebox and \\scalebox):
    x_new = x_old * m->a + y_old * m->c + m->e;   *retx = (scaled) DO_ROUND(x_new);
The unstripped aarch64 build computes fma(x, a, y*c) + e (fmul; fmadd; fadd); x86_64
computes (x*a + y*c) + e with two roundings. With a = cos(theta) the product x*a is inexact.
Random search over sp positions for inputs whose rounded results differ."""
import math
import random
import sys


def rnd(v):  # DO_ROUND then the C cast to an integer
    return int(v + .5) if v > 0 else int(v - .5)


random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
a, c, e = 0.866025, -0.5, 0.0
hits, n = [], 0
while len(hits) < 3 and n < 5_000_000:
    n += 1
    x, y = random.randint(-2**25, 2**25), random.randint(-2**25, 2**25)
    u = rnd(x * a + y * c + e)
    f = rnd(math.fma(x, a, y * c) + e)
    if u != f:
        hits.append((x, y, x * a + y * c + e, math.fma(x, a, y * c) + e, u, f))
print(f"tried {n}; differing: {len(hits)}")
for h in hits:
    print("x=%d y=%d unfused=%r fused=%r rounded %d vs %d" % h)
# the reviewer's example (round 1): x=11760000, y=31833967
x, y = 11760000, 31833967
print("reviewer example:", repr(x * a + y * c), repr(math.fma(x, a, y * c)))
