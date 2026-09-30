#!/usr/bin/env python3
"""Exhaustive check of the FMA site in read_jbig2_info (writejbig2.c:798-799, r78081):
    img_xres(img) = (int) (pip->xres * 0.0254 + 0.5);     (same for yres)
aarch64 compiles it to fmadd (one rounding), x86_64 to mul + add (two). pip->xres is an
unsigned 32-bit JBIG2 page-information field, so every input is enumerable. The two results
can differ only if x*0.0254 + 0.5 lies within a few ulps of an integer n, i.e. x within one
step (0.0254) of (n - 0.5)/0.0254; for every n reachable from a uint32 we test the
neighbouring integers x. Prints the number of inputs whose truncated results differ."""
import math
bad = []
N = int(0xFFFFFFFF * 0.0254) + 2
for n in range(1, N):
    t = (n - 0.5) / 0.0254
    for x in (math.floor(t) - 1, math.floor(t), math.floor(t) + 1, math.floor(t) + 2):
        if 0 <= x <= 0xFFFFFFFF:
            if int(x * 0.0254 + 0.5) != int(math.fma(x, 0.0254, 0.5)):
                bad.append(x)
print(f"n range 1..{N - 1}; inputs whose fused and unfused results differ: {len(bad)} {bad[:10]}")
