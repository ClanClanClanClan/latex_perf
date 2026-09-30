#!/usr/bin/env python3
"""The FMA site in read_pdf_info (pdftoepdf.cc, r78081):
    float pdf_version_wanted = major_pdf_version_wanted + (minor_pdf_version_wanted * 0.1);
aarch64: fmadd (one rounding) then float conversion; x86_64: mul, add, float conversion.
pdfTeX refuses \\pdfminorversion outside 0..9 (pdftex.web 15475). Checks every major 0..9
and minor -1000..99999, and reports which pairs give different floats."""
import math
import struct
f32 = lambda x: struct.unpack('f', struct.pack('f', x))[0]  # noqa: E731
bad = [(M, m) for M in range(10) for m in range(-1000, 100000)
       if f32(M + m * 0.1) != f32(math.fma(m, 0.1, M))]
inrange = [(M, m) for M, m in bad if 0 <= m <= 9]
print(f"pairs differing: {len(bad)} {bad[:10]}; with minor in 0..9: {len(inrange)}")
