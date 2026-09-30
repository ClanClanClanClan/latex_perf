#!/usr/bin/env python3
"""Kill-tests for h1diff.py's PDF canonical mask (spike H.1, review round 1).

usage: h1diff_selftest.py [path/to/h1diff.py]
Each case is (A bytes, B bytes, Ghostscript tags of A, of B, must-be-equal?).
The round-0 comparator (every /XXXXXX+ tag replaced, /Size /W /Index dropped)
FAILS cases 1-3; the narrowed one passes all."""
import importlib.util
import re
import sys
import zlib

path = sys.argv[1] if len(sys.argv) > 1 else __file__.replace("h1diff_selftest.py", "h1diff.py")
sys.argv = ["h1diff.py", "selftest", "arm64"]
spec = importlib.util.spec_from_file_location("h1diff", path)
h = importlib.util.module_from_spec(spec)
spec.loader.exec_module(h)
TD = h.td_regex("/nonexistent")


def pdf(font_tag: bytes, size: int, gs_tag: bytes = b"GSGSGS", xref_off: int = 1234) -> bytes:
    body = zlib.compress(b"BT /F1 10 Tf (x) Tj ET /" + gs_tag + b"+NimbusSans")
    return (b"%PDF-1.5\n1 0 obj\n<< /Type /FontDescriptor /FontName /" + font_tag
            + b"+CMR10 >>\nendobj\n2 0 obj\n<< /Length " + str(len(body)).encode()
            + b" /Filter /FlateDecode >>\nstream\n" + body + b"\nendstream\nendobj\n"
            + b"trailer\n<< /Size " + str(size).encode() + b" >>\nstartxref\n"
            + str(xref_off).encode() + b"\n%%EOF\n")


def equal(a, b, ga, gb):
    ok, _ = h.needed_masks("x.pdf", a, b, TD, TD, *( (ga, gb) if "ga" in h.needed_masks.__code__.co_varnames else () ))
    return ok


CASES = [
    ("pdfTeX's own subset tag differs", pdf(b"AAAAAA", 3), pdf(b"BBBBBB", 3), frozenset(), frozenset(), False),
    ("object count (/Size) differs", pdf(b"AAAAAA", 3), pdf(b"AAAAAA", 4), frozenset(), frozenset(), False),
    ("pdfTeX tag differs while a Ghostscript tag also differs",
     pdf(b"AAAAAA", 3, b"GSAAAA"), pdf(b"BBBBBB", 3, b"GSBBBB"),
     frozenset({b"GSAAAA"}), frozenset({b"GSBBBB"}), False),
    ("only the Ghostscript tag (inside a Flate stream) and the offsets differ",
     pdf(b"AAAAAA", 3, b"GSAAAA", 1234), pdf(b"AAAAAA", 3, b"GSBBBB", 1299),
     frozenset({b"GSAAAA"}), frozenset({b"GSBBBB"}), True),
    ("identical", pdf(b"AAAAAA", 3), pdf(b"AAAAAA", 3), frozenset(), frozenset(), True),
]
fails = 0
for name, a, b, ga, gb, want in CASES:
    got = equal(a, b, ga, gb)
    print(("ok  " if got == want else "FAIL"), f"{name}: equal={got}, expected {want}")
    fails += got != want
print(f"{len(CASES) - fails}/{len(CASES)} pass")
sys.exit(1 if fails else 0)
