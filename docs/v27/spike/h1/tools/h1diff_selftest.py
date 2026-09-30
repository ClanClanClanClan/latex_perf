#!/usr/bin/env python3
"""Kill-tests for h1diff.py's PDF canonical mask (spike H.1, review round 1).

usage: h1diff_selftest.py [path/to/h1diff.py]
Each case is (A bytes, B bytes, Ghostscript tags of A, of B, must-be-equal?).
The round-0 comparator (every /XXXXXX+ tag replaced, /Size /W /Index dropped)
FAILS cases 1-3. The round-1 comparator passes 1-5 but FAILS 6-11 (review
round 2): it engaged the canonical form with no Ghostscript intermediate, kept
nothing of the xref stream, and dropped bytes after a zlib end. The current
one passes all."""
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


def xpdf(body: bytes, xref: bytes, gs_tag: bytes = b"GSGSGS", pred: bool = False) -> bytes:
    """A PDF with one Flate content stream and an XRef stream (/W [1 3 1])."""
    parms = b""
    if pred:        # PNG Up predictor, 5 columns, as xpdf/pdfTeX may write it
        rows, prev = [], bytes(5)
        for i in range(0, len(xref), 5):
            r = xref[i:i + 5]
            rows.append(b"\x02" + bytes((r[k] - prev[k]) & 0xFF for k in range(5)))
            prev = r
        xref = b"".join(rows)
        parms = b" /DecodeParms << /Columns 5 /Predictor 12 >>"
    xs = zlib.compress(xref)
    c = zlib.compress(b"BT (x) Tj ET /" + gs_tag + b"+NimbusSans") if body is None else body
    return (b"%PDF-1.5\n2 0 obj\n<< /Length " + str(len(c)).encode() + b" /Filter /FlateDecode >>\nstream\n"
            + c + b"\nendstream\nendobj\n3 0 obj\n<< /Type /XRef /Size 4 /W [1 3 1]" + parms + b" /Length "
            + str(len(xs)).encode() + b" /Filter /FlateDecode >>\nstream\n" + xs
            + b"\nendstream\nendobj\nstartxref\n99\n%%EOF\n")


TXT = b"BT /F1 10 Tf (hello hello hello hello) Tj ET" * 20
X1 = b"\x01\x00\x00\x10\x00"          # type 1, offset 16, generation 0
X1b = b"\x01\x00\x00\x99\x00"         # type 1, offset 153: only the offset differs
X2 = b"\x02\x00\x00\x07\x00"          # type 2: in object stream 7, index 0
G, GA, GB = frozenset(), frozenset({b"GSAAAA"}), frozenset({b"GSBBBB"})

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
    # review round 2: no Ghostscript intermediate on either side -> no canonical form at all
    ("zlib level 1 vs 9, no Ghostscript intermediate",
     xpdf(zlib.compress(TXT, 1), X1), xpdf(zlib.compress(TXT, 9), X1), G, G, False),
    ("xref entry type 1 vs 2, no Ghostscript intermediate",
     xpdf(zlib.compress(TXT), X1), xpdf(zlib.compress(TXT), X2), G, G, False),
    ("bytes after the zlib end, no Ghostscript intermediate",
     xpdf(zlib.compress(TXT) + b"XX", X1), xpdf(zlib.compress(TXT) + b"YY", X1), G, G, False),
    # ... and with Ghostscript intermediates present, the canonical form must still see them
    ("xref entry type 1 vs 2, Ghostscript tags differ too",
     xpdf(None, X1, b"GSAAAA"), xpdf(None, X2, b"GSBBBB"), GA, GB, False),
    ("xref entry type 1 vs 2 under a PNG predictor, Ghostscript tags differ too",
     xpdf(None, X1, b"GSAAAA", True), xpdf(None, X2, b"GSBBBB", True), GA, GB, False),
    ("bytes after the zlib end, Ghostscript tags differ too",
     xpdf(zlib.compress(TXT) + b"XX", X1, b"GSAAAA"), xpdf(zlib.compress(TXT) + b"YY", X1, b"GSBBBB"), GA, GB, False),
    # the positive control of the same shapes: only Ghostscript's tag and a type-1 offset differ
    ("only the Ghostscript tag and a type-1 xref offset differ (xref stream, predictor)",
     xpdf(None, X1, b"GSAAAA", True), xpdf(None, X1b, b"GSBBBB", True), GA, GB, True),
]
fails = 0
for name, a, b, ga, gb, want in CASES:
    got = equal(a, b, ga, gb)
    print(("ok  " if got == want else "FAIL"), f"{name}: equal={got}, expected {want}")
    fails += got != want
print(f"{len(CASES) - fails}/{len(CASES)} pass")
sys.exit(1 if fails else 0)
