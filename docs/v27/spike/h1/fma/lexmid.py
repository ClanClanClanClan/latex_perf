# Constructive search: a PDF MediaBox numeral whose xpdf parse (Lexer.cc:157-221) differs between
# fused (aarch64) and unfused (x86_64) arithmetic AND whose (float) rounding (epdf_width is float,
# pdftoepdf.cc:770) differs, so that bp2int (writeimg.c:25,320) gives different scaled image widths.
import math, random, struct, decimal, sys
decimal.getcontext().prec = 60
sys.path.insert(0, sys.argv[0].rsplit('/', 1)[0])
from lexsim import parse, f32, bp2int
random.seed(7); hits = []
for trial in range(20000):
    fl = f32(random.uniform(10, 2000))
    nxt = struct.unpack('f', struct.pack('I', struct.unpack('I', struct.pack('f', fl))[0] + 1))[0]
    mid = (decimal.Decimal(fl) + decimal.Decimal(nxt)) / 2          # float rounding midpoint, exact
    for nd in range(8, 26):
        q = mid.quantize(decimal.Decimal(1).scaleb(-nd))
        for k in range(-3, 4):
            s = str(q + k * decimal.Decimal(1).scaleb(-nd))
            a, b = parse(s, True), parse(s, False)
            if a != b and f32(a) != f32(b):
                hits.append((s, f32(a), f32(b), bp2int(f32(a)), bp2int(f32(b))))
    if len(hits) >= 5: break
print(f"float midpoints tried: {trial + 1}; numerals whose scaled width differs: {len(hits)}"); [print(h) for h in hits[:5]]
