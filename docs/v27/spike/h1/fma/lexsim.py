# Simulate xpdf Lexer.cc real parsing (lines 157-221) fused (aarch64 fmadd) vs unfused (x86_64),
# then pdftoepdf.cc epdf_width = (float)(x2 - x1) and writeimg.c bp2int = round(p*(onehundredbp/100.0)).
import math, random, struct, sys
f32 = lambda x: struct.unpack('f', struct.pack('f', x))[0]
def parse(s, fused):
    ip, _, fp = s.partition('.')
    xf = 0.0
    for c in ip:
        d = ord(c) - 48
        xf = math.fma(xf, 10.0, d) if fused else xf * 10 + d
    scale = 0.1
    for c in fp:
        d = ord(c) - 48
        xf = math.fma(scale, d, xf) if fused else xf + scale * d
        scale *= 0.1
    return xf
ONEHUNDREDBP = 6578176
def bp2int(p): 
    v = p * (ONEHUNDREDBP / 100.0)
    return math.floor(v + 0.5) if v >= 0 else -math.floor(-v + 0.5)  # C round(): half away from zero
if __name__ == '__main__':
    random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 200000
    dd = df = di = 0; ex = []
    for _ in range(N):
        nd = random.randint(1, 6)
        s = f"{random.randint(0, 2000)}.{random.randint(0, 10**nd - 1):0{nd}d}"
        a, b = parse(s, True), parse(s, False)
        if a != b:
            dd += 1
            fa, fb = f32(a), f32(b)
            if fa != fb:
                df += 1
                if bp2int(fa) != bp2int(fb):
                    di += 1; ex.append(s)
                elif len(ex) < 5: ex.append('f32-only:' + s)
    print(f"N={N} double-differs={dd} float-differs={df} scaled-differs={di} examples={ex[:8]}")
