#!/usr/bin/env python3
"""Decode a decompressed pdfTeX format stream completely, and encode it back.

usage: fmtdecode.py check FILE...      decode, re-encode, require the same bytes; print a summary
       (as a module: decode(bytes) -> Fmt, encode(Fmt) -> bytes)

The layout is store_fmt_file of the tangled pdftex.p of r78081 (the H.1 rebuild,
Work/texk/web2c/pdftex.p, procedure storefmtfile; tex.web §1299ff with tex.ch, etex.ch,
pdftex.web's additions: e-TeX's sa_root, MLTeX and encTeX headers, the font arrays, pdfTeX's
pdf_mem, obj_tab, head_tab, image meta and the ToUnicode tree), and the C types of the
generated pdftexd.h and texmfmem.h on a little-endian host:
  dumpint                  4 bytes, big-endian (do_dump swaps every item on a little-endian host)
  memoryword (mem, eqtb)   8 bytes: the 64-bit little-endian union, byte-reversed; so the file
                           holds RH (bytes 0-3) then LH (bytes 4-7), each big-endian; B0, B1 are
                           LH's high and low 16 bits; .int (CINT) is RH; qqqq B0..B3 are RH's bytes
  twohalves (prim, hash)   8 bytes, as a memoryword's hh
  fmemoryword (font_info)  4 bytes: CINT big-endian; qqqq B0..B3 in file order
  fourquarters             4 bytes, B0..B3 in file order
  ASCIIcode, packedASCIIcode, eightbits, smallnumber, quarterword: 1 byte
  ninebits (short), trieopcode (unsigned short): 2 bytes
  integer, halfword, scaled, strnumber, poolpointer, fontindex, triepointer: 4 bytes
Every byte of the stream is assigned to exactly one field (Fmt.fields: name, offset, length);
`encode` rebuilds the stream from the decoded state with store_fmt_file's own algorithms (the
eqtb run-length rule, the rover ring walk, the sparse hash rule), so decode followed by encode
being the identity is the check that no byte is unaccounted for."""
import hashlib
import struct
import sys

MAGIC, POOLCHK, MAGIC3, MLTEX, ENCTEX, END = 1462916184, 312141437, 268435455, 1296847960, 1162040408, 69069
EQTB_SIZE, HASH_PRIME, HYPH_PRIME = 30192, 8501, 607
INT_BASE = 29277               # eqtb's region 5 (integers) starts here: the first loop's bound
HASH_BASE, UNDEF_CS = 514, 26627   # hash_base; undefined_control_sequence (hash's dense part ends below it)
EQTB_EXTRA = 30193             # eqtb_size + 1: the hash_extra region of eqtb and hash
PRIM_SIZE = 2101
NULL = -268435455              # min_halfword: null


class Fmt:
    pass


class Reader:
    def __init__(self, d):
        self.d, self.o, self.fields = d, 0, []

    def take(self, name, n):
        if self.o + n > len(self.d):
            raise ValueError(f"short stream at {name}: need {n} at {self.o}, have {len(self.d) - self.o}")
        b = self.d[self.o:self.o + n]
        self.fields.append((name, self.o, n))
        self.o += n
        return b

    def int(self, name):
        return struct.unpack(">i", self.take(name, 4))[0]

    def ints(self, name, n):
        return list(struct.unpack(">%di" % n, self.take(name, 4 * n))) if n else []

    def words(self, name, n):          # memoryword / twohalves: (rh, lh) signed
        b = self.take(name, 8 * n)
        v = struct.unpack(">%di" % (2 * n), b) if n else ()
        return [(v[2 * i], v[2 * i + 1]) for i in range(n)]

    def u8s(self, name, n):
        return list(self.take(name, n))

    def s16s(self, name, n):
        return list(struct.unpack(">%dh" % n, self.take(name, 2 * n))) if n else []

    def u16s(self, name, n):
        return list(struct.unpack(">%dH" % n, self.take(name, 2 * n))) if n else []


def b0(w):
    return (w[1] >> 16) & 0xFFFF


def b1(w):
    return w[1] & 0xFFFF


FONT_ARRAYS = [("fontcheck", "u32"), ("fontsize", "i"), ("fontdsize", "i"), ("fontparams", "i"),
               ("hyphenchar", "i"), ("skewchar", "i"), ("fontname", "i"), ("fontarea", "i"),
               ("fontbc", "u8"), ("fontec", "u8"), ("charbase", "i"), ("widthbase", "i"),
               ("heightbase", "i"), ("depthbase", "i"), ("italicbase", "i"), ("ligkernbase", "i"),
               ("kernbase", "i"), ("extenbase", "i"), ("parambase", "i"), ("fontglue", "i"),
               ("bcharlabel", "i"), ("fontbchar", "s16"), ("fontfalsebchar", "s16")]


def decode(d: bytes) -> Fmt:
    r, f = Reader(d), Fmt()
    # §1485 the header
    if r.int("header.magic") != MAGIC:
        raise ValueError("not a format (magic)")
    x = r.int("header.engine_len")
    f.engine = r.take("header.engine", x)
    assert r.int("header.pool_checksum") == POOLCHK
    f.xord, f.xchr, f.xprn = r.u8s("header.xord", 256), r.u8s("header.xchr", 256), r.u8s("header.xprn", 256)
    assert r.int("header.magic3") == MAGIC3
    f.hashhigh = r.int("header.hash_high")
    f.etex_mode = r.int("header.eTeX_mode")
    f.membot, f.memtop = r.int("header.mem_bot"), r.int("header.mem_top")
    assert (r.int("header.eqtb_size"), r.int("header.hash_prime"), r.int("header.hyph_prime")) == (
        EQTB_SIZE, HASH_PRIME, HYPH_PRIME)
    assert r.int("header.mltex_magic") == MLTEX
    f.mltex = r.int("header.mltex")
    assert r.int("header.enctex_magic") == ENCTEX
    f.enctex = r.int("header.enctex")
    if f.enctex:
        raise ValueError("encTeX tables present: not decoded")
    # §1487 the string pool
    f.poolptr, f.strptr = r.int("pool.pool_ptr"), r.int("pool.str_ptr")
    f.strstart = r.ints("pool.str_start", f.strptr + 1)
    f.strpool = r.take("pool.str_pool", f.poolptr)
    # §1489 the dynamic memory
    f.lomemmax, f.rover = r.int("mem.lo_mem_max"), r.int("mem.rover")
    f.saroot = r.ints("mem.sa_root", 6) if f.etex_mode == 1 else []
    f.mem = {}
    f.chunks = []                    # (first address, words) of each dumped lo-mem run
    p, q = f.membot, f.rover
    while True:
        ws = r.words("mem.lo[%d..%d]" % (p, q + 1), q + 2 - p)
        for i, w in enumerate(ws):
            f.mem[p + i] = w
        f.chunks.append((p, q + 2 - p))
        p, q = q + f.mem[q][1], f.mem[q + 1][0]       # node_size(q) = mem[q].lh; rlink(q) = mem[q+1].rh
        if q == f.rover:
            break
    ws = r.words("mem.lo[%d..%d]" % (p, f.lomemmax), f.lomemmax + 1 - p)
    for i, w in enumerate(ws):
        f.mem[p + i] = w
    f.chunks.append((p, f.lomemmax + 1 - p))
    f.himemmin, f.avail = r.int("mem.hi_mem_min"), r.int("mem.avail")
    ws = r.words("mem.hi[%d..%d]" % (f.himemmin, f.memtop), f.memtop + 1 - f.himemmin)
    for i, w in enumerate(ws):
        f.mem[f.himemmin + i] = w
    f.varused, f.dynused = r.int("mem.var_used"), r.int("mem.dyn_used")
    # §1495 eqtb, as the loader reads it: runs of explicit words, then copies of the last one
    f.eqtb = [None] * (EQTB_SIZE + 1)
    f.eqtb_runs = []
    k = 1
    while True:
        x = r.int("eqtb.explicit_count@%d" % k)
        ws = r.words("eqtb[%d..%d]" % (k, k + x - 1), x)
        for i, w in enumerate(ws):
            f.eqtb[k + i] = w
        k += x
        y = r.int("eqtb.copies@%d" % k)
        for j in range(k, k + y):
            f.eqtb[j] = f.eqtb[k - 1]
        f.eqtb_runs.append((x, y))
        k += y
        if k > EQTB_SIZE:
            break
    f.eqtb_extra = r.words("eqtb.extra[%d..]" % EQTB_EXTRA, f.hashhigh) if f.hashhigh > 0 else []
    f.parloc, f.writeloc = r.int("eqtb.par_loc"), r.int("eqtb.write_loc")
    # §1497 the hash
    f.prim = r.words("hash.prim", PRIM_SIZE)
    f.hashused = r.int("hash.hash_used")
    f.hash = {}
    f.hash_sparse = []
    p = HASH_BASE - 1
    while p != f.hashused:
        p = r.int("hash.sparse_index")
        f.hash[p] = r.words("hash[%d]" % p, 1)[0]
        f.hash_sparse.append(p)
    for p in range(HASH_BASE, f.hashused + 1):          # the loader's zero initialisation of the rest
        f.hash.setdefault(p, (0, 0))
    for i, w in enumerate(r.words("hash[%d..%d]" % (f.hashused + 1, UNDEF_CS - 1), UNDEF_CS - 1 - f.hashused)):
        f.hash[f.hashused + 1 + i] = w
    for i, w in enumerate(r.words("hash.extra[%d..]" % EQTB_EXTRA, f.hashhigh) if f.hashhigh > 0 else []):
        f.hash[EQTB_EXTRA + i] = w
    f.cscount = r.int("hash.cs_count")
    # §1499 font info
    f.fmemptr = r.int("font.fmem_ptr")
    f.fontinfo = r.ints("font.font_info", f.fmemptr)
    f.fontptr = r.int("font.font_ptr")
    f.font = {}
    n = f.fontptr + 1
    for name, t in FONT_ARRAYS:
        if t == "u8":
            f.font[name] = r.u8s("font." + name, n)
        elif t == "s16":
            f.font[name] = r.s16s("font." + name, n)
        elif t == "u32":
            f.font[name] = [v & 0xFFFFFFFF for v in r.ints("font." + name, n)]
        else:
            f.font[name] = r.ints("font." + name, n)
    # §1503 hyphenation exceptions and the trie
    f.hyphcount, f.hyphnext = r.int("hyph.hyph_count"), r.int("hyph.hyph_next")
    f.hyph = []
    for _ in range(f.hyphcount):
        f.hyph.append(tuple(r.ints("hyph.entry", 3)))     # (k + 65536*hyph_link[k], hyph_word[k], hyph_list[k])
    f.triemax, f.hyphstart = r.int("trie.trie_max"), r.int("trie.hyph_start")
    f.trietrl = r.ints("trie.trie_trl", f.triemax + 1)
    f.trietro = r.ints("trie.trie_tro", f.triemax + 1)
    f.trietrc = r.u8s("trie.trie_trc", f.triemax + 1)
    f.trieopptr = r.int("trie.trie_op_ptr")
    f.hyfdistance = r.u8s("trie.hyf_distance", f.trieopptr)
    f.hyfnum = r.u8s("trie.hyf_num", f.trieopptr)
    f.hyfnext = r.u16s("trie.hyf_next", f.trieopptr)
    f.trieused = []
    j = f.trieopptr
    while j > 0:
        k, x = r.ints("trie.trie_used", 2)
        f.trieused.append((k, x))
        j -= x
    assert j == 0
    # §1505 pdfTeX: image meta (writeimg.c), pdf_mem, obj_tab, counters, the ToUnicode tree
    f.image_limit, f.cur_image = r.int("pdf.image_limit"), r.int("pdf.cur_image")
    if f.cur_image != 0:
        raise ValueError("a format with images: not decoded")
    f.pdfmemsize, f.pdfmemptr = r.int("pdf.pdf_mem_size"), r.int("pdf.pdf_mem_ptr")
    f.pdfmem = r.ints("pdf.pdf_mem", f.pdfmemptr - 1) if f.pdfmemptr > 1 else []
    f.objtabsize, f.objptr, f.sysobjptr = r.int("pdf.obj_tab_size"), r.int("pdf.obj_ptr"), r.int("pdf.sys_obj_ptr")
    f.objtab = [tuple(r.ints("pdf.obj_tab", 4)) for _ in range(f.sysobjptr)]
    f.pdfcounts = r.ints("pdf.counters", 9)   # obj, xform, ximage counts; head_tab[7..9]; last obj, xform, ximage
    f.tounicode_count = r.int("pdf.tounicode_count")
    f.tounicode = []
    for _ in range(f.tounicode_count):
        x = r.int("pdf.tounicode.name_len")
        name = r.take("pdf.tounicode.name", x)
        code = r.int("pdf.tounicode.code")
        seq = None
        if code == -2:
            y = r.int("pdf.tounicode.seq_len")
            seq = r.take("pdf.tounicode.seq", y)
        f.tounicode.append((name, code, seq))
    # §1506 the trailer
    f.interaction, f.formatident = r.int("end.interaction"), r.int("end.format_ident")
    assert r.int("end.magic") == END
    if r.o != len(d):
        raise ValueError(f"{len(d) - r.o} bytes after the trailer")
    f.fields = r.fields
    f.size = len(d)
    return f


def string(f, s):
    return f.strpool[f.strstart[s]:f.strstart[s + 1]]


def elements(f: Fmt):
    """store_fmt_file, from the decoded state: the stream as a list of (key, bytes) in stream
    order. A key names WHAT a piece of the stream holds (a header field, str_start[i], pool
    byte i, mem[a], eqtb[k], a run header of the eqtb compression starting at k, hash[p], ...),
    independently of WHERE it lands, so two streams can be compared element by element."""
    out = []
    P = lambda key, b: out.append((key, b))
    I = lambda key, v: P(key, struct.pack(">i", v))
    W = lambda key, w: P(key, struct.pack(">ii", w[0], w[1]))
    I(("header", "magic"), MAGIC); I(("header", "engine_len"), len(f.engine)); P(("header", "engine"), f.engine)
    I(("header", "pool_checksum"), POOLCHK)
    P(("header", "xord"), bytes(f.xord)); P(("header", "xchr"), bytes(f.xchr)); P(("header", "xprn"), bytes(f.xprn))
    for k, v in (("magic3", MAGIC3), ("hash_high", f.hashhigh), ("eTeX_mode", f.etex_mode), ("mem_bot", f.membot),
                 ("mem_top", f.memtop), ("eqtb_size", EQTB_SIZE), ("hash_prime", HASH_PRIME),
                 ("hyph_prime", HYPH_PRIME), ("mltex_magic", MLTEX), ("mltex_flag", f.mltex),
                 ("enctex_magic", ENCTEX), ("enctex_flag", f.enctex), ("pool_ptr", f.poolptr), ("str_ptr", f.strptr)):
        I(("header", k), v)
    for i, v in enumerate(f.strstart):
        I(("str_start", i), v)
    for i, c in enumerate(f.strpool):
        P(("pool", i), bytes([c]))
    I(("mem", "lo_mem_max"), f.lomemmax); I(("mem", "rover"), f.rover)
    for i, v in enumerate(f.saroot):
        I(("mem", "sa_root", i), v)
    p, q = f.membot, f.rover
    while True:                                          # §1311's repeat ... until q = rover
        for a in range(p, q + 2):
            W(("mem", a), f.mem[a])
        p, q = q + f.mem[q][1], f.mem[q + 1][0]
        if q == f.rover:
            break
    for a in range(p, f.lomemmax + 1):
        W(("mem", a), f.mem[a])
    I(("mem", "hi_mem_min"), f.himemmin); I(("mem", "avail"), f.avail)
    for a in range(f.himemmin, f.memtop + 1):
        W(("mem", a), f.mem[a])
    I(("mem", "var_used"), f.varused); I(("mem", "dyn_used"), f.dynused)
    e = f.eqtb

    def run(k, l, j):
        I(("eqtb_run", "explicit", k), l - k)
        for i in range(k, l):
            W(("eqtb", i), e[i])
        I(("eqtb_run", "copies", l), j + 1 - l)
    # §1493: regions 1-4, two words equal when rh, b0 and b1 are (all 8 bytes)
    k = 1
    while True:
        j, found = k, False
        while j < INT_BASE - 1:
            if e[j] == e[j + 1]:
                found = True
                break
            j += 1
        if not found:
            l = INT_BASE
        else:
            j += 1
            l = j
            while j < INT_BASE - 1:
                if e[j] != e[j + 1]:
                    break
                j += 1
        run(k, l, j)
        k = j + 1
        if k == INT_BASE:
            break
    # §1494: regions 5-6, two words equal when .int (rh) is
    while True:
        j, found = k, False
        while j < EQTB_SIZE:
            if e[j][0] == e[j + 1][0]:
                found = True
                break
            j += 1
        if not found:
            l = EQTB_SIZE + 1
        else:
            j += 1
            l = j
            while j < EQTB_SIZE:
                if e[j][0] != e[j + 1][0]:
                    break
                j += 1
        run(k, l, j)
        k = j + 1
        if k > EQTB_SIZE:
            break
    for i, w in enumerate(f.eqtb_extra):
        W(("eqtb", EQTB_EXTRA + i), w)
    I(("eqtb", "par_loc"), f.parloc); I(("eqtb", "write_loc"), f.writeloc)
    for i, w in enumerate(f.prim):
        W(("prim", i), w)
    I(("hash", "hash_used"), f.hashused)
    for p in range(HASH_BASE, f.hashused + 1):          # §1318: the entries with text(p) <> 0
        if f.hash[p][0] != 0:
            I(("hash_index", p), p); W(("hash", p), f.hash[p])
    for p in range(f.hashused + 1, UNDEF_CS):
        W(("hash", p), f.hash[p])
    for p in range(EQTB_EXTRA, EQTB_EXTRA + f.hashhigh):
        W(("hash", p), f.hash[p])
    I(("hash", "cs_count"), f.cscount)
    I(("font", "fmem_ptr"), f.fmemptr)
    for i, v in enumerate(f.fontinfo):
        I(("font_info", i), v)
    I(("font", "font_ptr"), f.fontptr)
    for name, t in FONT_ARRAYS:
        for i, v in enumerate(f.font[name]):
            P(("font", name, i), bytes([v]) if t == "u8" else struct.pack(">h", v) if t == "s16"
              else struct.pack(">I", v) if t == "u32" else struct.pack(">i", v))
    I(("hyph", "hyph_count"), f.hyphcount); I(("hyph", "hyph_next"), f.hyphnext)
    for t in f.hyph:
        P(("hyph", t[0] % 65536), struct.pack(">3i", *t))
    I(("trie", "trie_max"), f.triemax); I(("trie", "hyph_start"), f.hyphstart)
    for i, v in enumerate(f.trietrl):
        I(("trie_trl", i), v)
    for i, v in enumerate(f.trietro):
        I(("trie_tro", i), v)
    for i, v in enumerate(f.trietrc):
        P(("trie_trc", i), bytes([v]))
    I(("trie", "trie_op_ptr"), f.trieopptr)
    for i, v in enumerate(f.hyfdistance):
        P(("hyf_distance", i + 1), bytes([v]))
    for i, v in enumerate(f.hyfnum):
        P(("hyf_num", i + 1), bytes([v]))
    for i, v in enumerate(f.hyfnext):
        P(("hyf_next", i + 1), struct.pack(">H", v))
    for k, x in f.trieused:
        P(("trie_used", k), struct.pack(">2i", k, x))
    I(("pdf", "image_limit"), f.image_limit); I(("pdf", "cur_image"), f.cur_image)
    I(("pdf", "pdf_mem_size"), f.pdfmemsize); I(("pdf", "pdf_mem_ptr"), f.pdfmemptr)
    for i, v in enumerate(f.pdfmem):
        I(("pdf_mem", i + 1), v)
    I(("pdf", "obj_tab_size"), f.objtabsize); I(("pdf", "obj_ptr"), f.objptr); I(("pdf", "sys_obj_ptr"), f.sysobjptr)
    for i, t in enumerate(f.objtab):
        P(("obj_tab", i + 1), struct.pack(">4i", *t))
    for i, v in enumerate(f.pdfcounts):
        I(("pdf", "counter", i), v)
    I(("pdf", "tounicode_count"), f.tounicode_count)
    for name, code, seq in f.tounicode:
        b = struct.pack(">i", len(name)) + name + struct.pack(">i", code)
        if code == -2:
            b += struct.pack(">i", len(seq)) + seq
        P(("tounicode", name), b)
    I(("end", "interaction"), f.interaction); I(("end", "format_ident"), f.formatident); I(("end", "magic"), END)
    return out


def encode(f: Fmt) -> bytes:
    """store_fmt_file, from the decoded state."""
    return b"".join(b for _, b in elements(f))


def check(path):
    d = open(path, "rb").read()
    f = decode(d)
    cover = sum(n for _, _, n in f.fields)
    same = encode(f) == d
    print(f"{path}: {len(d)} bytes, sha256 {hashlib.sha256(d).hexdigest()[:16]}, {len(f.fields)} fields cover "
          f"{cover} bytes, re-encoded identical: {same}; strings {f.strptr}, mem words {len(f.mem)}, "
          f"hash_used {f.hashused}, hash_high {f.hashhigh}, fonts {f.fontptr + 1}, font_info {f.fmemptr}, "
          f"hyph {f.hyphcount}, trie_max {f.triemax}, trie ops {f.trieopptr}, tounicode {f.tounicode_count}, "
          f"format_ident {string(f, f.formatident)!r}")
    return same and cover == len(d)


if __name__ == "__main__":
    if len(sys.argv) < 3 or sys.argv[1] != "check":
        sys.exit(__doc__)
    sys.exit(0 if all([check(p) for p in sys.argv[2:]]) else 1)
