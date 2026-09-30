"""Name resolution, C typing and storage layout: web2c's Pascal -> the PS IR.

What web2c's C MEANS is decided here, from web2c's own rules (cited per rule),
so that the Coq interpreter (PS) is a small, uniform machine:

* C types of Pascal types (web2c-parser.y, SIMPLE_TYPE): a subrange with two
  numeric bounds is `unsigned char` if within 0..255, else `schar` if within
  -128..127, else `short` if within -32768..32767, else `unsigned short` if
  within 0..65535, else `integer`; a subrange with a symbolic bound is
  `integer`. `integer` is C int (32 bits, H.1 report §2), `longinteger` is
  off_t (64 bits), `boolean` is int (kpathsea/simpletypes.h), `real` and
  `glueratio` are double.
* Integer literals (web2c-parser.y, CONSTANT): |n| > 32767 gets the suffix L,
  so it is a C long (64 bits on both targets); otherwise int. A constant
  identifier is web2c's #define of its value, so it has its value's type.
* Expression types are C's usual arithmetic conversions over int, long (int64)
  and double. Operands narrower than int are promoted to int.
* Memory words (texmfmem.h, little-endian, non-SMALL TeX): an 8-byte union;
  hh.v.LH at bytes 0..3, hh.v.RH at 4..7, hh.u.B1 (short) at 0..1, hh.u.B0
  (short) at 2..3, cint at 4..7, qqqq.B3/B2/B1/B0 (unsigned char) at 4/5/6/7,
  gr (double) at 0..7. twohalves: LH 0..3, RH 4..7, B1 0..1, B0 2..3.
  fourquarters: B3 0, B2 1, B1 2, B0 3. fmemoryword (4 bytes): cint 0..3,
  qqqq at 0..3.

IR (tuples), consumed by emit_coq.py:
  lexp : ('glob', g) | ('loc', k) | ('ref', k)       whole variable; ref = by-reference param
         | ('idx', lexp, expr, lo, hi, esize)         static array element
         | ('pidx', expr, expr, esize)                pointer + index (C pointer arithmetic)
         | ('fld', lexp, off)                         record field
         | ('sl', lexp, slice)                        union-word field, slice = (byteoff, nbytes, kind)
  expr : ('int', ty, z) | ('dbl', text) | ('str', text) | ('null',)
         | ('load', ty, lexp)                         read a scalar, promoted to ty
         | ('un', op, ty, e) | ('bin', op, ty, e1, e2) | ('cmp', op, ty, e1, e2)
         | ('and', e1, e2) | ('or', e1, e2) | ('not', e)
         | ('conv', ty, e)                            C conversion between arithmetic types
         | ('call', fid, [arg]) | ('ext', name, [arg]) | ('addr', lexp)
  arg  : ('val', e) | ('ref', lexp) | ('word', lexp)   (word/record/array by value = copy)
  stmt : ('skip',) | ('asg', lexp, ct, e) | ('copy', lexp, lexp, ncells)
         | ('pcall', pid, [arg]) | ('ext', name, [arg]) | ('seq', [stmt]) | ('label', n)
         | ('if', e, s1, s2) | ('while', e, s) | ('repeat', s, e)
         | ('for', lexp, ct, up, e1, e2, s) | ('case', e, [([z], s)], dflt|None)
         | ('goto', n) | ('incr', lexp, ct, delta) | ('write', file_e, [witem], nl)
  ty   : 'i32' | 'i64' | 'f64' | 'ptr' | 'cstr' | 'file'
  ct   : the C storage type of a location: 'u8','s8','s16','u16','i32','i64','f64','ptr','cstr','file'
"""
import sys

INT_MIN, INT_MAX = -2 ** 31, 2 ** 31 - 1


class TranslateError(Exception):
    pass


# ---------------------------------------------------------------------------
# types
class T:
    """A resolved type. kind: 'scalar' (ct, lo, hi, isbool) | 'real' | 'ptr' (target) |
    'array' (dims [(lo,hi)], elem) | 'record' (fields {name: (off, type)}) |
    'word' (wk in mw/th/fq/fmw) | 'file' | 'cstr' | 'opaque' (name)"""
    __slots__ = ("kind", "ct", "lo", "hi", "isbool", "target", "dims", "elem", "fields", "wk", "name", "size")

    def __init__(self, kind, **kw):
        self.kind = kind
        for s in self.__slots__[1:]:
            setattr(self, s, kw.get(s))
        if self.size is None:
            self.size = 1

    def __repr__(self):
        return f"T({self.kind},{self.ct},{self.lo},{self.hi},{self.wk},{self.name})"


def web2c_ct(lo, hi, symbolic):
    if symbolic:
        return "i32"
    if 0 <= lo and hi <= 255:
        return "u8"
    if -128 <= lo and hi <= 127:
        return "s8"
    if -32768 <= lo and hi <= 32767:
        return "s16"
    if 0 <= lo and hi <= 65535:
        return "u16"
    return "i32"


def lit_ty(z):
    return "i64" if abs(z) > 32767 else "i32"


PROMOTE = {"w8": "w8", "w4": "w4", "c8": "i32", "u8": "i32", "s8": "i32", "s16": "i32", "u16": "i32", "i32": "i32", "i64": "i64", "f64": "f64",
           "ptr": "ptr", "cstr": "cstr", "file": "file"}


def arith(t1, t2):
    if "f64" in (t1, t2):
        return "f64"
    if "i64" in (t1, t2):
        return "i64"
    if t1 == t2 == "i32":
        return "i32"
    raise TranslateError(f"no arithmetic conversion for {t1}, {t2}")


# memory-word slices: (byte offset, nbytes, kind) kind: 's'=signed int, 'u'=unsigned, 'f'=double,
# 'w'=a sub-word value (copied as bytes)
SLICES = {
    ("mw", "hh"): (0, 8, "w", "th"), ("mw", "int"): (4, 4, "s", None), ("mw", "sc"): (4, 4, "s", None),
    ("mw", "gr"): (0, 8, "f", None), ("mw", "qqqq"): (4, 4, "w", "fq"),
    ("th", "lh"): (0, 4, "s", None), ("th", "rh"): (4, 4, "s", None),
    ("th", "b0"): (2, 2, "s", None), ("th", "b1"): (0, 2, "s", None),
    ("fq", "b3"): (0, 1, "u", None), ("fq", "b2"): (1, 1, "u", None),
    ("fq", "b1"): (2, 1, "u", None), ("fq", "b0"): (3, 1, "u", None),
    ("fmw", "int"): (0, 4, "s", None), ("fmw", "qqqq"): (0, 4, "w", "fq"),
}
SLICE_CT = {("s", 4): "i32", ("s", 2): "s16", ("u", 1): "u8", ("f", 8): "f64"}
WORD_BYTES = {"mw": 8, "th": 8, "fq": 4, "fmw": 4}


class Lowerer:
    def __init__(self, P, ext_consts=None):
        self.P = P
        self.defines = {n: (k, a) for k, n, a in P["defines"]}
        self.consts = {}      # name -> (z, ty) | ('str', text)
        self.types = {}
        self.globals = {}     # name -> (gid, T)
        self.procs = {}       # name -> dict
        self.exts = {}        # name -> id
        self.issues = []      # (severity, where, text)
        self.stats = {"expr_nodes": 0, "stmt_nodes": 0}
        self.where = ""
        self._builtin_types()
        self._consts()
        self._types()
        self._globals()
        self._procsigs()

    # -- declarations ---------------------------------------------------------
    def _builtin_types(self):
        I = lambda ct, lo, hi, b=False: T("scalar", ct=ct, lo=lo, hi=hi, isbool=b)
        self.types.update({
            "integer": I("i32", INT_MIN, INT_MAX), "cinttype": I("i32", INT_MIN, INT_MAX),
            "longinteger": I("i64", -2 ** 63, 2 ** 63 - 1), "integer64": I("i64", -2 ** 63, 2 ** 63 - 1),
            "boolean": I("i32", 0, 1, True), "real": T("real"), "glueratio": T("real"),
            "memoryword": T("word", wk="mw"), "twohalves": T("word", wk="th"),
            "fourquarters": T("word", wk="fq"), "fmemoryword": T("word", wk="fmw"),
            "gzFile": T("file", name="gz"),
            # plain C `char` (common.defines: @define type char = 0..255): signed on x86_64,
            # unsigned on aarch64 (H.1 report §5.4); ct 'c8', whose load PS parameterises
            "char": T("scalar", ct="c8", lo=0, hi=255, isbool=False),
        })
        # cpascal.h: cstring = string = char *, constcstring = const_string = const char *
        self.types["cstring"] = T("ptr", target=self.types["char"])
        self.types["constcstring"] = T("ptr", target=self.types["char"])

    def cval(self, e):
        """Evaluate a constant expression (web2c CONSTANT_EXPRESS)."""
        if e[0] == "num":
            return e[1]
        if e[0] == "id":
            v = self.consts.get(e[1])
            if v is None or v[0] == "str":
                raise TranslateError(f"not a numeric constant: {e[1]}")
            return v[0]
        if e[0] == "bin":
            a, b = self.cval(e[2]), self.cval(e[3])
            return {"+": a + b, "-": a - b, "*": a * b}[e[1]]
        if e[0] == "paren":
            return self.cval(e[1])
        raise TranslateError(f"constant expression {e}")

    def _consts(self):
        self.consts["true"] = (1, "i32")
        self.consts["false"] = (0, "i32")
        self.consts["maxint"] = (INT_MAX, "i32")  # cpascal.h: maxint INTEGER_MAX
        for n, e in self.P["consts"]:
            if e[0] == "id" and e[1] not in self.consts:
                self.consts[n] = ("ext", e[1])   # a C macro from the build (TEXMFPOOLNAME, ...)
                continue
            z = self.cval(e)
            self.consts[n] = (z, lit_ty(z))

    def rtype(self, t):
        k = t[0]
        if k == "named":
            n = t[1]
            if n in self.types:
                return self.types[n]
            if n in ("alphafile", "bytefile"):
                return T("file", name=n)
            raise TranslateError(f"unknown type {n}")
        if k == "subrange":
            sym = t[1][0] == "id" or t[2][0] == "id"
            lo = self.bound(t[1])
            hi = self.bound(t[2])
            return T("scalar", ct=web2c_ct(lo, hi, sym), lo=lo, hi=hi, isbool=False)
        if k == "ptr":
            return T("ptr", target=self.rtype(t[1]))
        if k == "file":
            return T("file", name="file")
        if k == "array":
            dims = []
            for it in t[1]:
                r = self.rtype(it)
                if r.kind != "scalar":
                    raise TranslateError(f"array index type {it}")
                dims.append((r.lo, r.hi))
            el = self.rtype(t[2])
            n = 1
            for lo, hi in dims:
                n *= hi - lo + 1
            return T("array", dims=dims, elem=el, size=n * el.size)
        if k == "record":
            fields, off = {}, 0
            for fn, ft in t[1]:
                r = self.rtype(ft)
                fields[fn] = (off, r)
                off += r.size
            return T("record", fields=fields, size=off)
        raise TranslateError(f"type {t}")

    def bound(self, b):
        if b[0] == "num":
            return b[1]
        n = b[1]
        if n in self.consts and self.consts[n][0] != "ext":
            return self.consts[n][0]
        # a variable bound (web2c allows var_id_tok): the C type is integer, and the
        # array has no static size; only used in types of pointer targets / subranges
        return None

    def _types(self):
        for n, t in self.P["types"]:
            if n == "alphafile" or n == "bytefile":
                self.types[n] = T("file", name=n)
                continue
            r = self.rtype(t)
            if r.kind == "scalar" and (r.lo is None or r.hi is None):
                r = T("scalar", ct="i32", lo=INT_MIN, hi=INT_MAX, isbool=False)
            self.types[n] = r

    def _globals(self):
        for gid, (n, t) in enumerate(self.P["vars"]):
            r = self.rtype(t)
            if r.kind == "scalar" and (r.lo is None or r.hi is None):
                r = T("scalar", ct="i32", lo=INT_MIN, hi=INT_MAX, isbool=False)
            self.globals[n] = (gid, r)
        # web2c texmf.defines: `mem` and `eqtb` are C globals (pointers into the
        # dynamically allocated arrays); TeX Live's change files assign them
        # C globals the program names through texmf.defines / common.defines (`@define var`),
        # with their C types from texmfmp.h, cpascal.h and kpathsea: part of the boundary,
        # initialised by the C main program before mainbody runs
        I32 = T("scalar", ct="i32", lo=INT_MIN, hi=INT_MAX, isbool=False)
        CSTR = self.types["cstring"]
        EXTG = [("mem", T("ptr", target=self.types["memoryword"])),
                ("eqtb", T("ptr", target=self.types["memoryword"])),
                ("tfmtemp", I32), ("texinputtype", I32),        # texmfmp.h: extern int
                ("kpsemaketexdiscarderrors", I32),               # kpathsea: boolean (int)
                ("translatefilename", CSTR),                     # texmfmp.h: extern string
                ("versionstring", CSTR)]                         # const_string
        base = len(self.globals)
        self.ext_globals = []
        for i, (n, r) in enumerate(EXTG):
            if self.defines.get(n, ("?",))[0] != "var":
                raise TranslateError(f"{n} is not an @define var")
            self.globals[n] = (base + i, r)
            self.ext_globals.append(n)

    def _procsigs(self):
        for pid, p in enumerate(self.P["procs"]):
            params = []
            for n, t, byref in p["params"]:
                params.append((n, self.fix(self.rtype(t)), byref))
            res = self.fix(self.rtype(p["result"])) if p["result"] else None
            self.procs[p["name"]] = {"id": pid, "params": params, "result": res, "ast": p}

    def fix(self, r):
        if r.kind == "scalar" and (r.lo is None or r.hi is None):
            return T("scalar", ct="i32", lo=INT_MIN, hi=INT_MAX, isbool=False)
        return r

    def ext(self, name):
        if name not in self.exts:
            self.exts[name] = len(self.exts)
        return name

    # -- storage types -----------------------------------------------------------
    def ct_of(self, r):
        if r.kind == "scalar":
            return r.ct
        if r.kind == "real":
            return "f64"
        if r.kind == "ptr":
            return "ptr"
        if r.kind == "cstr":
            return "cstr"
        if r.kind == "file":
            return "file"
        if r.kind == "word":  # a union word is one cell, copied as its bytes
            return "w%d" % WORD_BYTES[r.wk]
        return None

    # -- procedures ------------------------------------------------------------------
    def lower_all(self, keep_going=False):
        out, failed = [], []
        for name, info in self.procs.items():
            try:
                out.append(self.lower_proc(name, info))
            except TranslateError as ex:
                if not keep_going:
                    raise
                failed.append((name, str(ex)))
        return out, failed

    def lower_proc(self, name, info):
        p = info["ast"]
        self.where = name
        self.cur = info
        self.locals = {}
        off = 0
        for n, r, byref in info["params"]:
            self.locals[n] = (off, r, "ref" if byref else "loc")
            off += 1 if byref else r.size
        if info["result"] is not None:
            self.locals[name] = (off, info["result"], "loc")
            self.result_off = off
            off += info["result"].size
        else:
            self.result_off = None
        self.lconsts = {}
        for n, e in p["consts"]:
            z = self.cval(e)
            self.lconsts[n] = (z, lit_ty(z))
        for n, t in p["vars"]:
            r = self.fix(self.rtype(t))
            self.locals[n] = (off, r, "loc")
            off += r.size
        body = self.stmt(p["body"])
        layout = [(n, o, self.ct_of(r) or r.kind, r.size, kind) for n, (o, r, kind) in self.locals.items()]
        return {"name": name, "id": info["id"], "nparams": len(info["params"]),
                "params": [(n, "ref" if br else ("val" if r.size == 1 and self.ct_of(r) else "copy"), r.size)
                           for n, r, br in info["params"]],
                "frame": off, "result": (self.result_off, self.ct_of(info["result"])) if info["result"] else None,
                "layout": layout, "body": body, "labels": p["labels"]}

    # -- lvalues -----------------------------------------------------------------------
    def lval(self, e):
        """-> (lexp IR, T)"""
        k = e[0]
        if k == "id":
            n = e[1]
            if n in self.locals:
                off, r, kind = self.locals[n]
                return ((kind, off), r)
            if n in self.globals:
                gid, r = self.globals[n]
                return (("glob", gid), r)
            raise TranslateError(f"{self.where}: not a variable: {n}")
        if k == "idx":
            base, r = self.lval(e[1])
            for ix in e[2]:
                ie, it = self.rexpr(ix)
                if it not in ("i32", "i64"):
                    raise TranslateError(f"{self.where}: non-integer index")
                if r.kind == "array":
                    lo, hi = r.dims[0]
                    rest = r.dims[1:]
                    el = r.elem if not rest else T("array", dims=rest, elem=r.elem,
                                                   size=r.size // (hi - lo + 1))
                    base = ("idx", base, ie, lo, hi, el.size)
                    r = el
                elif r.kind == "ptr":
                    base = ("pidx", ("load", "ptr", base), ie, r.target.size)
                    r = r.target
                else:
                    raise TranslateError(f"{self.where}: indexing a {r.kind}")
            return (base, r)
        if k == "fld":
            base, r = self.lval(e[1])
            f = e[2]
            if r.kind == "record":
                if f not in r.fields:
                    raise TranslateError(f"{self.where}: no field {f}")
                off, fr = r.fields[f]
                return (("fld", base, off), fr)
            if r.kind == "word":
                key = (r.wk, f)
                if key not in SLICES:
                    raise TranslateError(f"{self.where}: no field {f} in {r.wk}")
                boff, nb, sk, sub = SLICES[key]
                if base[0] == "sl":  # nested slice: compose byte offsets
                    b0, n0, k0 = base[2]
                    base = base[1]
                    boff += b0
                if sk == "w":
                    return (("sl", base, (boff, nb, "w")), T("word", wk=sub))
                ct = SLICE_CT[(sk, nb)]
                if sk == "f":
                    return (("sl", base, (boff, nb, "f")), T("real"))
                return (("sl", base, (boff, nb, sk)),
                        T("scalar", ct=ct, lo=None, hi=None, isbool=False))
            raise TranslateError(f"{self.where}: field {f} of a {r.kind}")
        if k == "paren":
            return self.lval(e[1])
        raise TranslateError(f"{self.where}: not an lvalue: {str(e)[:160]}")

    # -- expressions ------------------------------------------------------------------
    def rexpr(self, e):
        """-> (expr IR, ty)"""
        self.stats["expr_nodes"] += 1
        k = e[0]
        if k == "num":
            return (("int", lit_ty(e[1]), e[1]), lit_ty(e[1]))
        if k == "real":
            return (("dbl", e[1]), "f64")
        if k == "char":
            return (("int", "i32", ord(e[1])), "i32")   # a C character constant is an int
        if k == "str":
            return (("str", e[1]), "ptr")   # a C string literal: a pointer to a static char array
        if k == "paren":
            return self.rexpr(e[1])
        if k == "id":
            n = e[1]
            if n in self.lconsts:
                z, t = self.lconsts[n]
                return (("int", t, z), t)
            if n in self.locals or n in self.globals:
                l, r = self.lval(e)
                return self.load(l, r)
            if n in self.consts:
                v = self.consts[n]
                if v[0] == "ext":
                    return (("ext", self.ext(v[1]), []), "cstr")
                return (("int", v[1], v[0]), v[1])
            if n in self.procs:
                return self.fcall(n, [])
            if n == "nil":
                return (("null",), "ptr")
            return self.extcall(n, [])
        if k in ("idx", "fld"):
            l, r = self.lval(e)
            return self.load(l, r)
        if k == "call":
            n = e[1]
            if n in self.procs:
                return self.fcall(n, e[2])
            return self.builtin_or_ext(n, e[2])
        if k == "un":
            op = e[1]
            x, t = self.rexpr(e[2])
            if op == "not":
                return (("not", x), "i32")
            if t not in ("i32", "i64", "f64"):
                raise TranslateError(f"{self.where}: unary {op} on {t}")
            if op == "neg":
                return (("un", "neg", t, x), t)
            return (x, t)
        if k == "bin":
            op = e[1]
            if op in ("and", "or"):
                a, _ = self.rexpr(e[2])
                b, _ = self.rexpr(e[3])
                return ((op, a, b), "i32")
            a, ta = self.rexpr(e[2])
            b, tb = self.rexpr(e[3])
            if op in ("=", "<>", "<", ">", "<=", ">="):
                if ta == tb == "ptr" and op in ("=", "<>"):
                    return (("cmp", op, "ptr", a, b), "i32")
                t = arith(ta, tb)
                return (("cmp", op, t, self.conv(a, ta, t), self.conv(b, tb, t)), "i32")
            if ta == "ptr" and tb in ("i32", "i64") and op in ("+", "-"):
                # C pointer arithmetic, scaled by the target's size in cells
                l, r = self.lval(e[2])
                if r.kind != "ptr":
                    raise TranslateError(f"{self.where}: pointer arithmetic on a non-pointer lvalue")
                return (("padd", a, r.target.size, op, b), "ptr")
            if op == "/":  # web2c: a / ((double) b)
                t = "f64"
                return (("bin", "fdiv", t, self.conv(a, ta, t), self.conv(b, tb, t)), t)
            t = arith(ta, tb)
            if op in ("div", "mod") and t == "f64":
                raise TranslateError(f"{self.where}: {op} on double")
            opn = {"+": "add", "-": "sub", "*": "mul", "div": "div", "mod": "mod"}[op]
            return (("bin", opn, t, self.conv(a, ta, t), self.conv(b, tb, t)), t)
        raise TranslateError(f"{self.where}: expression {k}")

    def conv(self, x, frm, to):
        if frm == to:
            return x
        return ("conv", to, x)

    def load(self, l, r):
        ct = self.ct_of(r)
        if ct is None:
            return (("aggr", l, r.size), "aggr:" + r.kind)
        if ct == "c8":  # plain char: promotion depends on the architecture's signedness
            return (("load", "c8", l), "i32")
        return (("load", PROMOTE[ct], l), PROMOTE[ct])

    def args(self, formals, actuals):
        out = []
        if len(formals) != len(actuals):
            raise TranslateError(f"{self.where}: arity")
        for (n, r, byref), a in zip(formals, actuals):
            if byref:
                l, _ = self.lval(a)
                out.append(("ref", l))
            elif self.ct_of(r) is None:
                l, _ = self.lval(a)
                out.append(("copy", l, r.size))
            else:
                x, t = self.rexpr(a)
                ct = self.ct_of(r)
                out.append(("val", ct, self.conv(x, t, PROMOTE[ct]) if t in ("i32", "i64", "f64") and PROMOTE[ct] in ("i32", "i64", "f64") else x))
        return out

    def fcall(self, n, actuals):
        info = self.procs[n]
        if info["result"] is None:
            raise TranslateError(f"{self.where}: procedure {n} used as a function")
        ct = self.ct_of(info["result"])
        return (("call", info["id"], self.args(info["params"], actuals)), PROMOTE[ct])

    # C macros from cpascal.h / texmfmp.h with a meaning in the translated program, and every
    # other external: a named call into the boundary model. The C types of the results that
    # the program uses arithmetically are stated here (the boundary model must agree).
    EXT_RESULT = {"abs": None, "odd": "i32", "round": "i32", "getc": "i32", "eof": "i32", "feof": "i32",
                  "chr": None, "ord": None, "strlen": "i64", "strcmp": "i32", "inputln": "i32",
                  "xmallocarray": "ptr", "xreallocarray": "ptr", "addressof": "ptr", "stringcast": "cstr",
                  "conststringcast": "cstr", "ucharcast": "i32", "fabs": "f64"}

    def builtin_or_ext(self, n, actuals):
        if n in ("chr", "ord"):  # cpascal.h: chr(x) (x), ord(x) (x)
            return self.rexpr(actuals[0])
        if n == "abs":           # cpascal.h: abs(x) ((integer)(x) >= 0 ? (integer)(x) : (integer)-(x))
            x, t = self.rexpr(actuals[0])
            if t == "f64":
                raise TranslateError(f"{self.where}: abs of a double (cpascal.h casts to integer)")
            return (("abs", self.conv(x, t, "i32") if t != "i32" else x), "i32") if t == "i32" else \
                (("abs", ("conv", "i32", x)), "i32")
        if n == "odd":           # ((x) & 1)
            x, t = self.rexpr(actuals[0])
            return (("odd", t, x), "i32")
        if n == "addressof":
            l, _ = self.lval(actuals[0])
            return (("addr", l), "ptr")
        if n in ("xmallocarray", "xreallocarray"):
            # cpascal.h: ((type*)xmalloc((size+1)*sizeof(type))) -- the type is an argument
            tyarg = actuals[0] if n == "xmallocarray" else actuals[1]
            if tyarg[0] != "id" or tyarg[1] not in self.types:
                raise TranslateError(f"{self.where}: {n} without a type")
            r = self.types[tyarg[1]]
            szx, szt = self.rexpr(actuals[-1])
            if n == "xmallocarray":
                return (("alloc", r.size, self.ct_of(r) or r.kind, szx), "ptr")
            px, _ = self.rexpr(actuals[0])
            return (("realloc", r.size, self.ct_of(r) or r.kind, px, szx), "ptr")
        return self.extcall(n, actuals)

    def extcall(self, n, actuals):
        args = []
        for a in actuals:
            if a[0] == "width":
                raise TranslateError(f"{self.where}: width field outside write")
            if a[0] == "id" and a[1] in self.types and a[1] not in self.globals and a[1] not in self.locals:
                args.append(("type", a[1]))
                continue
            # An external is a C function or a C macro; a macro may take its argument's
            # address (dumpthings, addressof, ...). An argument that is a variable is
            # therefore passed as its location AND its C storage type; the boundary
            # model decides per external whether it reads it or addresses it.
            a0 = a[1] if a[0] == "paren" else a
            if a0[0] in ("idx", "fld") or (a0[0] == "id" and (a0[1] in self.locals or a0[1] in self.globals)):
                l, r = self.lval(a0)
                args.append(("lv", l, self.ct_of(r) or r.kind, r.size))
            else:
                x, t = self.rexpr(a)
                args.append(("val", t, x))
        return (("ext", self.ext(n), args), self.EXT_RESULT.get(n) or "i32")

    # -- statements ---------------------------------------------------------------------
    def doreturn(self, label):
        """web2c-parser.y doreturn(): in TeX mode, label 10 is `return` (goto 10 returns,
        `10:` emits nothing) except in macrocall, hpack, vpackage and trybreak."""
        return label == 10 and self.where not in ("macrocall", "hpack", "vpackage", "trybreak")

    def stmt(self, s):
        self.stats["stmt_nodes"] += 1
        k = s[0]
        if k == "seq":
            # a labelled statement `n: s` is spliced into its statement list as
            # [label n, s], so that a goto finds the label in the list that holds it
            # (Pascal: a label is a position in an enclosing statement sequence)
            out = []
            for x in s[1]:
                while x[0] == "label":
                    if not self.doreturn(x[1]):   # web2c S_LABEL: no C label for a return label
                        out.append(("label", x[1]))
                    x = x[2]
                out.append(self.stmt(x))
            return ("seq", out)
        if k == "empty":
            return ("skip",)
        if k == "label" and self.doreturn(s[1]):
            return self.stmt(s[2])
        if k == "label":
            # a labelled statement outside a statement list (the body of if/while/case):
            # a goto to it from outside is a jump into a structured statement, which
            # Pascal forbids; kept as a one-element sequence and counted
            self.stats["nested_labels"] = self.stats.get("nested_labels", 0) + 1
            return ("seq", [("label", s[1]), self.stmt(s[2])])
        if k == "goto":
            if self.doreturn(s[1]):
                return ("return",)
            return ("goto", s[1])
        if k == "if":
            c, _ = self.rexpr(s[1])
            return ("if", c, self.stmt(s[2]), self.stmt(s[3]) if s[3] else ("skip",))
        if k == "while":
            c, _ = self.rexpr(s[1])
            return ("while", c, self.stmt(s[2]))
        if k == "repeat":
            c, _ = self.rexpr(s[2])
            return ("repeat", self.stmt(("seq", s[1])), c)
        if k == "for":
            l, r = self.lval(("id", s[1]))
            a, ta = self.rexpr(s[2])
            b, tb = self.rexpr(s[4])
            ct = self.ct_of(r)
            return ("for", l, ct, s[3] == "to", self.conv(a, ta, PROMOTE[ct]) if ta != PROMOTE[ct] else a,
                    self.conv(b, tb, "i32") if tb != "i32" else b, self.stmt(s[5]))
        if k == "case":
            e, t = self.rexpr(s[1])
            arms, dflt = [], None
            for labs, st in s[2]:
                ls = [x for x in labs if x != "others"]
                body = self.stmt(st)
                if "others" in labs:
                    if ls:
                        raise TranslateError(f"{self.where}: others mixed with labels")
                    dflt = body
                else:
                    arms.append((ls, body))
            return ("case", e, arms, dflt)
        if k == "assign":
            tgt = s[1]
            if tgt[0] == "id" and tgt[1] == self.where and self.result_off is not None:
                l, r = ("loc", self.result_off), self.cur["result"]
            else:
                l, r = self.lval(tgt)
            ct = self.ct_of(r)
            if ct is None:
                src, rr = self.lval(s[2])
                if rr.size != r.size:
                    raise TranslateError(f"{self.where}: aggregate copy of different sizes")
                return ("copy", l, src, r.size)
            x, t = self.rexpr(s[2])
            return ("asg", l, ct, x)
        if k == "pcall":
            n, actuals = s[1], s[2]
            if n in ("incr", "decr"):  # cpascal.h: ++(x), --(x)
                l, r = self.lval(actuals[0])
                return ("incr", l, self.ct_of(r), 1 if n == "incr" else -1)
            if n in ("write", "writeln"):
                return self.write(n, actuals)
            if n in self.procs:
                info = self.procs[n]
                return ("pcall", info["id"], self.args(info["params"], actuals))
            x, _ = self.builtin_or_ext(n, actuals)
            if x[0] == "ext":
                return ("ext", x[1], x[2])
            raise TranslateError(f"{self.where}: statement call of {n}")
        raise TranslateError(f"{self.where}: statement {k}")

    def write(self, n, actuals):
        """fixwrites.c: every item is %c, %s or %ld, decided from its C text's first token."""
        f = actuals[0]
        fe, _ = self.rexpr(f)
        items = []
        for a in actuals[1:]:
            if a[0] == "width":
                a = a[1]   # web2c drops width fields
            head = a
            while head[0] in ("idx", "fld", "call") and head[0] != "call":
                head = head[1]
            hname = head[1] if head[0] in ("id", "call") else None
            if a[0] == "char" or hname in ("xchr", "nameoffile", "months"):
                x, _ = self.rexpr(a)
                items.append(("c", x))
            elif a[0] == "str":
                items.append(("s", ("str", a[1])))
            elif hname in ("versionstring", "poolname", "formatengine", "dumpname", "stringcast",
                           "conststringcast"):
                x, _ = self.rexpr(a)
                items.append(("s", x))
            else:
                x, t = self.rexpr(a)
                items.append(("ld", self.conv(x, t, "i64") if t != "i64" else x))
        return ("write", fe, items, n == "writeln")


def main():
    import pickle
    P = pickle.load(open(sys.argv[1], "rb"))
    L = Lowerer(P)
    procs, failed = L.lower_all(keep_going=True)
    print(len(procs), "procedures lowered,", len(failed), "failed;", L.stats, "; externals:", len(L.exts))
    import collections
    kinds = collections.Counter(msg.split(": ", 1)[1][:60] for _, msg in failed)
    for k, n in kinds.most_common():
        print(n, k)


if __name__ == "__main__":
    main()
