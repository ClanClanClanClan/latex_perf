"""C's unspecified evaluation order, checked (spike H.2).

C leaves unspecified the order in which an operator's operands, a call's arguments,
and an assignment's target address and value are evaluated (C11 6.5p3, 6.5.2.2p10,
6.5.16p3). PS evaluates left to right, target first. That is exact only where the
order cannot matter: where neither side writes what the other side reads or writes.

This module computes, for every procedure, the regions it may read and write
(transitively through its callees), and checks every unsequenced pair in the IR.
Regions: ('g', gid) a global's own cells; ('h', gid) the heap block(s) reached through
the pointer global gid (mem and eqtb, which web2c copies into locals, count as zmem
and zeqtb); ('l',) the current frame; ANY for an external whose effects are not
declared here. A pair conflicts if W1 meets R2 u W2 or W2 meets R1 (ANY meets every
non-empty set). `check(L, procs)` returns (conflicts, pairs checked)."""
ANY = ("ANY",)

# Externals. An external the boundary model (Boundary.v) does not model makes the run
# Stuck, so on every run that is not Stuck it was never called: its effect is empty.
# A modelled external's effect is declared here from its C source, and `modelled()`
# checks that this table and Boundary.v name the same externals. Every argument that
# is a variable, or the address of one, counts as read and written (a C macro may
# assign it).
#   name: (globals read, globals written, heap blocks read, heap blocks written, calls)
EXT_EFFECTS = {
    "setupboundvariable": ((), (), (), (), ()),
    "stdout": ((), (), (), (), ()), "stderr": ((), (), (), (), ()), "stdin": ((), (), (), (), ()),
    "fflush": ((), (), (), (), ()), "initstarttime": ((), (), (), (), ()),
    "pdfinitmapfile": ((), (), (), (), ()), "uexit": ((), (), (), (), ()),
    "inputln": (("first", "bufsize", "buffer", "maxbufstack", "xord"), ("last", "maxbufstack"),
                ("buffer",), ("buffer",), ()),
    "topenin": (("first", "buffer"), (), (), ("buffer",), ()),
    "loadpoolstrings": (("strpool", "poolptr"), ("poolptr",), (), ("strpool",), ("makestring",)),
    "dateandtime": ((), (), (), (), ()), "secondsandmicros": ((), (), (), (), ()),
    "synctexinitcommand": (("synctexoption", "synctexoffset", "zeqtb"), (), (), ("zeqtb",), ()),
    "getjobname": ((), (), (), (), ()), "recorderchangefilename": ((), (), (), (), ()),
    "stringcast": ((), (), (), (), ()), "libcfree": ((), (), (), (), ()), "ISDIRSEP": ((), (), (), (), ()), "synctexterminate": ((), (), (), (), ()), "aclose": ((), (), (), (), ()),
    "aopenout": (("nameoffile", "shellenabledp"), (), ("nameoffile",), (), ()),
    "makepdftexbanner": (("versionstring", "strpool", "poolptr", "poolsize"), ("poolptr", "pdftexbanner"), (),
                         ("strpool",), ("makestring", "getnullstr")),
    # spike H.3, the format file (Boundary.v): the (un)dump macros use the global fmtfile;
    # their base argument is a variable, counted read and written below
    "wopenin": (("nameoffile", "texinputtype"), ("nameoffile", "namelength"), ("nameoffile",), ("nameoffile",), ()),
    "wopenout": (("nameoffile",), (), ("nameoffile",), (), ()),
    "wclose": ((), (), (), (), ()),
    "undumpthings": (("fmtfile",), (), (), (), ()), "undumpint": (("fmtfile",), (), (), (), ()),
    "undumphh": (("fmtfile",), (), (), (), ()), "undumpcheckedthings": (("fmtfile",), (), (), (), ()),
    "undumpuppercheckthings": (("fmtfile",), (), (), (), ()),
    "dumpthings": (("fmtfile",), (), (), (), ()), "dumpint": (("fmtfile",), (), (), (), ()),
    "dumphh": (("fmtfile",), (), (), (), ()),
    "undumpimagemeta": (("fmtfile",), (), (), (), ()), "dumpimagemeta": (("fmtfile",), (), (), (), ()),
    "undumptounicode": (("fmtfile",), (), (), (), ()), "dumptounicode": (("fmtfile",), (), (), (), ()),
    # strcmp reads the two strings its pointer arguments point to: any heap block
    "strcmp": ((), (), ("*",), (), ()),
    "ucharcast": ((), (), (), (), ()),
    "getcreationdate": (("strpool", "poolptr", "poolsize"), ("poolptr",), (), ("strpool",), ()),
    "strlen": ((), (), ("*",), (), ()),
    # strcpy writes the block its first argument points to: any heap block
    "strcpy": ((), (), ("*",), ("*",), ()),
    # boundary step, file input (Boundary.v open_input, Kpse.v): open_input reads
    # nameoffile (and its block), texinputtype and (open_in_or_pipe) shellenabledp, and
    # replaces nameoffile and namelength; bopenin also sets tfmtemp (the first getc);
    # kpathsea's own state and the streams are the I/O state
    "kpseinnameok": ((), (), ("*",), (), ()),
    "kpsetexformat": ((), (), (), (), ()),
    "aopenin": (("nameoffile", "shellenabledp", "texinputtype"), ("nameoffile", "namelength"),
                ("nameoffile",), ("nameoffile",), ()),
    "bopenin": (("nameoffile", "texinputtype"), ("nameoffile", "namelength", "tfmtemp"),
                ("nameoffile",), ("nameoffile",), ()),
    "makefullnamestring": (("strpool", "poolptr", "poolsize"), ("poolptr",), (), ("strpool",),
                           ("makestring", "getnullstr")),
    "synctexstartinput": (("synctexoption", "synctexoffset", "zeqtb", "curinput"), ("curinput",),
                          ("zeqtb",), ("zeqtb",), ()),
    "getc": ((), (), (), (), ()), "feof": ((), (), (), (), ()), "eof": ((), (), (), (), ()),
    "bclose": ((), (), (), (), ()),
    "kpseoutnameok": ((), (), ("*",), (), ()),
    "texmfyesno": ((), (), ("*",), (), ()),
    # pdftex.h pdfassert = assert: reads its condition (a value); a false one aborts (Stuck)
    "pdfassert": ((), (), (), (), ()),
    # cpascal.h: a string literal; printcstring calls printchar on each byte of its argument
    "promptfilenamehelpmsg": ((), (), (), (), ()),
    "printcstring": ((), (), ("*",), (), ("printchar",)),
    # checkpoint 3: getfilesize reads its string (strstart, strpool) and nameoffile is not
    # touched (it searches by a C string); it appends to the pool
    "removepdffile": (("outputfilename", "fixedpdfdraftmode"), (), (), (), ()),
    "synctexabort": ((), (), (), (), ()),
    "getfilesize": (("strstart", "strpool", "poolptr", "poolsize"), ("poolptr",), ("strstart", "strpool"), ("strpool",), ()),
}


# Externals with no effect on the I/O state: a handle constant, a cast, a string read
# (spike H.3; before, every modelled external counted as writing the I/O state, which made
# `write(stdout, ..., stringcast(nameoffile+1))` an unsequenced conflict)
PURE_EXTS = {"stdout", "stderr", "stdin", "stringcast", "ucharcast", "ISDIRSEP", "strcmp", "strlen",
             "kpseinnameok", "kpsetexformat", "pdfassert"}
# Externals that are C functions (or macros) reading their arguments' values only: a variable
# argument is read, not written (undumpimagemeta(integer, integer, integer) is a function)
VALUE_ARG_EXTS = {"undumpimagemeta", "strcmp", "strlen", "stringcast", "ucharcast", "ISDIRSEP", "dumpint",
                  "kpseinnameok", "kpseoutnameok", "texmfyesno", "getc", "feof", "eof", "pdfassert", "printcstring"}


# Procedures that never return (boundary step, H-boundary-report.md): the four the source
# declares `noreturn` (tex.ch; web2c gives them C's noreturn attribute), each VERIFIED here:
# its body has no return, goto or label, and cannot complete normally (it ends in uexit, or
# in a call to one of these, on every branch). Effects on paths that end in such a call never
# return to an unsequenced neighbour; `check` uses that (rule (b) there).
NORETURN_DECLARED = ("jumpout", "overflow", "fatalerror", "confusion")


def _jumps(s):
    if not isinstance(s, tuple) or not s:
        return False
    if s[0] in ("return", "goto", "label"):
        return True
    return any(_jumps(x) for x in s[1:] if isinstance(x, tuple)) or \
        any(_jumps(y) for x in s[1:] if isinstance(x, list) for y in x if isinstance(y, tuple))


def _cannot_complete(s, nr):
    k = s[0]
    if k == "pcall":
        return s[1] in nr
    if k == "ext":
        return s[1] == "uexit"
    if k == "seq":
        return any(_cannot_complete(x, nr) for x in s[1])
    if k == "if":
        return _cannot_complete(s[2], nr) and _cannot_complete(s[3], nr)
    return False


def noreturn_procs(L, procs):
    byname = {p["name"]: p for p in procs}
    nr = set()
    changed = True
    while changed:
        changed = False
        for n in NORETURN_DECLARED:
            pid = byname[n]["id"]
            if pid not in nr and not _jumps(byname[n]["body"]) and _cannot_complete(byname[n]["body"], nr):
                nr.add(pid)
                changed = True
    if len(nr) != len(NORETURN_DECLARED):
        raise SystemExit(f"a declared noreturn procedure is not shown to never return: "
                         f"{sorted(set(NORETURN_DECLARED) - {p['name'] for p in procs if p['id'] in nr})}")
    return frozenset(nr)


def modelled(boundary_v_text):
    import re
    return set(re.findall(r"x =\? X_(\w+)", boundary_v_text))


class Effects:
    def __init__(self, L, procs, nr=None):
        """nr = None: every path; nr = the noreturn procedures: the effects on the paths that
        return (a call to one of nr, and uexit, contribute nothing: they never return)"""
        self.L = L
        self.nr = nr
        self.procs = {p["id"]: p for p in procs}
        self.gname = {gid: n for n, (gid, _) in L.globals.items()}
        self.mem_loc = {}   # proc id -> {local offset: region} for mem/eqtb register copies
        for p in procs:
            m = {}
            for n, off, _, _, _ in p["layout"]:
                if n in ("mem", "eqtb"):
                    m[off] = ("h", L.globals["zmem" if n == "mem" else "zeqtb"][0])
            self.mem_loc[p["id"]] = m
        self.summ = {pid: (set(), set()) for pid in self.procs}
        self.param_offsets = {}
        for p in procs:
            offs, o = [], 0
            for n, kind, size in p["params"]:
                offs.append(o)
                o += size if kind == "copy" else 1
            self.param_offsets[p["id"]] = offs
        changed = True
        while changed:
            changed = False
            for pid, p in self.procs.items():
                self.cur = pid
                r, w = set(), set()
                self.stmt_eff(p["body"], r, w)
                r = {x for x in r if x[0] != "l"}
                w = {x for x in w if x[0] != "l"}
                if (r, w) != self.summ[pid]:
                    if not (r <= self.summ[pid][0] and w <= self.summ[pid][1]):
                        self.summ[pid] = (self.summ[pid][0] | r, self.summ[pid][1] | w)
                        changed = True

    # region of an lvalue
    def lregion(self, l):
        k = l[0]
        if k == "glob":
            return ("g", l[1])
        if k == "loc":
            return ("l", l[1])
        if k == "ref":
            return ("p", l[1])        # the target of the var parameter in frame cell l[1]
        if k in ("idx", "fld", "sl"):
            return self.lregion(l[1])
        if k == "pidx":
            p = l[1]
            if p[0] == "load":
                base = p[2]
                if base[0] == "glob":
                    return ("h", base[1])
                if base[0] == "loc" and base[1] in self.mem_loc.get(self.cur, {}):
                    return self.mem_loc[self.cur][base[1]]
            return ANY
        return ANY

    def lval_eff(self, l, r, w):
        """reads made while computing the address of l"""
        k = l[0]
        if k == "ref":
            r.add(("l", l[1]))
        elif k == "idx":
            self.lval_eff(l[1], r, w)
            self.expr_eff(l[2], r, w)
        elif k in ("fld", "sl"):
            self.lval_eff(l[1], r, w)
        elif k == "pidx":
            self.expr_eff(l[1], r, w)
            self.expr_eff(l[2], r, w)

    def expr_eff(self, e, r, w):
        if not isinstance(e, tuple) or not e:
            return
        k = e[0]
        if k == "load":
            self.lval_eff(e[2], r, w)
            r.add(self.lregion(e[2]))
        elif k == "call":
            self.call_eff(e[1], e[2], r, w)
        elif k == "ext":
            self.ext_eff(e[1], e[2], r, w)
        elif k in ("alloc", "realloc"):
            w.add(("alloc",))
            for x in e[1:]:
                self.expr_eff(x, r, w)
        elif k == "addr":
            self.lval_eff(e[1], r, w)
        else:
            for x in e[1:]:
                if isinstance(x, tuple):
                    self.expr_eff(x, r, w)

    def call_eff(self, pid, args, r, w):
        sr, sw = self.summ.get(pid, (set(), set()))
        if self.nr is not None and pid in self.nr:
            sr, sw = set(), set()
        offs = self.param_offsets[pid]
        amap = {}
        for off, a in zip(offs, args):
            if a[0] == "ref":
                amap[off] = self.lregion(a[1])
        for S, D in ((sr, r), (sw, w)):
            for x in S:
                if x[0] == "p":       # the callee's var parameter: the actual argument
                    D.add(amap.get(x[1], ANY))
                else:
                    D.add(x)
        for a in args:
            self.arg_eff(a, r, w)

    def ext_eff(self, name, args, r, w):
        eff = EXT_EFFECTS.get(name)
        if eff is None:
            return                    # unmodelled: the run is Stuck here
        if self.nr is not None and name == "uexit":
            return                    # it never returns
        gr, gw, hr, hw, calls = eff
        g = self.L.globals
        r.update(("g", g[n][0]) for n in gr)
        w.update(("g", g[n][0]) for n in gw)
        r.update(ANY if n == "*" else ("h", g[n][0]) for n in hr)
        w.update(ANY if n == "*" else ("h", g[n][0]) for n in hw)
        if name not in PURE_EXTS:
            w.add(("io",))
        for c in calls:
            pid = self.L.procs[c]["id"]
            sr, sw = self.summ.get(pid, (set(), set()))
            r |= sr
            w |= sw
        for a in args:
            self.xarg_eff(a, r, w, name in VALUE_ARG_EXTS)

    def arg_eff(self, a, r, w, callee=None):
        if a[0] == "val":
            self.expr_eff(a[2], r, w)
        elif a[0] == "ref":
            self.lval_eff(a[1], r, w)
            reg = self.lregion(a[1])
            r.add(reg)
            w.add(reg)     # the callee may write its var parameter
        elif a[0] == "copy":
            self.lval_eff(a[1], r, w)
            r.add(self.lregion(a[1]))

    def xarg_eff(self, a, r, w, ro=False):
        if a[0] == "lv":
            self.lval_eff(a[1], r, w)
            reg = self.lregion(a[1])
            r.add(reg)
            if not ro:
                w.add(reg)     # a C macro may assign its argument
        elif a[0] == "val":
            self.expr_eff(a[2], r, w)
            if a[2][0] == "addr":      # &x given to a C function, which may write x
                reg = self.lregion(a[2][1])
                r.add(reg)
                w.add(reg)

    def stmt_eff(self, s, r, w):
        k = s[0]
        if k == "asg":
            self.lval_eff(s[1], r, w)
            w.add(self.lregion(s[1]))
            self.expr_eff(s[3], r, w)
        elif k == "copy":
            self.lval_eff(s[1], r, w)
            self.lval_eff(s[2], r, w)
            w.add(self.lregion(s[1]))
            r.add(self.lregion(s[2]))
        elif k == "incr":
            self.lval_eff(s[1], r, w)
            r.add(self.lregion(s[1]))
            w.add(self.lregion(s[1]))
        elif k == "pcall":
            self.call_eff(s[1], s[2], r, w)
        elif k == "ext":
            self.ext_eff(s[1], s[2], r, w)
        elif k == "write":
            w.add(("io",))
            self.expr_eff(s[1], r, w)
            for _, x in s[2]:
                self.expr_eff(x, r, w)
        elif k == "for":
            self.lval_eff(s[1], r, w)
            w.add(self.lregion(s[1]))
            self.expr_eff(s[4], r, w)
            self.expr_eff(s[5], r, w)
            self.stmt_eff(s[6], r, w)
        elif k == "seq":
            for x in s[1]:
                self.stmt_eff(x, r, w)
        elif k == "if":
            self.expr_eff(s[1], r, w)
            self.stmt_eff(s[2], r, w)
            self.stmt_eff(s[3], r, w)
        elif k == "while":
            self.expr_eff(s[1], r, w)
            self.stmt_eff(s[2], r, w)
        elif k == "repeat":
            self.stmt_eff(s[1], r, w)
            self.expr_eff(s[2], r, w)
        elif k == "case":
            self.expr_eff(s[1], r, w)
            for _, b in s[2]:
                self.stmt_eff(b, r, w)
            if s[3] is not None:
                self.stmt_eff(s[3], r, w)


def meets(a, b):
    """ANY is every region an external can reach: every global, heap block and the I/O
    state, but not the current frame (an external reaches a local only through an
    argument, which xarg_eff records)."""
    if not a or not b:
        return False
    if ANY in a:
        return any(x[0] != "l" for x in b)
    if ANY in b:
        return any(x[0] != "l" for x in a)
    return bool(a & b)


def conflict(e1, e2):
    (r1, w1), (r2, w2) = e1, e2
    return meets(w1, r2 | w2) or meets(w2, r1)


def conflict2(x1, x2):
    """x = (effects on every path, effects on the paths that return). Rule (a): the parts do
    not interfere. Rule (b) (boundary step): a part that writes nothing commutes with a part
    whose returning paths write nothing it reads: if the other part returns, the two orders
    reach the same state and values; if it never returns, the part that writes nothing left
    no trace either way."""
    (f1, ret1), (f2, ret2) = x1, x2
    if not conflict(f1, f2):
        return False
    if not f1[1] and not meets(ret2[1], f1[0]):
        return False
    if not f2[1] and not meets(ret1[1], f2[0]):
        return False
    return True


def check(L, procs):
    E = Effects(L, procs)
    ER = Effects(L, procs, noreturn_procs(L, procs))
    conflicts, pairs = [], [0]

    def both(f):
        out = []
        for X in (E, ER):
            r, w = set(), set()
            f(X, r, w)
            out.append((r, w))
        return tuple(out)

    def eff_e(e):
        return both(lambda X, r, w: X.expr_eff(e, r, w))

    def eff_l(l):
        return both(lambda X, r, w: X.lval_eff(l, r, w))

    def eff_arg(a, xt, ro=False):
        if xt:
            return both(lambda X, r, w: X.xarg_eff(a, r, w, ro))
        return both(lambda X, r, w: X.arg_eff(a, r, w))

    def group(kind, effs, where, node=None):
        # every pair of unsequenced parts
        for i in range(len(effs)):
            for j in range(i + 1, len(effs)):
                pairs[0] += 1
                if conflict2(effs[i], effs[j]):
                    conflicts.append((where, kind, node, effs[i][0], effs[j][0]))
                    return

    def ve(e, where):
        if not isinstance(e, tuple) or not e:
            return
        k = e[0]
        if k in ("bin", "cmp"):
            group(k, [eff_e(e[3]), eff_e(e[4])], where, e)
        elif k == "call":
            group("args", [eff_arg(a, False) for a in e[2]], where, e)
        elif k == "ext":
            group("xargs", [eff_arg(a, True, e[1] in VALUE_ARG_EXTS) for a in e[2]], where, e)
        elif k == "padd":
            group("padd", [eff_e(e[1]), eff_e(e[4])], where, e)
        elif k == "load":
            vl(e[2], where)
        for x in e[1:]:
            if isinstance(x, tuple):
                ve(x, where)
            elif isinstance(x, list):
                for y in x:
                    if isinstance(y, tuple):
                        ve(y if y[0] not in ("val", "ref", "copy", "lv") else
                           (y[2] if y[0] == "val" else ("load", "i32", y[1])), where)

    def vl(l, where):
        if l[0] == "idx":
            group("index", [eff_l(l[1]), eff_e(l[2])], where, l)
            vl(l[1], where)
            ve(l[2], where)
        elif l[0] == "pidx":
            group("pindex", [eff_e(l[1]), eff_e(l[2])], where, l)
            ve(l[1], where)
            ve(l[2], where)
        elif l[0] in ("fld", "sl"):
            vl(l[1], where)

    def vs(s, where):
        k = s[0]
        if k == "asg":
            group("assign", [eff_l(s[1]), eff_e(s[3])], where, s)
            vl(s[1], where)
            ve(s[3], where)
        elif k in ("pcall", "ext"):
            group("args", [eff_arg(a, k == "ext", k == "ext" and s[1] in VALUE_ARG_EXTS) for a in s[2]], where, s)
            for a in s[2]:
                if a[0] == "val":
                    ve(a[2], where)
        elif k == "seq":
            for x in s[1]:
                vs(x, where)
        elif k == "if":
            ve(s[1], where)
            vs(s[2], where)
            vs(s[3], where)
        elif k == "while":
            ve(s[1], where)
            vs(s[2], where)
        elif k == "repeat":
            vs(s[1], where)
            ve(s[2], where)
        elif k == "for":
            ve(s[4], where)
            ve(s[5], where)
            vs(s[6], where)
        elif k == "case":
            ve(s[1], where)
            for _, b in s[2]:
                vs(b, where)
            if s[3] is not None:
                vs(s[3], where)
        elif k == "write":
            group("write", [eff_e(s[1])] + [eff_e(x) for _, x in s[2]], where, s)
    for p in procs:
        E.cur = ER.cur = p["id"]
        vs(p["body"], p["name"])
    return conflicts, pairs[0]
