"""Emit the lowered program as Coq terms over Syntax.v (spike H.2).

usage: emit_coq.py PDFTEX_P DEFINES... --out DIR [--chunk N]

Writes DIR/Prog_<k>.v (procedures, N per file), DIR/ProgGlobals.v (global shapes,
string literals, external and type names) and DIR/Prog.v (the procedure table),
plus DIR/manifest.json (input sha256s, counts). Every number in the output is a
Z literal; doubles are emitted as their IEEE-754 bit patterns (Python's float()
rounds a decimal correctly, as gcc does), strings as lists of byte codes.
"""
import hashlib
import json
import os
import struct
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from parser import parse          # noqa: E402
from lower import Lowerer, WORD_BYTES   # noqa: E402

CT = {"u8": "CU8", "s8": "CS8", "s16": "CS16", "u16": "CU16", "i32": "CI32", "i64": "CI64", "c8": "CC8",
      "f64": "CF64", "ptr": "CPTR", "file": "CFILE", "w8": "CW8", "w4": "CW4",
      "record": "CAGG", "array": "CAGG"}
TY = {"c8": "TC8", "i32": "TI32", "i64": "TI64", "f64": "TF64", "ptr": "TPTR", "w8": "TW8", "w4": "TW4", "file": "TFILE"}
BIN = {"add": "OAdd", "sub": "OSub", "mul": "OMul", "div": "ODiv", "mod": "OMod", "fdiv": "OFDiv"}
CMP = {"=": "CEq", "<>": "CNe", "<": "CLt", ">": "CGt", "<=": "CLe", ">=": "CGe"}
SLK = {"s": "SkS", "u": "SkU", "f": "SkF", "w": "SkW"}


def Z(z):
    return f"({z})" if z < 0 else str(z)


class Emitter:
    def __init__(self, L):
        self.L = L
        self.strings = {}
        self.types = {}
        self.nodes = 0

    def sid(self, s):
        if s not in self.strings:
            self.strings[s] = len(self.strings)
        return self.strings[s]

    def lst(self, xs):
        out = "nil"
        for x in reversed(xs):
            out = f"(cons {x} {out})"
        return out

    def lexp(self, l):
        self.nodes += 1
        k = l[0]
        if k == "glob":
            return f"(LGlob {l[1]})"
        if k == "loc":
            return f"(LLoc {l[1]})"
        if k == "ref":
            return f"(LRef {l[1]})"
        if k == "idx":
            return f"(LIdx {self.lexp(l[1])} {self.expr(l[2])} {Z(l[3])} {Z(l[4])} {l[5]})"
        if k == "pidx":
            return f"(LPIdx {self.expr(l[1])} {self.expr(l[2])} {l[3]})"
        if k == "fld":
            return f"(LFld {self.lexp(l[1])} {l[2]})"
        if k == "sl":
            b, n, sk = l[2]
            return f"(LSl {self.lexp(l[1])} {b} {n} {SLK[sk]})"
        raise ValueError(l)

    def expr(self, e):
        self.nodes += 1
        k = e[0]
        if k == "int":
            return f"(EInt {TY[e[1]]} {Z(e[2])})"
        if k == "dbl":
            bits = struct.unpack("<Q", struct.pack("<d", float(e[1])))[0]
            return f"(EDbl {bits})"
        if k == "str":
            return f"(EStr {self.sid(e[1])})"
        if k == "null":
            return "ENull"
        if k == "load":
            return f"(ELoad {TY[e[1]]} {self.lexp(e[2])})"
        if k == "un":
            return f"(ENeg {TY[e[2]]} {self.expr(e[3])})"
        if k == "bin":
            return f"(EBin {BIN[e[1]]} {TY[e[2]]} {self.expr(e[3])} {self.expr(e[4])})"
        if k == "cmp":
            if e[2] == "ptr":
                return f"(EPCmp {'true' if e[1] == '=' else 'false'} {self.expr(e[3])} {self.expr(e[4])})"
            return f"(ECmp {CMP[e[1]]} {TY[e[2]]} {self.expr(e[3])} {self.expr(e[4])})"
        if k == "and":
            return f"(EAnd {self.expr(e[1])} {self.expr(e[2])})"
        if k == "or":
            return f"(EOr {self.expr(e[1])} {self.expr(e[2])})"
        if k == "not":
            return f"(ENot {self.expr(e[1])})"
        if k == "conv":
            return f"(EConv {TY[e[1]]} {self.expr(e[2])})"
        if k == "call":
            return f"(ECall {e[1]} {self.lst([self.parg(a) for a in e[2]])})"
        if k == "ext":
            return f"(EExt {self.L.exts[e[1]]} {self.lst([self.xarg(a) for a in e[2]])})"
        if k == "addr":
            return f"(EAddr {self.lexp(e[1])})"
        if k == "padd":
            return f"(EPAdd {self.expr(e[1])} {e[2]} {'true' if e[3] == '-' else 'false'} {self.expr(e[4])})"
        if k == "abs":
            return f"(EAbs {self.expr(e[1])})"
        if k == "odd":
            return f"(EOdd {TY[e[1]]} {self.expr(e[2])})"
        if k == "alloc":
            return f"(EAlloc {e[1]} {CT[e[2]]} {self.expr(e[3])})"
        if k == "realloc":
            return f"(ERealloc {e[1]} {CT[e[2]]} {self.expr(e[3])} {self.expr(e[4])})"
        raise ValueError(k)

    def parg(self, a):
        k = a[0]
        if k == "val":
            return f"(AVal {CT[a[1]]} {self.expr(a[2])})"
        if k == "ref":
            return f"(ARef {self.lexp(a[1])})"
        if k == "copy":
            return f"(ACopy {self.lexp(a[1])} {a[2]})"
        raise ValueError(a)

    def xarg(self, a):
        k = a[0]
        if k == "lv":
            return f"(ALv {self.lexp(a[1])} {CT[a[2]]} {a[3]})"
        if k == "val":
            ty = a[1]
            return f"(AExp {TY.get(ty, 'TI32')} {self.expr(a[2])})"
        if k == "type":
            if a[1] not in self.types:
                self.types[a[1]] = len(self.types)
            return f"(AType {self.types[a[1]]})"
        raise ValueError(a)

    def stmt(self, s):
        self.nodes += 1
        k = s[0]
        if k == "skip":
            return "SSkip"
        if k == "asg":
            return f"(SAsg {self.lexp(s[1])} {CT[s[2]]} {self.expr(s[3])})"
        if k == "copy":
            return f"(SCopy {self.lexp(s[1])} {self.lexp(s[2])} {s[3]})"
        if k == "pcall":
            return f"(SPCall {s[1]} {self.lst([self.parg(a) for a in s[2]])})"
        if k == "ext":
            return f"(SExt {self.L.exts[s[1]]} {self.lst([self.xarg(a) for a in s[2]])})"
        if k == "seq":
            return f"(SSeq {self.lst([self.stmt(x) for x in s[1]])})"
        if k == "label":
            return f"(SLabel {s[1]})"
        if k == "if":
            return f"(SIf {self.expr(s[1])} {self.stmt(s[2])} {self.stmt(s[3])})"
        if k == "while":
            return f"(SWhile {self.expr(s[1])} {self.stmt(s[2])})"
        if k == "repeat":
            return f"(SRepeat {self.stmt(s[1])} {self.expr(s[2])})"
        if k == "for":
            return (f"(SFor {self.lexp(s[1])} {CT[s[2]]} {'true' if s[3] else 'false'} "
                    f"{self.expr(s[4])} {self.expr(s[5])} {self.stmt(s[6])})")
        if k == "case":
            arms = [f"(pair {self.lst([Z(z) for z in ls])} {self.stmt(b)})" for ls, b in s[2]]
            d = f"(Some {self.stmt(s[3])})" if s[3] is not None else "None"
            return f"(SCase {self.expr(s[1])} {self.lst(arms)} {d})"
        if k == "goto":
            return f"(SGoto {s[1]})"
        if k == "return":
            return "SReturn"
        if k == "incr":
            return f"(SIncr {self.lexp(s[1])} {CT[s[2]]} {Z(s[3])})"
        if k == "write":
            items = []
            for kind, x in s[2]:
                items.append(f"({ {'c': 'WC', 's': 'WS', 'ld': 'WLd'}[kind] } {self.expr(x)})")
            return f"(SWrite {self.expr(s[1])} {self.lst(items)} {'true' if s[3] else 'false'})"
        raise ValueError(k)


def shape(L, r):
    """Flatten a type into runs of (count, ct) cells."""
    if r.kind == "array":
        n = 1
        for lo, hi in r.dims:
            n *= hi - lo + 1
        el = shape(L, r.elem)
        if len(el) == 1:
            return [(el[0][0] * n, el[0][1])]
        return el * n
    if r.kind == "record":
        out = []
        for _, (off, fr) in sorted(r.fields.items(), key=lambda kv: kv[1][0]):
            out += shape(L, fr)
        return out
    ct = L.ct_of(r)
    return [(1, ct)]


def compress(runs):
    out = []
    for n, c in runs:
        if out and out[-1][1] == c:
            out[-1] = (out[-1][0] + n, c)
        else:
            out.append((n, c))
    return out


def main():
    a = sys.argv[1:]
    out = a[a.index("--out") + 1]
    chunk = int(a[a.index("--chunk") + 1]) if "--chunk" in a else 40
    files = [x for x in a if not x.startswith("--") and x not in (out, str(chunk))]
    pfile, defines = files[0], files[1:]
    text = "".join(open(d).read() for d in defines) + open(pfile).read()
    P = parse(text)
    L = Lowerer(P)
    procs, failed = L.lower_all(keep_going=True)
    import gotos
    bad, into, gcounts = gotos.check(procs)
    if bad:
        raise SystemExit(f"unresolvable gotos: {bad}")
    import cprec
    E = Emitter(L)
    os.makedirs(out, exist_ok=True)
    hdr = "(* GENERATED by docs/v27/spike/h2/translate/emit_coq.py; do not edit. *)\n" \
          "From Coq Require Import ZArith List String.\nFrom PS Require Import Syntax.\nOpen Scope Z_scope.\n\n"
    names = []
    procs = sorted(procs, key=lambda p: p["id"])
    for ci in range(0, len(procs), chunk):
        part = procs[ci:ci + chunk]
        k = ci // chunk
        with open(os.path.join(out, f"Prog_{k}.v"), "w") as f:
            f.write(hdr)
            for p in part:
                pk = []
                for n, kind, size in p["params"]:
                    if kind == "ref":
                        pk.append("PRef")
                    elif kind == "copy":
                        pk.append(f"(PCopy {size})")
                    else:
                        c = [x for x in p["layout"] if x[0] == n][0][2]
                        pk.append(f"(PVal {CT[c]})")
                res = "None" if p["result"] is None else f"(Some (pair {p['result'][0]} {CT[p['result'][1]]}))"
                body = E.stmt(p["body"])
                f.write(f"(* {p['name']} *)\nDefinition p_{p['id']} : proc := mkproc {E.lst(pk)} {p['frame']} {res}\n  {body}.\n\n")
                names.append((p["id"], p["name"], k))
    with open(os.path.join(out, "ProgGlobals.v"), "w") as f:
        f.write(hdr)
        gl = sorted(L.globals.items(), key=lambda kv: kv[1][0])
        shapes = []
        for n, (gid, r) in gl:
            runs = compress(shape(L, r))
            shapes.append(E.lst([f"(pair {c} {CT[t]})" for c, t in runs]))
        f.write(f"Definition globals : list gshape := {E.lst(shapes)}.\n\n")
        strs = sorted(E.strings.items(), key=lambda kv: kv[1])
        f.write("Definition strings : list (list Z) := " +
                E.lst([E.lst([str(b) for b in s.encode('latin-1')]) for s, _ in strs]) + ".\n\n")
        # name tables: the boundary model (Boundary.v) names externals, globals and
        # procedures through these, so it does not depend on numbering
        exts = sorted(L.exts, key=L.exts.get)
        f.write("Definition ext_names : list string := " +
                E.lst(['"%s"%%string' % n for n in exts]) + ".\n")
        for n in exts:
            f.write(f"Definition X_{n} : Z := {L.exts[n]}.\n")
        for n, (gid, _) in gl:
            f.write(f"Definition G_{n} : Z := {gid}.\n")
        for pid, n, _ in names:
            f.write(f"Definition P_{n} : Z := {pid}.\n")
        for n, i in sorted(E.types.items(), key=lambda kv: kv[1]):
            f.write(f"Definition T_{n} : Z := {i}.\n")
    with open(os.path.join(out, "Prog.v"), "w") as f:
        f.write(hdr)
        f.write("".join(f"From PS Require Prog_{k}.\n" for k in sorted(set(k for _, _, k in names))))
        f.write("\nDefinition procs : list proc := " +
                E.lst([f"Prog_{k}.p_{i}" for i, _, k in names]) + ".\n")
    man = {
        "inputs": {os.path.basename(x): hashlib.sha256(open(x, "rb").read()).hexdigest() for x in [pfile] + defines},
        "procedures": len(procs), "failed": failed, "externals": sorted(L.exts, key=L.exts.get),
        "globals": [n for n, _ in sorted(L.globals.items(), key=lambda kv: kv[1][0])],
        "ext_globals": L.ext_globals,
        "strings": len(E.strings), "types_as_args": sorted(E.types, key=E.types.get),
        "ir_nodes": E.nodes, "proc_names": [n for _, n, _ in names], "stats": L.stats,
        "gotos": gcounts, "gotos_into_structured": into, "c_vs_pascal_grouping": cprec.check(P),
    }
    json.dump(man, open(os.path.join(out, "manifest.json"), "w"), indent=1)
    print(f"{len(procs)} procedures emitted ({len(failed)} failed), {E.nodes} IR nodes, "
          f"{len(L.exts)} externals, {len(E.strings)} strings -> {out}")


if __name__ == "__main__":
    main()
