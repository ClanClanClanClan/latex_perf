# gdb Python script (review round 4, MEDIUM-2): count, for one run of one
# document, how often each DIVERGES-site instruction executes and how often it
# executes with an EDGE operand. Sourced by gdb (`gdb -x trace_gdb.py`); it
# starts nothing itself: the driver in RUN.md starts the engine under gdb
# (native, aarch64) or attaches to qemu-user's gdbstub (x86_64), then calls
#   python install("<site_addrs.tsv>", "<arch>")   after the program is loaded
#   continue                                        (to exit, or to a signal)
#   python stopped()                                record a signal stop, if any
#   continue                                        (deliver it: the run dies as it would)
#   python dump("<out.json>")
#
# A breakpoint never stops the program: its stop() method counts and returns
# False. Each one is placed at <function symbol> + <offset> (site_addrs.tsv) and
# its instruction is disassembled there and compared with the census mnemonic
# before the run starts: a breakpoint on any other instruction aborts.
#
# EDGE operand (the operand values at which the two ISAs answer differently):
#   DIV  (32-bit sdiv/udiv/idiv) divisor 0, divisor -1, dividend INT_MIN or
#        divisor INT_MIN (as 32-bit patterns; for udiv, 0x80000000)
#   F2I  (fcvtzs/cvttsd2si to 32 bits) source NaN, or outside the open
#        interval (-2147483649, 2147483648), where truncation is undefined in C
#
# F2I sources are CROSS-CHECKED against the instruction's result. A companion
# breakpoint on the next instruction reads the destination register, and the
# source is the candidate lane whose conversion, by the ISA's own rule (x86_64:
# 0x80000000 for NaN and out of range; aarch64: saturate, NaN -> 0), gives that
# result. A hit for which no candidate lane gives the result is counted as
# `inconsistent` (build_trace.py refuses any). Why: qemu-user 7.0's x86_64
# gdbstub (the colima VM's) sends the two 64-bit halves of an xmm register
# swapped, so gdb shows the scalar double in v2_double[1], not [0]; reading [0]
# alone gave 0 edge hits for every x86_64 conversion. Both lanes are candidates
# on x86_64, only the scalar lane on aarch64 (native gdb); `lanes` counts which
# lane matched.
import json
import math
import re

import gdb

ROWS, BPS, SIG, SIGNALS = [], [], [], []


def _on_stop(ev):
    if isinstance(ev, gdb.SignalEvent):
        SIGNALS.append(ev.stop_signal)


gdb.events.stop.connect(_on_stop)
INT_MIN = 0x80000000


def u32(expr):
    return int(gdb.parse_and_eval(expr).cast(gdb.lookup_type("long long"))) & 0xFFFFFFFF


def operands(arch, insn):
    """(kind, [gdb expressions]) for the instruction text of the census."""
    op, args = insn.split(None, 1)
    regs = [a.strip() for a in args.split(",")]
    if arch == "arm64" and op in ("sdiv", "udiv"):
        assert all(r.startswith("w") for r in regs), insn
        return "DIV", [f"${regs[1]}", f"${regs[2]}"]
    if arch == "arm64" and op == "fcvtzs":
        assert regs[0].startswith("w") and regs[1].startswith("d"), insn
        return "F2I", [f"$v{regs[1][1:]}.d.f[0]", f"${regs[0]}"]
    if arch == "amd64" and op == "idiv":
        r = regs[0].lstrip("%")
        assert re.fullmatch(r"e[a-z]{2}|r\d+d", r), insn
        return "DIV", ["$eax", f"${r}"]
    if arch == "amd64" and op == "cvttsd2si":
        src, dst = (x.lstrip("%") for x in regs)
        assert src.startswith("xmm") and (dst.startswith("e") or dst.endswith("d")), insn
        return "F2I", [f"${src}.v2_double[0]", f"${src}.v2_double[1]", f"${dst}"]
    raise AssertionError(f"no operand model for {arch} {insn}")


def converts(arch, x):
    """the 32-bit result pattern of the ISA's truncating conversion of x"""
    if math.isnan(x):
        return INT_MIN if arch == "amd64" else 0
    if not (-2147483649.0 < x < 2147483648.0):
        return INT_MIN if arch == "amd64" or x < 0 else 0x7FFFFFFF
    return int(x) & 0xFFFFFFFF


def is_edge(x):
    return math.isnan(x) or not (-2147483649.0 < x < 2147483648.0)


class Site(gdb.Breakpoint):
    def __init__(self, row, addr):
        super().__init__(f"*{addr:#x}", internal=False)
        self.row, self.addr, self.hits, self.edge, self.examples = row, addr, 0, 0, []
        self.inconsistent, self.lanes, self.waiting = 0, {}, None
        self.kind, self.exprs = operands(row["arch"], row["insn"])

    def count(self, edge, val):
        if edge:
            self.edge += 1
            if len(self.examples) < 3:
                self.examples.append(val)

    def stop(self):
        self.hits += 1
        if self.kind == "DIV":
            a, b = (u32(e) for e in self.exprs)
            self.count(b in (0, 0xFFFFFFFF, INT_MIN) or a == INT_MIN,
                       [a - (1 << 32) if a & INT_MIN else a, b - (1 << 32) if b & INT_MIN else b])
        else:   # the sources now; decided at the next instruction (Result)
            self.waiting = [float(gdb.parse_and_eval(e)) for e in self.exprs[:-1]]
        return False

    def result(self):
        if self.waiting is None:
            return
        lanes, self.waiting = self.waiting, None
        got = u32(self.exprs[-1])
        ok = [i for i, x in enumerate(lanes) if converts(self.row["arch"], x) == got]
        if not ok or len({is_edge(lanes[i]) for i in ok}) != 1:
            self.inconsistent += 1
            return
        self.lanes[ok[0]] = self.lanes.get(ok[0], 0) + 1
        x = lanes[ok[0]]
        self.count(is_edge(x), [repr(x), got - (1 << 32) if got & INT_MIN else got])


class Result(gdb.Breakpoint):
    def __init__(self, site, addr):
        super().__init__(f"*{addr:#x}", internal=True)
        self.site = site

    def stop(self):
        self.site.result()
        return False


def install(tsv, arch):
    hdr, *lines = open(tsv).read().splitlines()
    keys = hdr.split("\t")
    for ln in lines:
        r = dict(zip(keys, ln.split("\t")))
        if r["arch"] != arch:
            continue
        entry = int(gdb.parse_and_eval(f"(long long)&'{r['function']}'"))
        addr = entry + int(r["offset"], 16)
        dis = gdb.execute(f"x/i {addr:#x}", to_string=True)
        mnem = r["insn"].split()[0]
        if not re.search(rf":\s+{re.escape(mnem)}\s", dis):
            raise gdb.GdbError(f"breakpoint for {r['site']} at {addr:#x} is not {mnem}: {dis.strip()}")
        ROWS.append(r)
        b = Site(r, addr)
        BPS.append(b)
        if b.kind == "F2I":
            nxt = gdb.selected_frame().architecture().disassemble(addr, count=2)[1]["addr"]
            Result(b, nxt)
    gdb.write(f"TRACE installed {len(BPS)} breakpoints for {arch}\n")


def stopped():
    try:
        pc = int(gdb.parse_and_eval("$pc"))
    except gdb.error:
        return
    sym = gdb.execute(f"info symbol {pc:#x}", to_string=True).strip()
    SIG.append({"pc": f"{pc:#x}", "symbol": sym, "signal": SIGNALS[-1] if SIGNALS else None,
                "at_site": [b.row["site"] for b in BPS if b.addr == pc]})


def dump(path):
    def cv(n):
        v = gdb.convenience_variable(n)
        return None if v is None else int(v)
    out = {"exitcode": cv("_exitcode"), "exitsignal": cv("_exitsignal"), "signal_stops": SIG,
           "breakpoints": [{"site": b.row["site"], "class": b.row["class"], "function": b.row["function"],
                            "link_addr": b.row["addr"], "runtime_addr": f"{b.addr:#x}", "insn": b.row["insn"],
                            "hits": b.hits, "edge_hits": b.edge, "edge_examples": b.examples,
                            "inconsistent": b.inconsistent, "lanes": {str(k): v for k, v in b.lanes.items()},
                            "pending_at_exit": b.waiting is not None} for b in BPS]}
    with open(path, "w") as f:
        json.dump(out, f, indent=1)
    gdb.write(f"TRACE wrote {path}\n")
