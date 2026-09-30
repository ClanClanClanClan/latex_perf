"""Capacity probes of the strict fragment (correction C-94).

Shared by measure_strict_capacity.py (corpora/strict_s0/capacity.json) and
gen_strict_arg_signatures.py (the A-CAP families of every candidate).

THE CLASS. A TeX capacity (here: grouping levels, 255) must be bounded by an
exact account of what it counts, never through a proxy the grammar can
outgrow. C-86 bounded the BRACE depth; slice A let a formula open inside an
argument, so a document of 128 box-and-formula levels held 256 groups within
100 braces... and was PROVEN-READY. The kernel now bounds Decide.groups, the
TeX groups of the frame stack, over every state of the run (Decide.peak).

THE PROBES. The frame kinds and which kind can be pushed on which are read
from the EXTRACTED model (strict_decide.exe --frame-pairs: a breadth-first
search through the extracted step over every token of the grammar), never
listed by hand. For every ordered pair (below, above) the model can stack,
`stream` builds a token stream whose run holds exactly `target` groups at
its peak, repeating the pair as often as the model allows (a cycle through
the pair, else the pair once on a filler chain), with one character
innermost and every frame closed after it. The probes grade the stream at
the bound (the model must decide it and agree with pdfTeX), one group past
it (the model must place it outside the fragment), and search the depth at
which pdfTeX itself overflows, which must lie where the account predicts:
the body's measured capacity, less at most the largest transient a
construct adds on top of its frames (C-94 exactness check).
"""
from __future__ import annotations

from collections import deque


def arg_groups(asigs: dict) -> dict:
    """{(name, "t"|"m"): g} from argument signatures (the run behaviours'
    measured TeX groups, C-94)."""
    out = {}
    for n, h in asigs.items():
        if h["text"][0] == "run":
            out[(n, "t")] = h["text"][3]
        if h["math"][0] == "run":
            out[(n, "m")] = h["math"][2]
    return out


def cost_of(label: str, groups: dict) -> int:
    """The TeX groups of a frame by its label (strict_decide.ml
    pushed_label): 1, or an argument frame's g for its command and the mode
    it was pushed from."""
    if label.startswith("arg."):
        name, mode = label[4:].split(":", 1)[1].rsplit("/", 1)
        return groups[(name, mode)]
    return 1


def graph(pairs: dict) -> tuple[dict, dict]:
    """(successors of each label, the opener tokens of each (below, above)
    pair: the last step of the model's witness path)."""
    succ, opener = {}, {}
    for p in pairs["pairs"]:
        succ.setdefault(p["below"], [])
        if p["above"] not in succ[p["below"]]:
            succ[p["below"]].append(p["above"])
        opener[(p["below"], p["above"])] = p["path"][-1]
    for k in succ:
        succ[k].sort()
    return succ, opener


def dim_weight(asigs: dict, table: dict):
    """C-104: the dimensions a frame of each label costs the stream (its
    opener and closer tokens, and for an argument frame its command), by the
    account's table: the stream builder keeps the whole chain within the
    dimension bound, preferring labels of no dimensions."""
    def w(label: str) -> int:
        if label.startswith("arg."):
            name, mode = label[4:].split(":", 1)[1].rsplit("/", 1)
            m = mode == "m"
            return asigs[name]["dim"][1 if m else 0] + table["open"][1 if m else 0] \
                + table["close"][1]
        if label == "script":
            return table["script"][1] + table["open"][1]
        if label == "mgroup":
            return table["open"][1]
        if label.startswith("inline."):
            return 2 * max(table["dollar"][0], table["open_inline"][0])
        if label.startswith("display."):
            return 4 * max(table["dollar"][0], table["open_display"][0])
        return 0
    return w


def _path(succ: dict, src: str, dst: str, wt=None) -> list[str] | None:
    """A shortest label path of at least one pair from src to dst (both
    included; among the shortest, the lightest first), or None."""
    q, seen = deque([(src, [src])]), {src}
    while q:
        x, p = q.popleft()
        for y in sorted(succ.get(x, []), key=lambda y: (wt(y) if wt else 0, y)):
            if y == dst:
                return p + [y]
            if y not in seen:
                seen.add(y)
                q.append((y, p + [y]))
    return None


def stream(pairs: dict, below: str, above: str, target: int, groups: dict,
           wt=None, budget: int | None = None) -> tuple[list, list[str]] | None:
    """A token stream (strict_decide.exe JSON tokens, to be closed with
    "close": true) whose frame stack peaks at exactly `target` groups, made
    of the pair (below, above) repeated; and its label chain. None when the
    pair cannot be reached or `target` cannot be met exactly. With `wt`
    (dim_weight) and `budget` (C-104), the pair is repeated only while the
    chain stays within the dimension budget, and the rest is filled with the
    lightest labels."""
    wt = wt or (lambda _x: 0)
    budget = budget if budget is not None else 10 ** 12
    succ, opener = graph(pairs)
    pre = ["top"] if below == "top" else _path(succ, "top", below, wt)
    if pre is None:
        return None
    # a cycle through the pair: above ... below
    back = _path(succ, above, below, wt) if below != "top" else None
    chain = pre[1:] + [above]
    cost = sum(cost_of(x, groups) for x in chain)
    wsum = sum(wt(x) for x in chain)
    if cost > target:
        return None
    if back is not None:
        loop = back[1:] + [above]  # ... below, above
        while True:
            step = loop
            c = sum(cost_of(x, groups) for x in step)
            wc = sum(wt(x) for x in step)
            if cost + c > target or wsum + wc > budget:
                break
            chain += step
            cost += c
            wsum += wc
    # fill to the target: a cheapest continuation from the top of the chain
    guard = 0
    while cost < target and guard < 10 * target:
        guard += 1
        top = chain[-1]
        nxt = [y for y in succ.get(top, []) if cost + cost_of(y, groups) <= target]
        if not nxt:
            return None
        # prefer a label that can continue (has successors), cheapest first
        nxt.sort(key=lambda y: (wt(y), cost_of(y, groups), 0 if succ.get(y) else 1, y))
        y = nxt[0]
        chain.append(y)
        cost += cost_of(y, groups)
    if cost != target:
        return None
    toks, prev = [], "top"
    for x in chain:
        toks += opener[(prev, x)]
        prev = x
    return toks + [["char", "x"]], chain


def request(toks: list) -> dict:
    return {"toks": toks, "close": True}


def adjacent(frames_innermost_first: list[str], below: str, above: str) -> bool:
    """Does the peak's frame stack hold `above` directly on `below`?"""
    f = list(reversed(frames_innermost_first))  # outermost first
    if below == "top":
        return bool(f) and f[0] == above
    return any(a == below and b == above for a, b in zip(f, f[1:]))


# ---------------------------------------------------------------- memory ---
# C-98, C-104. pdfTeX's main memory holds (i) what the format and the class
# leave at body start, (ii) the nodes the typeset material makes, a cost per
# token that depends on the construct, and (iii) a COPY of every argument a
# command is running, which an argument command nested inside another
# argument reads out of the outer copy: tokens times depth. The account over
# the model is Decide.mem: every token its c_cost, every argument's tokens its
# command's as_copy (Decide.held); it is checked, never proved, to bound
#     used(doc) <= M0 + mem(doc)
# with M0 what pdfTeX reports for a one-character document.
#
# HOW A COST IS MEASURED (C-104). pdfTeX reports a HIGH-WATER MARK, and the
# base document's already holds some 31,000 words that \begin{document}
# allocates and frees again: a document's report is max(M0, B + c * n) with
# B < M0, so the first ~31,000 words of its material are hidden under M0. C-98
# divided the report by the count (used - M0) / n, which is (B - M0)/n + c < c:
# an UNDER-count, up to 1.25x at 4,000 repetitions (the round-1 review). The
# cost is now the SLOPE of the report over the count between documents whose
# material is well past that mark (300,000 words and twice that), which is c
# exactly once both are past it, and never more than c before; the largest
# per-occurrence figure is kept as well (both are lower bounds of c).
# Every record carries pdfTeX's own report ("used"); a grade without it (a
# grade reused from a file that did not keep the statistics) is refused.

def nested(S, x: str, depth: int, inner: list) -> list:
    node = inner
    for _ in range(depth):
        node = [S.cmd(x), S.group(*node)]
    return node


def mem_build(S, x: str, where: str, unit: list, D: int, k: int, r: int, p: int) -> dict:
    """The memory worst-case document of x with D levels, k filler units
    innermost, r at the outermost level and p characters there."""
    node = nested(S, x, D - 1, unit * k)
    body = [S.cmd(x), S.group(*(unit * r), *([S.text("x" * p)] if p else []), *node)]
    return S.doc(*body) if where == "text" else S.doc(S.math("paren", *body))


def mem_maximiser(S, model, x: str, where: str, unit: list, max_groups: int,
                  max_tokens: int, max_mem: int, pchar: list | None = None) -> dict:
    """The worst case of the memory account for the argument command x run
    from `where` (text or math): as many levels of x as the group bound
    allows, the filler innermost (every innermost token is held by every
    level) and at the outermost level, then characters, as many as the
    FRAGMENT allows (the model's verdict: every bound of Decide.bounded, the
    dimension account of C-104 included). Returns the document AT the bound
    and the one with ONE more character (past it). `model` runs the extracted
    decider under the contract being attested."""
    def build(D, k, r, p):
        return mem_build(S, x, where, unit, D, k, r, p)

    def fits(d):
        m = model(d)
        return m["verdict"] != "not_strict", m

    def largest(f, hi):
        lo = 0
        if f(hi):
            return hi
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if f(mid):
                lo = mid
            else:
                hi = mid
        return lo
    D = largest(lambda d: d >= 1 and fits(build(d, 1, 0, 0))[0], max_groups)
    k = largest(lambda k: fits(build(D, k, 0, 0))[0], max_tokens)
    r = largest(lambda r: fits(build(D, k, r, 0))[0], max_tokens)
    p = largest(lambda p: fits(build(D, k, r, p))[0], max_tokens)
    at, past = build(D, k, r, p), build(D, k, r, p + 1)
    ma, mp = model(at), model(past)
    which = [b for b, over in (("mem", mp["mem"] > max_mem), ("tokens", mp["ntoks"] > max_tokens),
                               ("dim", mp.get("dim", 0) > DIM_BOUND)) if over]
    return {"at": at, "past": past, "depth": D, "inner_units": k, "outer_units": r,
            "chars": p, "mem_at": ma["mem"], "mem_past": mp["mem"],
            "dim_at": ma.get("dim"), "dim_past": mp.get("dim"), "past_over": which,
            "past_outside": mp["verdict"] == "not_strict"}


DIM_BOUND = 8000  # Decide.v max_dim (check_strict_kernel.py pins it)
# the stream builder's dimension budget: the bound less a margin for the
# innermost character and the closers (C-104)
STREAM_BUDGET = DIM_BOUND - 500


def memory_record(m: dict, g: dict | None, **extra) -> dict:
    """The primary record of one memory document: its bytes' sha256, the
    model's counts and verdict, and (graded) the oracle tuple and pdfTeX's
    own report. A grade without pdfTeX's statistics is refused (C-104: 83 of
    the C-98 bound records had none, and the gate's check skipped them)."""
    import hashlib
    r = {"sha256": hashlib.sha256(m["tex"].encode()).hexdigest(), "ntoks": m["ntoks"],
         "held": m.get("held"), "mem": m.get("mem"), "dim": m.get("dim"),
         "verdict": m["verdict"], **extra}
    if g is not None:
        st = (g.get("stats") or {}).get("main_memory")
        if not st:
            raise ValueError(f"memory record {extra}: the grade carries no pdfTeX "
                             f"statistics (a reused grade?); regrade it with stats")
        r.update({"oracle": [g["rc"], g["pdf"], g["error"], g["line"]],
                  "used": st[0], "of": st[1], "stats": g.get("stats") or {}})
    return r


def raw_record(tex: str, g: dict, **extra) -> dict:
    """The record of a memory INSTRUMENT written in TeX directly (no model
    tokens): its bytes' sha256, the oracle tuple and pdfTeX's report."""
    import hashlib
    st = (g.get("stats") or {}).get("main_memory")
    if not st:
        raise ValueError(f"instrument {extra}: no pdfTeX statistics")
    return {"sha256": hashlib.sha256(tex.encode()).hexdigest(), **extra,
            "oracle": [g["rc"], g["pdf"], g["error"], g["line"]],
            "used": st[0], "of": st[1]}


# The structural shapes: a unit of model tokens, its length; text shapes are
# the document body, math shapes one inline formula. "hyph" is a 63-letter
# word TeX hyphenates in its second line-breaking pass (discretionaries and
# passive nodes per letter); "classes" and "dclasses" put every class of
# atom the safe characters make side by side (inter-atom glue).
HYPH_WORD = "incomprehensibilities" * 3
LEVELS = (20000, 40000, 80000)


def structural_units(S) -> dict:
    t, g = S.text, S.group
    x = t("x")
    return {
        "chars": ("text", [x]), "char-space": ("text", [x, S.space()]),
        "char-par": ("text", [x, S.par()]), "group": ("text", [g(x)]),
        "inline": ("text", [S.math("dollar", x)]), "paren": ("text", [S.math("paren", x)]),
        "display": ("text", [S.math("display", x)]), "bracket": ("text", [S.math("bracket", x)]),
        "formula": ("paren", [x]), "sup": ("paren", [x, S.script(True, x)]),
        "supgroup": ("paren", [x, S.script(True, g(x))]), "mgroup": ("paren", [g(x)]),
        "classes": ("paren", [t("x=(x)+x,")]),
        "dclasses": ("bracket", [t("x=(x)+x,")]),
    }


def _ulen(unit: list) -> int:
    n = 0
    for u in unit:
        if u[0] == "text":
            n += len(u[1])
        elif u[0] == "group":
            n += 2 + _ulen(u[1])
        elif u[0] == "math":
            n += {"dollar": 2, "paren": 2, "display": 4, "bracket": 2}[u[1]] + _ulen(u[2])
        elif u[0] == "script":
            n += 1 + _ulen([u[2]])
        else:
            n += 1
    return n


def hyph_bytes(units: int) -> bytes:
    """The hyphenation instrument, as BYTES (the renderer puts a line end,
    a space, after every character, so a rendered document never holds a
    word; a file does): `units` times a 63-letter word TeX hyphenates in its
    second line-breaking pass and a space, 16 words a line."""
    words = [HYPH_WORD.encode() + b" "] * units
    lines = [b"".join(words[i:i + 16]) for i in range(0, units, 16)]
    return (b"\\documentclass{article}\n\\begin{document}\n" + b"\n".join(lines)
            + b"\n\\end{document}\n")


def structural_doc(S, name: str, units: int) -> dict:
    where, unit = structural_units(S)[name]
    body = unit * units
    return S.doc(*body) if where == "text" else S.doc(S.math(where, *body))


def structural_docs(S, level: int = LEVELS[0]) -> list[tuple[str, dict, dict]]:
    """(family, document, extra): the base, and each shape at `level` tokens
    (an instrument: graded for pdfTeX's report only)."""
    out = [("BASE", S.doc(S.text("x")), {})]
    for name, (where, unit) in structural_units(S).items():
        k = max(1, level // _ulen(unit))
        out.append((f"S:{name}@{k}", structural_doc(S, name, k), {"units": k}))
    k = level // 64
    out.append((f"S:hyph@{k}", None, {"units": k, "bytes": True}))
    return out


def more_levels(r: dict, m0: int, count: int, k1: int, cap: int) -> list[int]:
    """The two other counts of a memory instrument, from its first level's
    report (k1 occurrences): 2 k1 and 4 k1 while the largest stays under
    MEM_MAX_WORDS words of material (under half of main memory with the
    base), else lower ones. Whether the levels are past the base's
    high-water mark is checked afterwards (`absorbed_findings`): a context
    whose levels are all under it must have a cost floored at the token
    cost by the measured slack."""
    est = max(1.0, (r["used"] - m0) / count)
    for ks in ([2 * k1, 4 * k1], [k1 // 2, 2 * k1], [k1 // 4, k1 // 2]):
        if est * max(ks) <= MEM_MAX_WORDS and max(ks) <= cap:
            return [max(1, k) for k in ks]
    return [max(1, k1 // 8), max(2, k1 // 4)]


def slack(records: dict, m0: int, prefix: str) -> float:
    """The largest part of the base's high-water mark a document's material
    can hide: over every context of `records` (families `{prefix}...@level`)
    whose two largest levels both report more than the base, M0 minus the
    intercept of the line through them (the memory the report would show
    with no material, in the linear regime)."""
    out = 0.0
    for ctx, rs in _levels(records, prefix).items():
        rs = [r for r in rs if _ok(r)]
        if len(rs) < 2:
            continue
        a, b = rs[-2], rs[-1]
        if a["used"] <= m0:
            continue
        xa, xb = (a.get("count") or a.get("units") or a["ntoks"]), \
            (b.get("count") or b.get("units") or b["ntoks"])
        c = (b["used"] - a["used"] + GRAIN) / (xb - xa)
        out = max(out, m0 - (a["used"] - c * xa))
    return out


def absorbed_findings(records: dict, m0: int, prefix: str, sl: float, cost: int,
                      per_token: bool = False) -> list[str]:
    """C-104: a context whose second-largest level reports only the base (its
    material hidden under the high-water mark) proves only that its memory
    per occurrence (per token, for the structural shapes) is at most slack /
    count: the cost charged must be above that."""
    out = []
    for ctx, rs in _levels(records, prefix).items():
        if len(rs) < 2:
            continue
        a = rs[-2]
        if a["used"] > m0:
            continue
        n = a["ntoks"] if per_token else (a.get("count") or a.get("units"))
        if not sl / n < cost - 1:
            out.append(f"{prefix}{ctx}: its levels are under the base's high-water mark "
                       f"and slack {sl:.0f} / {n} is not under the cost {cost}")
    return out


# pdfTeX grows its variable-size memory 1,000 words at a time (tex.web
# "Grow more variable-size memory"), so a report is up to that much above
# the words in use: every slope is taken with the difference of two reports
# widened by it (an upper bound; the lower one where a slope is subtracted).
GRAIN = 1000
MEM_PAST_HW = 300000
MEM_MAX_WORDS = 1800000


def _ok(r: dict) -> bool:
    o = r.get("oracle")
    return bool(o) and o[0] == 0 and o[1] and r.get("used") is not None


def _levels(recs: dict, prefix: str) -> dict[str, list[dict]]:
    """{context: [records by increasing count]} of the families
    `{prefix}{context}@{level}`."""
    by: dict[str, list[dict]] = {}
    for f, r in recs.items():
        if f.startswith(prefix) and "@" in f:
            by.setdefault(f[len(prefix):].split("@")[0], []).append(r)
    return {k: sorted(v, key=lambda r: r.get("count") or r.get("units") or r["ntoks"])
            for k, v in by.items()}


def token_cost(structural: dict) -> int:
    """The most memory per token any structural shape takes: over every
    shape, the slope of pdfTeX's report over the tokens between consecutive
    levels and the per-token report over the base at every level, rounded
    up, plus one. Every level must have compiled with its report (a shape
    that does not is a finding, never skipped)."""
    import math
    m0 = structural["BASE"]["used"]
    vals = []
    for ctx, rs in _levels(structural, "S:").items():
        for r in rs:
            if not _ok(r):
                raise ValueError(f"structural shape {ctx}: a level did not compile")
            vals.append((r["used"] - m0) / r["ntoks"])
        for a, b in zip(rs, rs[1:]):
            vals.append((b["used"] - a["used"] + GRAIN) / (b["ntoks"] - a["ntoks"]))
    return math.ceil(max(vals)) + 1


def _per(r: dict, m0: int, tcost: int) -> float:
    return (r["used"] - m0 - tcost * (r["ntoks"] - r["count"])) / r["count"]


def _slope(a: dict, b: dict, tcost: int) -> float:
    return (((b["used"] - a["used"] + GRAIN) - tcost * ((b["ntoks"] - b["count"])
                                                 - (a["ntoks"] - a["count"])))
            / (b["count"] - a["count"]))


def name_base_cost(recs: dict, m0: int, tcost: int) -> int | None:
    """A name's measured memory per occurrence from its repetition documents
    `R-MEM-{context}@{level}` (the other tokens charged the token cost): the
    largest slope between consecutive levels of a context, and the largest
    per-occurrence figure, rounded up, plus one. None when it has none; a
    level that did not compile is refused."""
    import math
    vals = []
    for ctx, rs in _levels(recs, "R-MEM-").items():
        for r in rs:
            if not _ok(r):
                raise ValueError(f"memory context {ctx}: a level did not compile")
            vals.append(_per(r, m0, tcost))
        for a, b in zip(rs, rs[1:]):
            vals.append(_slope(a, b, tcost))
    return math.ceil(max(vals)) + 1 if vals else None


def name_cost(recs: dict, m0: int, tcost: int, letters: int, atoms: int,
              boundary: dict) -> int | None:
    """The name's cost (Contract.v c_cost): its base cost, plus the memory
    of the boundaries it can make with ANY neighbour, which no repetition of
    the name alone shows: per letter it prints in text, a letter's memory in
    a word TeX hyphenates (H_text); per atom it makes in math, the largest
    inter-atom excess over the eight classes (B_math). At least the token
    cost."""
    b = name_base_cost(recs, m0, tcost)
    if b is None:
        return None
    return max(tcost, b + letters * boundary["H_text"] + atoms * boundary["B_math"])


def boundary_constants(structural: dict, pairs: dict) -> dict:
    """H_text: the per-token slope of the hyphenated-word shape, rounded up;
    B_math: over the class-pair instruments `CP:{a}.{b}@{level}` (units of
    two atoms), the largest excess of a pair's slope per unit over the mean of
    its two classes' own, rounded up (0 if none exceeds)."""
    import math
    rs = _levels(structural, "S:")["hyph"]
    h = max((b["used"] - a["used"] + GRAIN) / (b["ntoks"] - a["ntoks"])
            for a, b in zip(rs, rs[1:]))
    sl = {}
    for ctx, rr in _levels(pairs, "CP:").items():
        for r in rr:
            if not _ok(r):
                raise ValueError(f"class pair {ctx}: a level did not compile")
        # (an upper and a lower slope: the excess is taken at its largest)
        sl[ctx] = (max((b["used"] - a["used"] + GRAIN) / (b["units"] - a["units"])
                       for a, b in zip(rr, rr[1:])),
                   min((b["used"] - a["used"] - GRAIN) / (b["units"] - a["units"])
                       for a, b in zip(rr, rr[1:])))
    ex = [0.0]
    for ctx, s in sl.items():
        a, b = ctx.split(".")
        ex.append(s[0] - (sl[f"{a}.{a}"][1] + sl[f"{b}.{b}"][1]) / 2)
    return {"H_text": math.ceil(h), "B_math": math.ceil(max(ex))}


def class_pair_docs(levels=(8000, 16000)) -> list[tuple[str, str, dict]]:
    """(family, TeX, extra): two atoms of the given classes, repeated, in a
    display-style formula (instruments; the spacing of the display and text
    styles is the largest)."""
    from itertools import product
    classes = ("mathord", "mathop", "mathbin", "mathrel", "mathopen", "mathclose",
               "mathpunct", "mathinner")
    out = []
    for a, b in product(classes, classes):
        for L in levels:
            unit = f"\\{a}{{x}}\\{b}{{x}}"
            lines = "\n".join(unit * 20 for _ in range(L // 20))
            tex = ("\\documentclass{article}\n\\begin{document}\n$\\displaystyle\n"
                   + lines + "\n$\n\\end{document}\n")
            out.append((f"CP:{a}.{b}@{L}", tex, {"units": L}))
    return out


def copy_and_cost(recs: dict, m0: int, tcost: int) -> dict:
    """An argument command's copy factor and cost from stage G's memory
    documents, per mode: FLAT@k / FLATX@k (the command with an empty /
    one-character argument, repeated, at two or more counts: the SLOPE per
    occurrence, C-104), SHALLOW / DEEP / DEEP-HALF (the same characters inside
    2 and D levels, and half of them inside D): the copy factor is the slope
    over the tokens held (raw held, factor 1), the per-level memory the rest;
    the cost is the larger of the flat cost per occurrence and the per-level
    memory, rounded up, plus one."""
    import math
    slope, levels, flat = [], [], []
    for w in ("text", "math"):
        sh, dp, hf = (recs.get(f"G-MEM-{k}:{w}") for k in ("SHALLOW", "DEEP", "DEEP-HALF"))
        for r in (sh, dp, hf):
            if r is not None and not _ok(r):
                raise ValueError(f"stage G memory document {w} did not compile")
        if sh and dp and hf:
            W = (dp["used"] - hf["used"] + GRAIN) / (dp["held"] - hf["held"])
            slope.append(W)
            levels.append((dp["used"] - sh["used"] + GRAIN - W * (dp["held"] - sh["held"]))
                          / (dp["depth"] - sh["depth"]))
        for k in ("FLAT", "FLATX"):
            rs = sorted((r for f, r in recs.items() if f.startswith(f"G-MEM-{k}:{w}@")),
                        key=lambda r: r["count"])
            for r in rs:
                if not _ok(r):
                    raise ValueError(f"stage G {k} {w}: a level did not compile")
                flat.append(_per(r, m0, tcost))
            for a, b in zip(rs, rs[1:]):
                flat.append(_slope(a, b, tcost))
    if not slope:
        return {"copy": None, "cost": None}
    # a cost below one word (the braces of an empty argument are already
    # charged a token's cost each) is one word
    return {"copy": math.ceil(max(slope)), "cost": max(1, math.ceil(max(flat + levels)) + 1),
            "slope": round(max(slope), 4), "per_level": round(max(levels), 1),
            "flat": round(max(flat), 1) if flat else None}


# ----------------------------------------- the phase-1 memory documents ------
# Written once here: the generator builds them, the binary gate
# (check_strict_capacity.py) rebuilds them from the recorded family and count
# and requires the recorded bytes and model counts to be the extracted model's.

MEM_CONTEXTS = ("TEXT", "MATH", "DISPLAY", "MSCRIPT", "DSCRIPT")


# A display's material is ONE box: past 2^31 sp its width wraps and the run
# may stop ("Dimension too large", C-104), so a display instrument holds at
# most DISPLAY_WIDTH points of the name (by the account) and reaches past the
# base's high-water mark with a BALLAST of empty math groups before it (Ord
# atoms with no width), the same at every level: the slope over the levels is
# the name's alone. (A display inside the fragment holds at most 8,000 points
# of material anyway.)
BALLAST = 4000
DISPLAY_WIDTH = 12000


def display_levels(unit_dim: int, cap: int) -> list[int]:
    """Three counts of a display instrument whose unit has `unit_dim` points
    in math."""
    k3 = min(cap, DISPLAY_WIDTH // unit_dim) if unit_dim > 0 else min(cap, 20000)
    return sorted({max(1, k3 // 4), max(2, k3 // 2), max(3, k3)})


def name_mem_doc(S, x: str, ctx: str, k: int) -> dict:
    """`R-MEM-{ctx}@{k}`: the name k times in text (then a character), in a
    formula, in a display (after the ballast), and with a super- and a
    subscript each time in a formula and in a display (after the ballast)."""
    c = S.cmd(x)
    unit = [c, S.script(True, S.text("x")), S.script(False, S.text("x"))]
    ballast = [S.group()] * BALLAST
    if ctx == "TEXT":
        return S.doc(*([c] * k), S.text("x"))
    if ctx == "MATH":
        return S.doc(S.math("paren", *([c] * k)))
    if ctx == "DISPLAY":
        return S.doc(S.math("bracket", *ballast, *([c] * k)))
    if ctx == "MSCRIPT":
        return S.doc(S.math("paren", *(unit * k)))
    if ctx == "DSCRIPT":
        return S.doc(S.math("bracket", *ballast, *(unit * k)))
    raise ValueError(ctx)


def cap_doc(S, dims, x: str, where: str, k: int) -> dict:
    """`R-CAP-{where}` with count k: the name k times, cut within the
    dimension bound (paragraphs; in math, formulas) by `dims.segment`."""
    c = S.cmd(x)
    if where == "TEXT":
        return dims.segment(S, S.doc(*([c] * k), S.text("x")))
    return dims.segment(S, S.doc(S.math("paren", *([c] * k))))


def dim_doc(S, x: str, where: str, k: int) -> dict:
    """`R-DIM-{where}` with count k: one paragraph, formula or display of the
    name k times (the dimension bound's document)."""
    c = S.cmd(x)
    if where == "TEXT":
        return S.doc(*([c] * k))
    if where == "MATH":
        return S.doc(S.math("paren", *([c] * k)))
    return S.doc(S.math("bracket", *([c] * k)))


def review_docs(S) -> list[tuple[str, str, dict]]:
    """The round-1 review's memory documents (C-104): (family, name, doc)."""
    c, x = S.cmd, S.text("x")
    return [
        ("R-REVIEW-ttdefault-math", "ttdefault", S.doc(S.math("paren", *[c("ttdefault")] * 19000))),
        ("R-REVIEW-indexname-math", "indexname", S.doc(S.math("paren", *[c("indexname")] * 6000))),
        ("R-REVIEW-sum-limits", "sum", S.doc(S.math("bracket", *[
            n for _ in range(3999) for n in (c("sum"), S.script(True, x), S.script(False, x))]))),
        ("R-REVIEW-lim-sub", "lim", S.doc(S.math("bracket", *[
            n for _ in range(6665) for n in (c("lim"), S.script(False, x))]))),
        ("R-REVIEW-sum-sub", "sum", S.doc(S.math("bracket", *[
            n for _ in range(6665) for n in (c("sum"), S.script(False, x))]))),
    ]
