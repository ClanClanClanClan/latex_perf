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


def _path(succ: dict, src: str, dst: str) -> list[str] | None:
    """A shortest label path of at least one pair from src to dst (both
    included), or None."""
    q, seen = deque([(src, [src])]), {src}
    while q:
        x, p = q.popleft()
        for y in succ.get(x, []):
            if y == dst:
                return p + [y]
            if y not in seen:
                seen.add(y)
                q.append((y, p + [y]))
    return None


def stream(pairs: dict, below: str, above: str, target: int, groups: dict
           ) -> tuple[list, list[str]] | None:
    """A token stream (strict_decide.exe JSON tokens, to be closed with
    "close": true) whose frame stack peaks at exactly `target` groups, made
    of the pair (below, above) repeated; and its label chain. None when the
    pair cannot be reached or `target` cannot be met exactly."""
    succ, opener = graph(pairs)
    pre = ["top"] if below == "top" else _path(succ, "top", below)
    if pre is None:
        return None
    # a cycle through the pair: above ... below
    back = _path(succ, above, below) if below != "top" else None
    chain = pre[1:] + [above]
    cost = sum(cost_of(x, groups) for x in chain)
    if cost > target:
        return None
    if back is not None:
        loop = back[1:] + [above]  # ... below, above
        while True:
            step = loop
            c = sum(cost_of(x, groups) for x in step)
            if cost + c > target:
                break
            chain += step
            cost += c
    # fill to the target: a cheapest continuation from the top of the chain
    guard = 0
    while cost < target and guard < 10 * target:
        guard += 1
        top = chain[-1]
        nxt = [y for y in succ.get(top, []) if cost + cost_of(y, groups) <= target]
        if not nxt:
            return None
        # prefer a label that can continue (has successors), cheapest first
        nxt.sort(key=lambda y: (cost_of(y, groups), 0 if succ.get(y) else 1, y))
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
# C-98. pdfTeX's main memory holds (i) what the format and the class leave
# at body start, (ii) the nodes the typeset material makes, a cost per token
# that depends on the construct, and (iii) a COPY of every argument a command
# is running, which an argument command nested inside another argument reads
# out of the outer copy: tokens times depth. The account over the model is
#     used(doc) <= M0 + A * ntoks + W * held
# (Decide.held; ntoks the model's tokens), with A the most node memory per
# token any construct of the fragment makes, anywhere, and W the most memory
# per held token any argument command costs, each MEASURED by a maximiser
# over every admitted name and command and every structural shape. The
# families below are the maximiser's documents; measure_strict_capacity.py
# grades them, and check_strict_kernel.py recomputes A, W and the account
# from the per-document records.

def _flat(unit: list, per: int, total: int) -> list:
    return unit * max(1, (total - 1) // per)


def memory_survey(S, sigs: dict, asigs: dict, total: int) -> list[tuple[str, dict]]:
    """(family, document): each construct repeated to the token bound, in
    text, in math, and inside one box argument (nodes kept until the box
    closes); structural shapes likewise."""
    t, g, c = S.text, S.group, S.cmd
    x = t("x")
    dollar = lambda *b: S.math("dollar", *b)  # noqa: E731
    paren = lambda *b: S.math("paren", *b)  # noqa: E731
    box = sorted(n for n, h in asigs.items() if h["text"][0] == "run"
                 and h["text"][2] == "text_restricted" and h["text"][3] == 1)
    out = []
    shapes = {
        "chars": ([x], 1), "char-space": ([x, S.space()], 2),
        "char-par": ([x, S.par()], 2), "group": ([g(x)], 3),
        "inline": ([dollar(x)], 3), "paren": ([paren(x)], 3),
        "display": ([S.math("display", x)], 5), "bracket": ([S.math("bracket", x)], 3),
    }
    for name, (unit, per) in shapes.items():
        out.append((f"MEM-S:{name}", S.doc(*_flat(unit, per, total))))
        if box and name not in ("char-par", "display", "bracket"):
            out.append((f"MEM-SB:{name}", S.doc(c(box[0]), g(*_flat(unit, per, total - 3)))))
    math_shapes = {
        "formula": ([x], 1), "sup": ([x, S.script(True, x)], 3),
        "supgroup": ([x, S.script(True, g(x))], 5), "mgroup": ([g(x)], 3),
    }
    for name, (unit, per) in math_shapes.items():
        out.append((f"MEM-SM:{name}", S.doc(paren(*_flat(unit, per, total - 2)))))
    for n, h in sorted(sigs.items()):
        if not isinstance(h["text"], list):
            out.append((f"MEM-T:{n}", S.doc(*_flat([c(n)], 1, total - 1), x)))
            if box:
                out.append((f"MEM-TB:{n}", S.doc(c(box[0]), g(*_flat([c(n)], 1, total - 4)))))
        if not isinstance(h["math"], list):
            out.append((f"MEM-M:{n}", S.doc(paren(*_flat([c(n)], 1, total - 2)))))
    for n, h in sorted(asigs.items()):
        if h["text"][0] == "run":
            out.append((f"MEM-A:{n}", S.doc(*_flat([c(n), g()], 3, total))))
            out.append((f"MEM-AX:{n}", S.doc(*_flat([c(n), g(x)], 4, total))))
        if h["math"][0] == "run":
            out.append((f"MEM-AM:{n}", S.doc(paren(*_flat([c(n), g()], 3, total - 2)))))
    return out


def nested(S, x: str, depth: int, inner: list) -> list:
    node = inner
    for _ in range(depth):
        node = [S.cmd(x), S.group(*node)]
    return node


def held_slopes(S, asigs: dict, max_groups: int) -> list[tuple[str, dict]]:
    """For each argument command and mode, the same 5,000 characters inside
    few and many levels of the command: the memory per held token is the
    slope (the documents differ only in the copies)."""
    out = []
    inner = [S.text("x" * 5000)]
    for n, h in sorted(asigs.items()):
        for w, mk in (("text", lambda b: S.doc(*b)),
                      ("math", lambda b: S.doc(S.math("paren", *b)))):
            if h[w][0] != "run":
                continue
            g = h[w][3] if w == "text" else h[w][2]
            gi = max(h["text"][3] if h["text"][0] == "run" else 1, g, 1)
            deep = max(2, (max_groups - 2) // gi)
            for d in (2, deep):
                out.append((f"MEM-H:{n}/{w}@{d}", mk(nested(S, n, d, inner))))
    return out


def mem_build(S, x: str, where: str, unit: list, D: int, k: int, r: int, p: int) -> dict:
    """The memory worst-case document of x with D levels, k filler units
    innermost, r at the outermost level and p characters there."""
    node = nested(S, x, D - 1, unit * k)
    body = [S.cmd(x), S.group(*(unit * r), *([S.text("x" * p)] if p else []), *node)]
    return S.doc(*body) if where == "text" else S.doc(S.math("paren", *body))


def mem_maximiser(S, model, x: str, where: str, unit: list, max_groups: int,
                  max_tokens: int, max_mem: int) -> dict:
    """The worst case of the memory account for the argument command x run
    from `where` (text or math): as many levels of x as the group bound
    allows, the costliest filler innermost (every innermost token is held by
    every level) and at the outermost level, then characters, as many as the
    account (Decide.mem <= max_mem) and the token bound allow. Returns the
    document AT the bound and the one with ONE more character (past it).
    `model` runs the extracted decider under the contract being attested."""
    def build(D, k, r, p):
        return mem_build(S, x, where, unit, D, k, r, p)

    def fits(d):
        m = model(d)
        return m["mem"] <= max_mem and m["ntoks"] <= max_tokens - 2 and \
            m["peak_groups"] <= max_groups, m

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
    return {"at": at, "past": past, "depth": D, "inner_units": k, "outer_units": r,
            "chars": p, "mem_at": ma["mem"], "mem_past": mp["mem"],
            "past_outside": mp["verdict"] == "not_strict"}


# ---------------------------------------------- measured costs (C-98) -------
# Every cost of Contract.v c_cost / as_copy is derived here, from primary
# records (the graded document's sha256, its model counts, pdfTeX's reported
# memory), by the generators AND again by check_strict_kernel.py.

def memory_record(m: dict, g: dict | None, **extra) -> dict:
    import hashlib
    r = {"sha256": hashlib.sha256(m["tex"].encode()).hexdigest(), "ntoks": m["ntoks"],
         "held": m.get("held"), "mem": m.get("mem"), "verdict": m["verdict"], **extra}
    if g is not None:
        st = (g.get("stats") or {}).get("main_memory")
        r.update({"oracle": [g["rc"], g["pdf"], g["error"], g["line"]],
                  "used": st[0] if st else None, "of": st[1] if st else None,
                  "stats": g.get("stats") or {}})
    return r


def structural_docs(S, total: int) -> list[tuple[str, dict]]:
    t, g = S.text, S.group
    x = t("x")
    shapes = {
        "chars": ([x], 1), "char-space": ([x, S.space()], 2),
        "char-par": ([x, S.par()], 2), "group": ([g(x)], 3),
        "inline": ([S.math("dollar", x)], 3), "paren": ([S.math("paren", x)], 3),
        "display": ([S.math("display", x)], 5), "bracket": ([S.math("bracket", x)], 3),
    }
    out = [("BASE", S.doc(x))]
    for name, (unit, per) in shapes.items():
        out.append((f"S:{name}", S.doc(*(unit * ((total - 1) // per)))))
    maths = {"formula": ([x], 1), "sup": ([x, S.script(True, x)], 3),
             "supgroup": ([x, S.script(True, g(x))], 5), "mgroup": ([g(x)], 3)}
    for name, (unit, per) in maths.items():
        out.append((f"SM:{name}", S.doc(S.math("paren", *(unit * ((total - 3) // per))))))
    return out


def _ok(r: dict) -> bool:
    o = r.get("oracle")
    return bool(o) and o[0] == 0 and o[1] and r.get("used") is not None


def token_cost(structural: dict) -> int:
    """The most memory per token any structural shape takes over the base,
    rounded up, plus one."""
    import math
    m0 = structural["BASE"]["used"]
    worst = max((r["used"] - m0) / r["ntoks"] for f, r in structural.items()
                if f != "BASE" and _ok(r))
    return math.ceil(worst) + 1


def name_cost(records: list[dict], m0: int, tcost: int) -> int | None:
    """A name's cost from its repetition documents: the most memory per
    occurrence over the base and the other tokens' cost, rounded up, plus one
    (None when no document of it compiled)."""
    import math
    xs = [(r["used"] - m0 - tcost * (r["ntoks"] - r["count"])) / r["count"]
          for r in records if _ok(r) and r.get("count")]
    return math.ceil(max(xs)) + 1 if xs else None


def copy_and_cost(recs: dict, m0: int, tcost: int) -> dict:
    """An argument command's copy factor and cost from stage G's memory
    documents, per mode: FLAT (the command with an empty / one-character
    argument, repeated: cost per occurrence), SHALLOW / DEEP / DEEP-HALF (the
    same characters inside 2 and D levels, and half of them inside D): the
    copy factor is the slope over the tokens held (raw held, factor 1), the
    per-level memory the rest; the cost is the larger of the flat cost per
    occurrence and the per-level memory, rounded up, plus one."""
    import math
    slope, levels, flat = [], [], []
    for w in ("text", "math"):
        sh, dp, hf = (recs.get(f"G-MEM-{k}:{w}") for k in ("SHALLOW", "DEEP", "DEEP-HALF"))
        if sh and dp and hf and _ok(sh) and _ok(dp) and _ok(hf):
            W = (dp["used"] - hf["used"]) / (dp["held"] - hf["held"])
            slope.append(W)
            levels.append((dp["used"] - sh["used"] - W * (dp["held"] - sh["held"]))
                          / (dp["depth"] - sh["depth"]))
        for k in ("FLAT", "FLATX"):
            r = recs.get(f"G-MEM-{k}:{w}")
            if r and _ok(r):
                flat.append((r["used"] - m0 - tcost * (r["ntoks"] - r["count"])) / r["count"])
    if not slope:
        return {"copy": None, "cost": None}
    return {"copy": math.ceil(max(slope)), "cost": math.ceil(max(flat + levels)) + 1,
            "slope": round(max(slope), 4), "per_level": round(max(levels), 1),
            "flat": round(max(flat), 1) if flat else None}
