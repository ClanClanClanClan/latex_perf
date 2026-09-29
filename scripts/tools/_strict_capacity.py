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
