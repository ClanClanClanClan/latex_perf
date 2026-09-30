"""The DIMENSION account of the strict fragment (correction C-104).

Shared by gen_strict_signatures.py and gen_strict_arg_signatures.py (which
MEASURE it) and check_strict_kernel.py (which RE-DERIVES it from the recorded
primary data: TeX's own box dumps and the fonts' character dimensions).

WHY. TeX stores a dimension as a signed 32-bit count of sp (2^31 sp is
32,768pt) and adds widths without an overflow check (tex.web hpack). The
round-1 review's document, a display of 3,277 \\quad (32,770pt), wraps to a
negative width, skips the squeeze of §1199 and makes LaTeX's shipout stop
with "! Dimension too large"; it was PROVEN-READY. Scanning any dimension of
16,384pt or more (max_dimen) is also an error.

THE ACCOUNT (Decide.v [dim], Contract.v [c_dim]). Every dimension pdfTeX
computes while it typesets one paragraph is a sum, each term with a
coefficient of at most one, of dimensions of the nodes the paragraph's tokens
make (widths, heights, depths and shifts of boxes, rules and characters;
natural width, stretch and shrink of glue; kerns), plus constants of the
layout (\\hsize for a line or \\centerline box, a display's centring): an
hbox's width is the sum of its items' widths, its height the largest item's;
a vbox's height the sum; a glue's setting at most the box's target plus its
natural width; a script's shift at most its nucleus's height plus a font
constant; a limit's width the largest of the operator's and the limits'. So
if each token is charged at least the absolute sum of the dimensions of the
nodes IT makes (its own glyphs, glue, kerns, rules, and the constant parts of
the boxes it builds), plus what TeX inserts at its boundary with the previous
token (a kern or ligature in text; one inter-atom spacing per atom in math),
then every such dimension is at most the segment's sum plus the constants.

MEASURED, per token and per mode:
- INV(t): TeX's own dump (\\showbox, depth and breadth unlimited) of
  \\hbox{t} in text and of \\hbox{$\\<style> t$} in each of the four math
  styles; the sum over EVERY node of the dump, nested boxes included, of
  |w|+|h|+|d|+|shift| (boxes, rules), |w|+|stretch|+|shrink| (glue, every
  order counted at its raw value), |kern|, the math nodes' surround, and a
  character's width+height+depth (\\fontcharwd/ht/dp of its font, read by a
  second run). Minus the same sum for the empty context.
- the boundary constants: B_text, the largest INV(ab) - INV(a) - INV(b) over
  every ordered pair of the text items (every character code 0-127 of the
  text font, every safe character, every name and command run in text:
  kerns and ligatures); B_math, the same over every pair of math items (every
  safe character, every name and command run in math, a math group, and the
  eight atom classes), in the display and text styles (the largest spacings).
- atoms(t): the noads t appends (TeX's \\showlists of the math list).
c_dim(t) = ceil(INV_text(t) + B_text) in text, ceil(max over styles of
INV_style(t) + atoms(t) * B_math) in math; 0 in a mode where t stops pdfTeX.
"""
from __future__ import annotations

import math
import re
from pathlib import Path

SHOWPRE = r"\showboxdepth=2147483647 \showboxbreadth=2147483647 "
STYLES = ("displaystyle", "textstyle", "scriptstyle", "scriptscriptstyle")
SCRIPT_OF = {"displaystyle": "scriptstyle", "textstyle": "scriptstyle",
             "scriptstyle": "scriptscriptstyle", "scriptscriptstyle": "scriptscriptstyle"}
HEAD = "\\documentclass{article}\n\\begin{document}\n"
CLASSES = ("mathord", "mathop", "mathbin", "mathrel", "mathopen", "mathclose",
           "mathpunct", "mathinner")
NOAD_WORDS = ("mathord", "mathop", "mathbin", "mathrel", "mathopen", "mathclose",
              "mathpunct", "mathinner", "overline", "underline", "vcenter", "radical",
              "accent", "left", "middle", "right", "fraction")


class DumpError(Exception):
    pass


def box_doc(items: list[str], pre: str = "", post: str = "") -> str:
    """A document whose box 0 holds one \\hbox per item, dumped by \\showbox
    (the run then stops: the dump is in the log). `post` runs after the box
    is set (the fonts of every item are then loaded)."""
    body = "".join("\\hbox{" + it + "}%\n" for it in items)
    return (HEAD + SHOWPRE + pre + "%\n\\setbox0\\hbox{%\n" + body + "}%\n"
            + post + "\\showbox0\n\\end{document}\n")


def lists_doc(items: list[str], style: str = "displaystyle") -> str:
    """A document that shows the math list of the items, each after a marker
    penalty (\\showlists, before the list is converted: the noads)."""
    body = "".join(f"\\penalty{i + 1} " + it + "%\n" for i, it in enumerate(items))
    return (HEAD + SHOWPRE + "%\n\\setbox0\\hbox{$\\" + style + "%\n" + body
            + "\\showlists$}\n\\end{document}\n")


# ------------------------------------------------------------ the dump ------

_NUM = r"-?\d+(?:\.\d+)?"
_BOX = re.compile(rf"^\\([hv])box\(({_NUM})\+({_NUM})\)x({_NUM})(.*)$")
_RULE = re.compile(r"^\\rule\(([-\d.*]+)\+([-\d.*]+)\)x([-\d.*]+)$")
_GLUE = re.compile(rf"^\\glue(?:\(\\[A-Za-z]+\))? ({_NUM})(?: plus ({_NUM})(?:fil+)?)?"
                   rf"(?: minus ({_NUM})(?:fil+)?)?$")
_KERN = re.compile(rf"^\\kern ?({_NUM})(?: \(for accent\))?$")
_MATH = re.compile(rf"^\\math(?:on|off)(?:, surrounded ({_NUM}))?$")
_PEN = re.compile(r"^\\penalty -?\d+$")
_DISC = re.compile(r"^\\discretionary(?: replacing \d+)?$")
# a character node: the font identifier, a space, the character as
# print_ASCII prints it (the format's translation makes most codes print as
# the raw byte, whitespace included: code 10 is a raw line feed, so the node
# line ends right after the space and the log has an empty line after it),
# then possibly " (ligature ...)"
_CHAR = re.compile(r"^\\([A-Za-z0-9]+/[^ ]+) (\^\^[0-9a-f]{2}|\^\^.|.|)(?: \(ligature .*\))?$",
                   re.DOTALL)
_SHIFT = re.compile(rf", shifted ({_NUM})")


def char_code(s: str) -> int:
    """The code of a character as TeX prints it (print_ASCII)."""
    if s == "":
        return 10
    if len(s) == 1:
        return ord(s)
    if s.startswith("^^") and len(s) == 4:
        return int(s[2:], 16)
    if s.startswith("^^") and len(s) == 3:
        c = ord(s[2])
        return c + 64 if c < 64 else c - 64
    raise DumpError(f"unreadable character {s!r}")


def dump_lines(log: str, which: str = "\\box0=") -> list[str]:
    """The lines of TeX's dump of box 0 (after '> \\box0=' up to the '! OK.')."""
    i = log.find("> " + which)
    if i < 0:
        raise DumpError("no box dump in the log (the run stopped before \\showbox)")
    out = []
    for line in log[i:].split("\n")[1:]:
        if line.startswith("! "):
            break
        if line.strip() == "":
            continue
        out.append(line)
    return out


def _depth(line: str) -> tuple[int, str]:
    k = 0
    while k < len(line) and line[k] in ".|":
        k += 1
    return k, line[k:]


def items_of(lines: list[str]) -> list[list[tuple[int, str]]]:
    """The dump of box 0 split into its children (depth 1): each a list of
    (depth, node) with the child's own box line first."""
    d0, first = _depth(lines[0])
    if d0 != 0 or not first.startswith("\\hbox"):
        raise DumpError(f"the dump does not start with box 0: {lines[0]!r}")
    out: list[list[tuple[int, str]]] = []
    for line in lines[1:]:
        d, node = _depth(line)
        if d == 1:
            out.append([(d, node)])
        elif d > 1 and out:
            out[-1].append((d, node))
        else:
            raise DumpError(f"unexpected dump line {line!r}")
    return out


def fonts_chars(items: list[list[tuple[int, str]]]) -> set[tuple[str, int]]:
    """Every (font, code) the dump's character nodes use."""
    out = set()
    for it in items:
        for _, node in it:
            m = _CHAR.match(node)
            if m and not _BOX.match(node) and not node.startswith("\\glue"):
                out.add((m.group(1), char_code(m.group(2))))
    return out


def chardims_post(pairs: list[tuple[str, int]]) -> str:
    """TeX code that types out each (font, code)'s width, height and depth."""
    out = []
    for i, (f, c) in enumerate(pairs):
        cs = f"\\csname {f}\\endcsname"
        out.append(f"\\typeout{{CHD:{i}:\\the\\fontcharwd{cs} {c} :"
                   f"\\the\\fontcharht{cs} {c} :\\the\\fontchardp{cs} {c} }}%\n")
    return "".join(out)


def parse_chardims(log: str, pairs: list[tuple[str, int]]) -> dict:
    got = {}
    for m in re.finditer(r"CHD:(\d+):(-?[\d.]+)pt:(-?[\d.]+)pt:(-?[\d.]+)pt", log):
        f, c = pairs[int(m.group(1))]
        got[f"{f}|{c}"] = [float(m.group(2)), float(m.group(3)), float(m.group(4))]
    if len(got) != len(pairs):
        raise DumpError(f"character dimensions: {len(got)} of {len(pairs)} typed out")
    return got


def node_value(node: str, chardims: dict) -> float:
    """The absolute dimensions of one node of a dump (see the module doc)."""
    m = _BOX.match(node)
    if m:
        s = _SHIFT.search(m.group(5))
        return (abs(float(m.group(2))) + abs(float(m.group(3))) + abs(float(m.group(4)))
                + (abs(float(s.group(1))) if s else 0.0))
    m = _RULE.match(node)
    if m:
        return sum(abs(float(x)) for x in m.groups() if x != "*")
    m = _GLUE.match(node)
    if m:
        return sum(abs(float(x)) for x in m.groups() if x is not None)
    m = _KERN.match(node)
    if m:
        return abs(float(m.group(1)))
    m = _MATH.match(node)
    if m:
        return abs(float(m.group(1))) if m.group(1) else 0.0
    if _PEN.match(node) or _DISC.match(node):
        return 0.0
    m = _CHAR.match(node)
    if m:
        k = f"{m.group(1)}|{char_code(m.group(2))}"
        if k not in chardims:
            raise DumpError(f"no dimensions for character {k}")
        return sum(abs(x) for x in chardims[k])
    raise DumpError(f"a node the account does not know: {node!r}")


def inv(item: list[tuple[int, str]], chardims: dict) -> tuple[float, int]:
    """(the sum over every node of an item, the item's own box excluded;
    the number of nodes)."""
    nodes = item[1:]
    return sum(node_value(n, chardims) for _, n in nodes), len(nodes)


def top_nodes(item: list[tuple[int, str]]) -> list[str]:
    return [n for d, n in item[1:] if d == 2]


def measure_boxes(run, items: list[str]) -> dict:
    """Run the two instruments for `items` (`run(tex) -> log text`): the box
    dump, then the character dimensions of every font and code it uses.
    Returns the primary record: the dump lines of each item, and the
    character table."""
    tex1 = box_doc(items)
    log1 = run(tex1)
    its = items_of(dump_lines(log1))
    if len(its) != len(items):
        raise DumpError(f"the dump holds {len(its)} boxes for {len(items)} items")
    pairs = sorted(fonts_chars(its))
    tex2 = box_doc(items, post=chardims_post(pairs))
    log2 = run(tex2)
    cd = parse_chardims(log2, pairs)
    return {"items": items, "dumps": [[f"{d}|{n}" for d, n in it] for it in its],
            "chardims": cd, "tex_sha256": [_sha(tex1), _sha(tex2)]}


def _sha(s: str) -> str:
    import hashlib
    return hashlib.sha256(s.encode()).hexdigest()


def record_items(rec: dict) -> list[list[tuple[int, str]]]:
    out = []
    for it in rec["dumps"]:
        rows = []
        for x in it:
            d, n = x.split("|", 1)
            rows.append((int(d), n))
        out.append(rows)
    return out


def invs(rec: dict) -> dict[str, tuple[float, int]]:
    """{item: (INV, nodes)} of a measurement record (re-derived from its
    dump lines and character table: the gate calls this)."""
    its = record_items(rec)
    return {src: inv(it, rec["chardims"]) for src, it in zip(rec["items"], its)}


# ---------------------------------------------------------- the noads -------

def parse_lists(log: str, n: int) -> list[int]:
    """The number of noads each of the n items appended (TeX's \\showlists of
    the math list, split at the marker penalties). A \\mathchoice counts the
    largest of its four branches."""
    i = log.find("### math mode entered")
    if i < 0:
        raise DumpError("no math list in the log")
    lines = []
    for line in log[i:].split("\n")[1:]:
        if line.startswith("###") or line.startswith("! "):
            break
        lines.append(line)
    counts, cur = [], None
    choice: dict[str, int] | None = None

    def close_choice():
        nonlocal choice
        if choice is not None and cur is not None:
            counts[-1] += max(choice.values()) if choice else 0
        choice = None
    for line in lines:
        m = re.match(r"^\\penalty (\d+)$", line)
        if m:
            close_choice()
            if int(m.group(1)) != len(counts) + 1:
                raise DumpError(f"marker {m.group(1)} out of order")
            counts.append(0)
            cur = int(m.group(1))
            continue
        if cur is None or not line.strip():
            continue
        if line.startswith("\\mathchoice"):
            close_choice()
            choice = {}
            continue
        if choice is not None and line[:1] in "DTSs" and line[1:2] == "\\":
            w = line[2:].split()[0].split("\\")[0]
            if any(w.startswith(x) for x in NOAD_WORDS):
                choice[line[0]] = choice.get(line[0], 0) + 1
            continue
        if line.startswith("\\"):
            close_choice()
            w = line[1:]
            if any(w.startswith(x) for x in NOAD_WORDS):
                counts[-1] += 1
    close_choice()
    if len(counts) != n:
        raise DumpError(f"the math list shows {len(counts)} of {n} markers")
    return counts


def ceil_dim(x: float, nodes: int) -> int:
    """Whole points, rounded up, with TeX's printing error (at most 0.00001pt
    a printed value, at most six values a node) absorbed."""
    return int(math.ceil(x + 6e-5 * max(nodes, 1) - 1e-9))


# ------------------------------------------------------- the derivation ------

DIM_BOUND = 8000  # Decide.v max_dim, whole points (check_strict_kernel.py pins it)
SAFE_CHARS = ("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789"
              ".,;:!?()/+-=")
PARAMS = ("parindent", "parfillskip", "leftskip", "rightskip", "abovedisplayskip",
          "belowdisplayskip", "abovedisplayshortskip", "belowdisplayshortskip")


def params_post() -> str:
    return "".join(f"\\typeout{{PRM:{p}:\\the\\{p}}}%\n" for p in PARAMS)


def parse_params(log: str) -> dict[str, float]:
    """Each layout parameter's absolute components summed (a glue's natural
    size, stretch and shrink)."""
    out = {}
    for p in PARAMS:
        m = re.search(rf"PRM:{p}:(.*)", log)
        if not m:
            raise DumpError(f"parameter {p} not typed out")
        nums = re.findall(r"(-?[\d.]+)(?:pt|fil+)", m.group(1))
        out[p] = sum(abs(float(x)) for x in nums)
    return out


def snippet(kind: str, x: str = "") -> str:
    """The TeX of one item: a name ("\\x "), a command with an empty argument
    ("\\x{}"), a character (itself)."""
    if kind == "name":
        return f"\\{x} "
    if kind == "cmd":
        return f"\\{x}{{}}"
    if kind == "char":
        return x
    if kind == "code":
        # the space ends the number and is consumed: two codes in a row are
        # adjacent characters for TeX's ligature/kern program
        return f"\\char{int(x)} "
    raise ValueError(kind)


def in_style(style: str, s: str) -> str:
    return f"$\\{style} {s}$"


class Plan:
    """The items of one dimension measurement: text items and math items by
    label (their TeX), and the pairs to measure."""

    def __init__(self, text: dict[str, str], mathi: dict[str, str],
                 nuclei: list[str], text_pairs: list[tuple[str, str]],
                 math_pairs: list[tuple[str, str]]):
        self.text, self.math, self.nuclei = text, mathi, nuclei
        self.text_pairs, self.math_pairs = text_pairs, math_pairs

    def boxes(self) -> list[str]:
        out = [""]
        out += list(self.text.values())
        for st in STYLES:
            out.append(in_style(st, ""))
            out += [in_style(st, s) for s in self.math.values()]
            out += [in_style(st, "{x}")]
            for n in self.nuclei:
                s = self.math[n]
                out += [in_style(st, s + "^{x}"), in_style(st, s + "_{x}"),
                        in_style(st, s + "^{x}_{x}")]
        out += [self.text[a] + self.text[b] for a, b in self.text_pairs]
        for st in ("displaystyle", "textstyle"):
            out += [in_style(st, self.math[a] + self.math[b]) for a, b in self.math_pairs]
        # spaces: after every safe character, in text
        out += ["x"] + [c + "{ }x" for c in SAFE_CHARS]
        return list(dict.fromkeys(out))


def measure(run, plan: Plan, chunk: int = 6000, workers: int = 1) -> dict:
    """Grade the plan's boxes in chunks (two runs a chunk: the dump, the
    character dimensions) and the layout parameters and the noads (one run
    each). The primary record the derivation and the gate read."""
    from concurrent.futures import ThreadPoolExecutor
    boxes = plan.boxes()
    parts = [boxes[i:i + chunk] for i in range(0, len(boxes), chunk)]
    with ThreadPoolExecutor(max(1, workers)) as ex:
        recs = list(ex.map(lambda b: measure_boxes(run, b), parts))
    log = run(HEAD + params_post() + "\\end{document}\n")
    params = parse_params(log)
    names = list(plan.math)
    atoms = {}
    for i in range(0, len(names), 400):
        part = names[i:i + 400]
        lg = run(lists_doc([plan.math[n] for n in part]))
        atoms.update(zip(part, parse_lists(lg, len(part))))
    return {"text": plan.text, "math": plan.math, "nuclei": plan.nuclei,
            "text_pairs": plan.text_pairs, "math_pairs": plan.math_pairs,
            "chunks": recs, "params": params, "atoms": atoms}


def derive(m: dict) -> dict:
    """Every dimension cost from a measurement record (the generator and the
    gate both call this). Returns {"B_text", "B_math", "items": {label:
    [text, math]}, "script", "open", "space", "par", "dollar", "inline",
    "display", "letters": {label: n}, "atoms": {label: n}} in whole points
    ("items" before rounding: floats)."""
    iv, nodes = {}, {}
    for rec in m["chunks"]:
        for src, (v, n) in invs(rec).items():
            iv[src], nodes[src] = v, n
    text, mathi = m["text"], m["math"]
    base_t = iv[""]
    It = {k: iv[s] - base_t for k, s in text.items()}
    Is = {st: {k: iv[in_style(st, s)] - iv[in_style(st, "")] for k, s in mathi.items()}
          for st in STYLES}
    # boundaries
    bt = [0.0]
    for a, b in m["text_pairs"]:
        bt.append(iv[text[a] + text[b]] - base_t - It[a] - It[b])
    bm = [0.0]
    for st in ("displaystyle", "textstyle"):
        for a, b in m["math_pairs"]:
            bm.append(iv[in_style(st, mathi[a] + mathi[b])] - iv[in_style(st, "")]
                      - Is[st][a] - Is[st][b])
    B_t, B_m = max(bt), max(bm)
    atoms = m["atoms"]
    items = {}
    for k in set(text) | set(mathi):
        t = It.get(k)
        dt = None if t is None else t + (B_t if t > 0 else 0.0)
        dm = None
        if k in mathi:
            dm = max(Is[st][k] for st in STYLES) + atoms[k] * B_m
        items[k] = [dt, dm]
    # scripts: the construction over every nucleus and style
    sc = [0.0]
    for st in STYLES:
        e = iv[in_style(st, "")]
        xs = iv[in_style(SCRIPT_OF[st], mathi["char:x"])] - iv[in_style(SCRIPT_OF[st], "")]
        for n in m["nuclei"]:
            s, base = mathi[n], iv[in_style(st, mathi[n])]
            sc.append(iv[in_style(st, s + "^{x}")] - base - xs)
            sc.append(iv[in_style(st, s + "_{x}")] - base - xs)
            sc.append((iv[in_style(st, s + "^{x}_{x}")] - base - 2 * xs) / 2)
        del e
    grp = max(iv[in_style(st, "{x}")] - iv[in_style(st, mathi["char:x"])] for st in STYLES) + B_m
    sp = max(iv[c + "{ }x"] - iv[c] - iv["x"] for c in SAFE_CHARS)
    p = m["params"]
    par = p["parindent"] + p["parfillskip"] + p["leftskip"] + p["rightskip"]
    disp = max(p["abovedisplayskip"] + p["belowdisplayskip"],
               p["abovedisplayshortskip"] + p["belowdisplayshortskip"])
    inline = max(iv[in_style(st, "")] - base_t for st in STYLES)
    letters = {}
    for rec in m["chunks"]:
        for src, it in zip(rec["items"], record_items(rec)):
            letters[src] = sum(1 for _, n in it[1:] if _CHAR.match(n)
                               and not n.startswith("\\glue"))
    return {"B_text": B_t, "B_math": B_m, "items": items, "script": max(sc),
            "open": grp, "space": sp, "par": par, "display": disp, "inline": inline,
            "atoms": atoms, "letters": {k: letters[s] for k, s in text.items()}}


def up(x: float | None) -> int:
    """Whole points, rounded up, with 0.001pt for TeX's printing error."""
    return 0 if x is None or x <= 0 else int(math.ceil(x + 1e-3))


def run_log(oracle, tex: str, timeout: int = 600) -> str:
    """One pdfTeX pass of an instrument through the oracle; its log."""
    with oracle.tempdir("lp-strict-dims-") as td:
        td = Path(td)
        (td / "main.tex").write_text(tex, encoding="ascii")
        oracle.run_once(td, "main.tex", oracle.tex_env(td), timeout)
        log = td / "main.log"
        return log.read_text(errors="replace") if log.is_file() else ""


def zero_table(chars: str = SAFE_CHARS) -> dict:
    t = {"char": {c: [0, 0] for c in chars}}
    for k in ("space", "par", "open", "close", "dollar", "open_inline", "close_inline",
              "open_display", "close_display", "script", "end", "undefined"):
        t[k] = [0, 0]
    return t


def plan_for(text_names: list[str], math_names: list[str], text_cmds: list[str],
             math_cmds: list[str], classes: bool = True) -> Plan:
    """The measurement plan of the given names and commands (each in the
    modes it runs in) with the fragment's characters: text items (the names,
    the commands with an empty argument, the safe characters, and the text
    font's 128 codes, for the kern/ligature pairs), math items (the names,
    the commands, the safe characters, and one atom of each class), every
    math item a script nucleus; text pairs: every two codes, and every name
    or command with every safe character both ways; math pairs: every two
    math items."""
    text = {n: snippet("name", n) for n in text_names}
    text.update({n: snippet("cmd", n) for n in text_cmds})
    text.update({f"char:{c}": c for c in SAFE_CHARS})
    text.update({f"code:{k}": snippet("code", k) for k in range(128)})
    mathi = {n: snippet("name", n) for n in math_names}
    mathi.update({n: snippet("cmd", n) for n in math_cmds})
    mathi.update({f"char:{c}": c for c in SAFE_CHARS})
    if classes:
        mathi.update({f"class:{c}": f"\\{c}{{x}}" for c in CLASSES})
    codes = [f"code:{k}" for k in range(128)]
    chars = [f"char:{c}" for c in SAFE_CHARS]
    tp = [(a, b) for a in codes for b in codes]
    for n in list(text_names) + list(text_cmds):
        tp += [(n, c) for c in chars] + [(c, n) for c in chars]
    mp = [(a, b) for a in mathi for b in mathi]
    return Plan(text, mathi, list(mathi), tp, mp)


def table(d: dict, chars: str = SAFE_CHARS) -> dict:
    """The structural table of the loader (strict_decide.ml `set_sdims`):
    [text, math] per key, whole points rounded up (plus 0.001pt for TeX's
    printing error)."""
    it = d["items"]
    t = {"char": {c: [up(it[f"char:{c}"][0]), up(it[f"char:{c}"][1])] for c in chars}}
    t["space"] = [up(d["space"]), 0]
    t["par"] = [up(d["par"]), 0]
    t["open"] = [0, up(d["open"])]
    t["close"] = [0, 0]
    both = up(d["display"] + d["inline"])
    t["dollar"] = [both, both]
    t["open_inline"] = [up(d["inline"]), up(d["inline"])]
    t["close_inline"] = [up(d["inline"]), up(d["inline"])]
    t["open_display"] = [up(d["display"]), up(d["display"])]
    t["close_display"] = [up(d["display"]), up(d["display"])]
    t["script"] = [0, up(d["script"])]
    t["end"] = [0, 0]
    t["undefined"] = [0, 0]
    return t


# ------------------------------------------------ building within the bound --

class Dims:
    """The account's costs, for BUILDING documents within the bound (the
    model, not this, decides them): `table` the structural table, `names`
    {name: [text, math]}, `asigs` the argument signatures (the mode an
    argument runs in)."""

    def __init__(self, table: dict, names: dict, asigs: dict | None = None):
        self.t, self.a = table, asigs or {}
        # an argument command's own dims come with its signature
        self.n = {**{n: h["dim"] for n, h in self.a.items() if "dim" in h}, **names}

    def tok(self, key: str, m: bool) -> int:
        return self.t[key][1 if m else 0]

    def name(self, n: str, m: bool) -> int:
        if n in self.n:
            return self.n[n][1 if m else 0]
        return self.t["undefined"][1 if m else 0]

    def nodes(self, body: list, m: bool) -> int:
        tot, i = 0, 0
        while i < len(body):
            x = body[i]
            k = x[0] if isinstance(x, list) else None
            if (k == "cmd" and x[1] in self.a and i + 1 < len(body)
                    and isinstance(body[i + 1], list) and body[i + 1][0] == "group"):
                h = self.a[x[1]]
                b = h["math"] if m else h["text"]
                pm = m
                if b[0] == "run":
                    pay = b[2] if not m else b[1]
                    pm = pay == "math"
                tot += self.name(x[1], m) + self.tok("open", m) + \
                    self.nodes(body[i + 1][1], pm) + self.tok("close", pm)
                i += 2
                continue
            tot += self.node(x, m)
            i += 1
        return tot

    def node(self, x: list, m: bool) -> int:
        if isinstance(x, dict):
            return 0  # a raw token of a probe (an unbalanced delimiter)
        k = x[0]
        if k == "text":
            return sum(self.t["char"].get(c, [10 ** 6, 10 ** 6])[1 if m else 0] for c in x[1])
        if k == "space":
            return self.tok("space", m)
        if k == "par":
            return self.tok("par", m)
        if k == "group":
            return self.tok("open", m) + self.nodes(x[1], m) + self.tok("close", m)
        if k == "stray":
            return self.tok("close", m)
        if k == "script":
            return self.tok("script", m) + self.node(x[2], m)
        if k == "cmd":
            return self.name(x[1], m)
        if k == "math":
            op, cl = {"dollar": ("dollar", "dollar"), "display": ("dollar", "dollar"),
                      "paren": ("open_inline", "close_inline"),
                      "bracket": ("open_display", "close_display")}[x[1]]
            n2 = 2 if x[1] == "display" else 1
            return (n2 * self.tok(op, m) + self.nodes(x[2], True) + n2 * self.tok(cl, True))
        if k == "raw":
            return 0
        raise ValueError(f"unknown node {x!r}")

    def units(self, body: list) -> list[list]:
        """The body cut where TeX lets a paragraph break or a new formula go:
        a one-argument command stays with its argument, and a script with the
        noad before it."""
        out: list[list] = []
        i = 0
        while i < len(body):
            x = body[i]
            if (isinstance(x, list) and x and x[0] == "cmd" and x[1] in self.a
                    and i + 1 < len(body) and isinstance(body[i + 1], list)
                    and body[i + 1][0] == "group"):
                u = [x, body[i + 1]]
                i += 2
            else:
                u = [x]
                i += 1
            while i < len(body) and isinstance(body[i], list) and body[i][0] == "script":
                u.append(body[i])
                i += 1
            if (out and isinstance(u[0], list) and u[0][0] == "script"):
                out[-1] += u
            else:
                out.append(u)
        return out

    def segment(self, S, d: dict, budget: int = DIM_BOUND) -> dict:
        """The document with paragraph breaks inserted between top-level units
        (and top-level formulas split between units) so that every segment is
        within `budget` by this account: the shape a family means, inside the
        fragment. A document already within is returned unchanged (so its
        grade is reused); the model decides the result."""
        start = self.tok("par", False)
        out, seg = [], start
        for u in self.units(d["body"]):
            x = u[0]
            if isinstance(x, list) and x and x[0] == "par" and len(u) == 1:
                out.append(x)
                seg = start
                continue
            nd = self.nodes(u, False)
            if seg + nd > budget and seg > start:
                out.append(S.par())
                seg = start
            if seg + nd > budget and len(u) == 1 and isinstance(x, list) and x[0] == "math":
                for part in self._split_math(S, x, budget - start):
                    if seg > start:
                        out.append(S.par())
                        seg = start
                    out.append(part)
                    seg += self.nodes([part], False)
                continue
            out += u
            seg += nd
        return {**d, "body": out}

    def _split_math(self, S, x: list, budget: int) -> list:
        kind, body = x[1], x[2]
        wrap = self.node([x[0], kind, []], False)
        parts, cur, acc = [], [], wrap
        for u in self.units(body):
            c = self.nodes(u, True)
            if acc + c > budget and cur:
                parts.append(cur)
                cur, acc = [], wrap
            cur += u
            acc += c
        if cur:
            parts.append(cur)
        return [S.math(kind, *p) for p in parts]


def excesses(m: dict) -> dict:
    """Every measured boundary excess, by pair: {"text": {"a|b": e}, "math":
    {"style|a|b": e}, "script": {"style|nucleus|kind": e}} (the constants of
    `derive` are their maxima; the argument generator checks its commands'
    against the phase-1 constants)."""
    iv = {}
    for rec in m["chunks"]:
        for src, (v, _) in invs(rec).items():
            iv[src] = v
    text, mathi = m["text"], m["math"]
    base_t = iv[""]
    It = {k: iv[s] - base_t for k, s in text.items()}
    out = {"text": {}, "math": {}, "script": {}}
    for a, b in m["text_pairs"]:
        out["text"][f"{a}|{b}"] = iv[text[a] + text[b]] - base_t - It[a] - It[b]
    for st in ("displaystyle", "textstyle"):
        e = iv[in_style(st, "")]
        for a, b in m["math_pairs"]:
            out["math"][f"{st}|{a}|{b}"] = (iv[in_style(st, mathi[a] + mathi[b])] - e
                                           - (iv[in_style(st, mathi[a])] - e)
                                           - (iv[in_style(st, mathi[b])] - e))
    for st in STYLES:
        xs = iv[in_style(SCRIPT_OF[st], mathi["char:x"])] - iv[in_style(SCRIPT_OF[st], "")]
        for n in m["nuclei"]:
            s, base = mathi[n], iv[in_style(st, mathi[n])]
            out["script"][f"{st}|{n}|sup"] = iv[in_style(st, s + "^{x}")] - base - xs
            out["script"][f"{st}|{n}|sub"] = iv[in_style(st, s + "_{x}")] - base - xs
            out["script"][f"{st}|{n}|both"] = (iv[in_style(st, s + "^{x}_{x}")] - base
                                               - 2 * xs) / 2
    return out
