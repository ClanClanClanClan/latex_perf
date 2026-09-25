#!/usr/bin/env python3
"""Region census: in WHICH syntactic region of the ORIGINAL source does each
default --apply-fixes edit land?  (C-66 reach measurement for a proposed
Fix_guard region.)  CLI only, no pdflatex.

Window = census_fix_reach.py's: packages sorted by sha256(dirname) hex asc,
offset/n.  Each .tex file of a package is copied to a temp dir and fixed
(the same per-file recipe as ablate_fix_classes.build()).  Original vs fixed is
diffed at CHARACTER level (line diff first, then a char diff inside each
changed line block), and each changed span is attributed by its ORIGINAL offset
to the innermost *region-bearing* enclosing construct:

  A1  optional [..] arg whose top level has '=' (outside $..$)
  A2t optional [..] arg, no top-level '=', TYPESET owner
  A2o optional [..] arg, no top-level '=', other owner
  B   mandatory arg of a non-typeset command (explicit list + *set/*setup),
      and \\csname..\\endcsname
  C   macro-definition body (\\def-family body, all args of \\newcommand-family,
      \\newenvironment-family, xparse definers, \\DeclareMathOperator, \\let)
  D   everything else (sub-labelled by innermost owning command, math/text)

Plain {..} groups and mandatory args of TYPESET commands are transparent (an
edit in \\item[\\textbf{a b}] is A2t, not D).  Offsets are CHARACTER offsets in
the decoded original (UTF-8 if both sides decode strictly, else latin-1, which
is a byte bijection) -- equivalent for attribution.
"""
from __future__ import annotations

import argparse, collections, concurrent.futures as cf, difflib, hashlib, json
import os, pathlib, re, shutil, subprocess, sys, tempfile

REPO = pathlib.Path(__file__).resolve().parents[2]
CLI = REPO / "_build/default/latex-parse/src/validators_cli.exe"

SECTIONING = {"part", "chapter", "section", "subsection", "subsubsection",
              "paragraph", "subparagraph", "addchap", "addsec"}
CITES = {"cite", "citep", "citet", "citealp", "citealt", "citeauthor",
         "citeyear", "citeyearpar", "parencite", "Parencite", "textcite",
         "Textcite", "autocite", "Autocite", "footcite", "Citep", "Citet",
         "Cite", "smartcite", "supercite"}
TYPESET_OPT = SECTIONING | CITES | {"item", "caption", "footnote",
                                    "footnotetext", "footnotemark",
                                    "subcaption"}
THM_DEFAULT = {"theorem", "lemma", "proposition", "corollary", "definition",
               "remark", "example", "proof", "assumption", "conjecture",
               "claim", "notation", "exercise", "problem", "hypothesis",
               "condition", "note", "fact", "observation", "question",
               "thm", "lem", "prop", "cor", "defn", "dfn", "rem", "rmk", "ex",
               "conj", "assump", "exmp", "defi", "lemm", "coro"}
B_LIST = {"typeout": 1, "message": 1, "wlog": 1, "PackageWarning": 2,
          "PackageWarningNoLine": 2, "PackageInfo": 2, "PackageError": 3,
          "ClassWarning": 2, "ClassWarningNoLine": 2, "ClassInfo": 2,
          "ClassError": 3, "GenericWarning": 2, "GenericInfo": 2,
          "GenericError": 4, "errmessage": 1, "pgfkeys": 1, "pgfqkeys": 2,
          "tikzset": 1, "pgfplotsset": 1, "hypersetup": 1, "setkeys": 2,
          "definecolor": 3, "colorlet": 2, "lstset": 1, "sisetup": 1,
          "usetikzlibrary": 1, "usepgfplotslibrary": 1, "geometry": 1,
          "captionsetup": 1, "tcbset": 1, "newgeometry": 1,
          "pgfplotstableset": 1, "setbeamertemplate": 3, "setbeamercolor": 2,
          "setbeamerfont": 2, "hyphenation": 1, "SetKwInOut": 2}
B_SUFFIX = re.compile(r"(?<!under)(?<!over)(?<!sub)(?<!sup)(?<!empty)(?<!Sub)(?<!Sup)(set|setup)$")
# definer -> number of brace/name groups it owns (name counts even if a bare cs)
DEFS = {"newcommand": 2, "renewcommand": 2, "providecommand": 2,
        "DeclareRobustCommand": 2, "newenvironment": 3,
        "renewenvironment": 3, "NewDocumentCommand": 3,
        "RenewDocumentCommand": 3, "ProvideDocumentCommand": 3,
        "DeclareDocumentCommand": 3, "NewDocumentEnvironment": 4,
        "RenewDocumentEnvironment": 4, "DeclareMathOperator": 2,
        "newrobustcmd": 2, "renewrobustcmd": 2}
TEXDEFS = {"def", "gdef", "edef", "xdef"}
VERB_ENVS = {"verbatim", "verbatim*", "Verbatim", "lstlisting", "minted",
             "comment", "alltt", "BVerbatim", "LVerbatim", "filecontents",
             "filecontents*", "spverbatim"}
MATH_ENVS = {e + s for e in ("equation", "align", "gather", "multline",
                             "eqnarray", "displaymath", "math", "flalign",
                             "alignat", "dmath", "split", "aligned",
                             "gathered") for s in ("", "*")}
MATH_OPT_OK = {"sqrt", "\\", "xrightarrow", "xleftarrow", "smash",
               "xlongrightarrow", "xhookrightarrow", "overset", "cfrac",
               "hat", "mathclap", "text", "intertext", "tag"} - {
               "overset", "hat", "text", "tag", "intertext", "mathclap"}
NO_OPT = {"left", "right", "big", "Big", "bigg", "Bigg", "bigl", "bigr",
          "Bigl", "Bigr", "biggl", "biggr", "Biggl", "Biggr", "middle",
          "bigm", "Bigm", "relax", "par", "noindent", "hline", "centering",
          "quad", "qquad", "ldots", "dots", "cdots", "LaTeX", "TeX", "and",
          "else", "fi", "or", "hfill", "vfill", "newline", "cr",
          "displaystyle", "textstyle", "bf", "it", "em", "rm", "sf", "tt",
          "small", "large", "Large", "footnotesize", "scriptsize", "tiny",
          "normalsize", "huge", "Huge", "maketitle", "medskip", "bigskip",
          "smallskip", "clearpage", "newpage", "indent", "protect",
          "hspace", "vspace"}
BEGIN_EXTRA_BRACES = {"tabular": 1, "tabular*": 2, "tabularx": 2,
                      "array": 1, "minipage": 1, "multicols": 1,
                      "subfigure": 1, "wrapfigure": 2, "longtable": 1,
                      "alignat": 1, "alignat*": 1, "tabulary": 2,
                      "subequations": 0, "thebibliography": 1,
                      "minted": 1}


class Pend:
    __slots__ = ("name", "kind", "braces", "opts", "maxb", "env", "adj")

    def __init__(self, name, kind, maxb=None):
        self.name, self.kind, self.braces, self.opts = name, kind, 0, 0
        self.maxb, self.env, self.adj = maxb, None, True


class Region:
    __slots__ = ("start", "end", "label", "owner", "parent", "math")

    def __init__(self, start, label, owner, parent, math):
        self.start, self.end, self.label = start, None, label
        self.owner, self.parent, self.math = owner, parent, math


def top_level_eq(s: str) -> bool:
    d = 0
    math = False
    i = 0
    while i < len(s):
        c = s[i]
        if c == "\\":
            i += 2
            continue
        if c == "{":
            d += 1
        elif c == "}":
            d -= 1
        elif c == "$":
            math = not math
        elif c == "=" and d == 0 and not math:
            return True
        i += 1
    return False


def scan(src: str):
    """Return a list of closed Region objects (start=first content char,
    end=closing delimiter index) covering the source; plus a 'mathspans'
    list and comment/verbatim spans (label 'COMMENT'/'VERB')."""
    n = len(src)
    regions: list[Region] = []
    stack: list[tuple] = []          # (closer, Region|None, Pend|None)
    thm = set(THM_DEFAULT)
    optcmds = set()                  # user macros defined with an optional arg
    for m in re.finditer(r"\\newtheorem\*?\s*\{([^}]*)\}", src):
        thm.add(m.group(1).strip())
    for m in re.finditer(r"\\declaretheorem\s*(?:\[[^\]]*\])?\s*\{([^}]*)\}", src):
        thm.add(m.group(1).strip())
    for m in re.finditer(r"\\(?:re)?newcommand\*?\s*\{?\\([A-Za-z]+)\}?\s*\[\d\]\s*\[", src):
        optcmds.add(m.group(1))
    for m in re.finditer(r"\\(?:New|Renew|Declare|Provide)DocumentCommand\s*\{?\\([A-Za-z]+)\}?\s*\{([^}]*)\}", src):
        if re.search(r"(^|\s)[oOd]", m.group(2)) or m.group(2).lstrip().startswith(("o", "O")):
            optcmds.add(m.group(1))
    mathstack: list[str] = []        # '$', '$$', '\\(', '\\[', env names
    pend: Pend | None = None
    cur: Region | None = None        # innermost region-bearing region
    i = 0
    nl_since = 0

    def inmath():
        return bool(mathstack)

    def open_region(start, label, owner):
        nonlocal cur
        r = Region(start, label, owner, cur, inmath())
        regions.append(r)
        cur = r
        return r

    def close_region(r, end):
        nonlocal cur
        r.end = end
        cur = r.parent

    def classify_open(p: Pend, bracket: bool, start: int):
        """label for an arg group of pending command p."""
        if p.kind == "def":
            return "C"
        if bracket:
            return "OPT"             # resolved to A1/A2* at close (needs content)
        if p.kind == "begin_env":
            return None              # env args (column specs etc.): transparent
        if p.kind == "csb":
            return "B"
        if p.kind == "ref":
            return "D-guarded-arg"   # name tagged in owner; transparent-ish
        return None

    while i < n:
        c = src[i]
        if c == "%":
            e = src.find("\n", i)
            e = n if e < 0 else e
            r = Region(i + 1, "COMMENT", "%", cur, inmath()); r.end = e
            regions.append(r)
            i = e
            continue
        if c in " \t\r":
            i += 1
            continue
        if c == "\n":
            nl_since += 1
            if nl_since >= 2:
                pend = None
            i += 1
            continue
        nl_since = 0
        if c == "\\":
            j = i + 1
            if j < n and src[j].isalpha() and src[j].isascii():
                while j < n and src[j].isascii() and src[j].isalpha():
                    j += 1
                name = src[i + 1:j]
            else:
                name = src[j:j + 1]
                j = j + 1
            start = i
            i = j
            # star
            star = False
            if i < n and src[i] == "*" and name.isalpha():
                star = True
                i += 1
            # verb
            if name in ("verb", "lstinline", "mintinline") :
                if name == "mintinline" and i < n and src[i] == "{":
                    k = src.find("}", i); i = n if k < 0 else k + 1
                if i < n and src[i] == "*":
                    i += 1
                if i < n and src[i] == "[":
                    k = src.find("]", i); i = n if k < 0 else k + 1
                if i < n:
                    d = "}" if src[i] == "{" else src[i]
                    k = src.find(d, i + 1)
                    k = n if k < 0 else k
                    r = Region(i + 1, "VERB", name, cur, inmath()); r.end = k
                    regions.append(r)
                    i = k + 1
                pend = None
                continue
            if name == "csname":
                r = open_region(i, "B", "csname")
                stack.append(("\\endcsname", r, None))
                pend = None
                continue
            if name == "endcsname":
                if stack and stack[-1][0] == "\\endcsname":
                    _, r, _ = stack.pop()
                    close_region(r, start)
                pend = None
                continue
            # math switches
            if name == "(":
                mathstack.append("\\("); pend = None; continue
            if name == "[":
                mathstack.append("\\["); pend = None; continue
            if name in (")", "]"):
                if mathstack:
                    mathstack.pop()
                pend = None
                continue
            if name in TEXDEFS:
                # name token then parameter text up to '{'
                k = i
                while k < n and src[k] in " \t\n":
                    k += 1
                if k < n and src[k] == "\\":
                    k += 1
                    if k < n and src[k].isalpha():
                        while k < n and src[k].isalpha():
                            k += 1
                    else:
                        k += 1
                else:
                    k += 1
                r = Region(start, "C", name, cur, inmath())
                b = src.find("{", k)
                if b < 0:
                    b = n
                r.end = b                     # name+param text span
                regions.append(r)
                i = b
                pend = Pend(name, "def", 1)
                continue
            if name in ("let", "futurelet"):
                k = i
                toks = 0
                while k < n and toks < 2:
                    if src[k] in " \t\n=":
                        k += 1; continue
                    if src[k] == "\\":
                        k += 1
                        if k < n and src[k].isalpha():
                            while k < n and src[k].isalpha():
                                k += 1
                        else:
                            k += 1
                    else:
                        k += 1
                    toks += 1
                r = Region(start, "C", name, cur, inmath()); r.end = k
                regions.append(r)
                i = k
                pend = None
                continue
            full = name + ("*" if star else "")
            if name in DEFS:
                p = Pend(full, "def", DEFS[name])
                # bare-cs name form: \newcommand\foo
                k = i
                while k < n and src[k] in " \t\n":
                    k += 1
                if k < n and src[k] == "\\" and name not in (
                        "newenvironment", "renewenvironment",
                        "NewDocumentEnvironment", "RenewDocumentEnvironment"):
                    k2 = k + 1
                    while k2 < n and src[k2].isalpha():
                        k2 += 1
                    if k2 == k + 1:
                        k2 += 1
                    r = Region(start, "C", full, cur, inmath()); r.end = k2
                    regions.append(r)
                    p.braces = 1
                    i = k2
                pend = p
                continue
            if name == "begin":
                pend = Pend("begin", "begin", 1)
                continue
            if name == "end":
                # consume {env}
                k = i
                while k < n and src[k] in " \t":
                    k += 1
                if k < n and src[k] == "{":
                    e = src.find("}", k)
                    env = src[k + 1:e].strip() if e > 0 else ""
                    if mathstack and mathstack[-1] == env:
                        mathstack.pop()
                    i = e + 1 if e > 0 else n
                pend = None
                continue
            if name in B_LIST or B_SUFFIX.search(name):
                pend = Pend(full, "csb", B_LIST.get(name, 1))
            elif not name.isalpha() and name != "\\":
                pend = None          # control symbol (other than \\)
            else:
                pend = Pend(full, "cmd", None)
            continue
        if c == "$":
            if i + 1 < n and src[i + 1] == "$":
                if mathstack and mathstack[-1] == "$$":
                    mathstack.pop()
                else:
                    mathstack.append("$$")
                i += 2
            else:
                if mathstack and mathstack[-1] == "$":
                    mathstack.pop()
                else:
                    mathstack.append("$")
                i += 1
            pend = None
            continue
        if c == "{":
            p = pend
            if p is not None and (p.maxb is None or p.braces < p.maxb):
                p.braces += 1
                label = classify_open(p, False, i + 1)
                if p.kind == "begin" and p.braces == 1:
                    label = None
                r = open_region(i + 1, label or "T", p.name if p.kind != "begin_env" else "begin{%s}" % p.env)
                stack.append(("}", r, p))
            else:
                r = open_region(i + 1, "T", None)   # plain group, transparent
                stack.append(("}", r, None))
            pend = None
            i += 1
            continue
        if c == "[":
            p = pend
            ok = False
            if p is not None:
                if p.kind == "def":
                    ok = True
                elif p.kind == "begin_env":
                    ok = p.opts < 2
                elif p.kind in ("cmd", "csb"):
                    base = p.name.rstrip("*")
                    if base in NO_OPT:
                        ok = False
                    elif p.braces > 0 and base not in ("newtheorem",):
                        ok = base in CITES and False
                    elif inmath():
                        ok = base in MATH_OPT_OK or base in optcmds
                    else:
                        ok = True
            if ok:
                p.opts += 1
                owner = p.name if p.kind != "begin_env" else "begin{%s}" % p.env
                r = open_region(i + 1, "C" if p.kind == "def" else "OPT", owner)
                stack.append(("]", r, p))
            else:
                pend = None
            i += 1 if not ok else 1
            if ok:
                pend = None
            continue
        if c == "}" or c == "]":
            if c == "]" and not (stack and stack[-1][0] == "]"):
                pend = None
                i += 1
                continue
            # pop until matching closer
            while stack:
                closer, r, p = stack.pop()
                if closer == "\\endcsname":
                    close_region(r, i)
                    continue
                if closer == "]" and c == "}":
                    close_region(r, i)   # unclosed opt inside braces
                    continue
                close_region(r, i)
                # resume pending
                pend = p
                if p is not None and p.kind == "begin" and closer == "}":
                    env = src[r.start:i].strip()
                    np = Pend("begin", "begin_env",
                              BEGIN_EXTRA_BRACES.get(env, 0))
                    np.env = env
                    r.label = "D-envname"
                    r.owner = "begin"
                    pend = np
                    if env in VERB_ENVS:
                        k = src.find("\\end{%s}" % env, i)
                        k = n if k < 0 else k
                        vr = Region(i + 1, "VERB", env, cur, inmath())
                        vr.end = k
                        regions.append(vr)
                        i = k - 1
                        pend = None
                    elif env in MATH_ENVS:
                        mathstack.append(env)
                break
            i += 1
            continue
        # any other char
        pend = None
        i += 1
    while stack:
        _, r, _ = stack.pop()
        close_region(r, n)
    # resolve OPT labels
    for r in regions:
        if r.label == "OPT":
            content = src[r.start:r.end]
            own = (r.owner or "").rstrip("*")
            if top_level_eq(content):
                r.label = "A1"
            else:
                typeset = own in TYPESET_OPT
                if own.startswith("begin{"):
                    env = own[6:-1].rstrip("*")
                    typeset = env in thm or env.lower() in thm
                r.label = "A2t" if typeset else "A2o"
    return regions, thm


BEARING = {"A1", "A2t", "A2o", "B", "C", "COMMENT", "VERB"}


class Locator:
    def __init__(self, src):
        self.src = src
        self.regions, self.thm = scan(src)
        self.rs = sorted(self.regions, key=lambda r: (r.start, -(r.end if r.end is not None else len(src))))
        self.starts = [r.start for r in self.rs]

    def innermost(self, pos, insert=False):
        """innermost region whose content [start,end) holds pos (an insertion
        may also sit at pos==end, i.e. just before the closer)."""
        import bisect
        k = bisect.bisect_right(self.starts, pos) - 1
        # Regions nest: every region containing pos contains the start of the
        # latest-starting region r0 <= pos, so it is r0 or an ancestor of r0.
        n = len(self.src)
        x = self.rs[k] if k >= 0 else None
        while x is not None:
            e = x.end if x.end is not None else n
            if x.start <= pos < e or (insert and pos == e):
                return x
            x = x.parent
        return None

    def attribute(self, pos, insert=False):
        r = self.innermost(pos, insert)
        chain = []
        x = r
        while x is not None:
            chain.append(x)
            x = x.parent
        # parent chain: we need the structural parent, but LET/def spans are
        # not linked; fine.
        inner = None
        for x in chain:
            if x.label in BEARING:
                inner = x
                break
        underC = any(x.label == "C" for x in chain)
        if inner is None:
            owner = None
            for x in chain:
                if x.owner:
                    owner = x.owner
                    break
            return "D", (owner or "<prose>"), underC, (r.math if r else False)
        return inner.label, inner.owner or "?", underC, inner.math


def decode_pair(a: bytes, b: bytes):
    try:
        return a.decode("utf-8"), b.decode("utf-8"), "utf-8"
    except UnicodeDecodeError:
        return a.decode("latin-1"), b.decode("latin-1"), "latin-1"


NORMWS = re.compile(r"\s+")


def _cdiff(base, A, B):
    cm = difflib.SequenceMatcher(None, A, B, autojunk=False)
    for tt, a1, a2, b1, b2 in cm.get_opcodes():
        if tt != "equal":
            yield base + a1, base + a2, A[a1:a2], B[b1:b2]


def char_edits(o: str, f: str):
    """yield (orig_start, orig_end, old, new) at character granularity.

    Two-level alignment: raw line diff; then, inside each differing block, a
    line diff on WHITESPACE-NORMALISED keys, so a block whose every line lost
    its indentation (and whose blank lines were collapsed) still pairs each
    line with its own rewrite.  Without this second level a char diff over
    the whole block misaligns and invents edits (seen: 2507.11536v1)."""
    ol = o.splitlines(keepends=True)
    fl = f.splitlines(keepends=True)
    offs = [0]
    for L in ol:
        offs.append(offs[-1] + len(L))
    # Top-level alignment on NORMALISED keys, not raw lines: a fixer that
    # strips indentation makes raw lines of one block equal to raw lines of
    # ANOTHER block, and a raw-line diff then pairs across blocks (seen in
    # 2507.11536v1: 38576 lines in, 38576 out, content identical up to
    # whitespace, yet the raw diff "moved" whole environments).
    KO = [NORMWS.sub(" ", x).strip() for x in ol]
    KF = [NORMWS.sub(" ", x).strip() for x in fl]
    sm = difflib.SequenceMatcher(None, KO, KF, autojunk=False)
    for t, i1, i2, j1, j2 in sm.get_opcodes():
        if t == "equal":
            for k in range(i2 - i1):
                if ol[i1 + k] != fl[j1 + k]:
                    yield from _cdiff(offs[i1 + k], ol[i1 + k], fl[j1 + k])
            continue
        if t == "delete":
            yield offs[i1], offs[i2], "".join(ol[i1:i2]), ""
            continue
        if t == "insert":
            yield offs[i1], offs[i1], "", "".join(fl[j1:j2])
            continue
        ko = [NORMWS.sub(" ", x).strip() for x in ol[i1:i2]]
        kf = [NORMWS.sub(" ", x).strip() for x in fl[j1:j2]]
        sub = difflib.SequenceMatcher(None, ko, kf, autojunk=False)
        for st, a1, a2, b1, b2 in sub.get_opcodes():
            I1, I2, J1, J2 = i1 + a1, i1 + a2, j1 + b1, j1 + b2
            if st == "equal" or (st == "replace" and I2 - I1 == J2 - J1):
                for k in range(I2 - I1):
                    if ol[I1 + k] != fl[J1 + k]:
                        yield from _cdiff(offs[I1 + k], ol[I1 + k], fl[J1 + k])
            elif st == "delete":
                yield offs[I1], offs[I2], "".join(ol[I1:I2]), ""
            elif st == "insert":
                yield offs[I1], offs[I1], "", "".join(fl[J1:J2])
            else:
                A = "".join(ol[I1:I2]); B = "".join(fl[J1:J2])
                if len(A) + len(B) <= 6000:
                    yield from _cdiff(offs[I1], A, B)
                else:
                    CHARDIFF_COARSE.append((offs[I1], offs[I2]))
                    yield offs[I1], offs[I2], A, B


CHARDIFF_COARSE: list = []


def shape(old, new):
    if not old.strip() and not new.strip():
        return "ws"
    if old == " " and new == "~" or (old.strip() == "" and new == "~"):
        return "tie"
    if any(ord(ch) > 127 for ch in new):
        return "nonascii"
    return "other"


def run_pkg(pkg: pathlib.Path, timeout: int):
    out = []
    with tempfile.TemporaryDirectory(dir=os.environ.get("CENSUS_TMP")) as td:
        work = pathlib.Path(td) / "w"
        shutil.copytree(pkg, work, symlinks=True)
        for tex in sorted(work.rglob("*.tex")):
            if not tex.is_file():
                continue
            before = tex.read_bytes()
            try:
                p = subprocess.run([str(CLI), "--apply-fixes", str(tex)],
                                   capture_output=True, timeout=timeout)
            except subprocess.TimeoutExpired:
                out.append({"file": str(tex.relative_to(work)), "timeout": True})
                continue
            if p.returncode not in (0, 1):
                # A crash is not "no edits": it would undercount every region.
                raise RuntimeError(f"fixer crashed (exit {p.returncode}) on "
                                   f"{tex}: {p.stderr[-300:]!r}")
            if not (p.returncode in (0, 1) and p.stdout and p.stdout != before):
                continue
            o, f, enc = decode_pair(before, p.stdout)
            loc = Locator(o)
            for s, e, old, new in char_edits(o, f):
                ins = (s == e)
                reg, owner, underC, math = loc.attribute(s, insert=ins)
                out.append({"file": str(tex.relative_to(work)), "s": s, "e": e,
                            "old": old[:80], "new": new[:80], "reg": reg,
                            "owner": owner, "underC": underC, "math": math,
                            "shape": shape(old, new), "enc": enc,
                            "nonascii": any(ord(ch) > 127 and ch not in old for ch in new),
                            "ctx": o[max(0, s - 50):e + 30]})
    return pkg.name, out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpus-root", default=os.environ.get("LP_REAL_CORPUS"))
    ap.add_argument("--offset", type=int, default=2400)
    ap.add_argument("--n", type=int, default=120)
    ap.add_argument("--timeout", type=int, default=120)
    ap.add_argument("--jobs", type=int, default=6)
    ap.add_argument("--out", required=True)
    ns = ap.parse_args()
    root = pathlib.Path(ns.corpus_root)
    pkgs = sorted((p for p in root.iterdir() if p.is_dir()),
                  key=lambda p: hashlib.sha256(p.name.encode()).hexdigest())
    sample = pkgs[ns.offset:ns.offset + ns.n]
    assert len(sample) == ns.n
    res = {}
    with cf.ThreadPoolExecutor(ns.jobs) as ex:
        for name, rows in ex.map(lambda p: run_pkg(p, ns.timeout), sample):
            res[name] = rows
            print(name, len(rows), flush=True)
    json.dump({"window": [ns.offset, ns.n], "papers": [p.name for p in sample],
               "rows": res}, open(ns.out, "w"))


if __name__ == "__main__":
    main()
