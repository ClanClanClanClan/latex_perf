"""P2 diagnostics baseline ("exactly why"): the oracle-side diagnostic record,
the CLI-side prediction it is scored against, and the pre-registered matching.

Pre-registration: docs/v27/product/P2-baseline-preregistration.md. Every
definition below is the one that document names; change one here and the
document's DEFINITIONS VERSION must change with it (check_p2_diag.py pins the
two together).

PURE: no TeX, no container, no CLI. The producer that feeds this module real
runs is scripts/tools/p2_baseline.py.

WHY A MODULE OF ITS OWN, NOT AN EDIT OF _oracle.py OR diff_real_roots.py.
Every recorded grade names the git blobs of its grading code
(_oracle.grading_code, OPEN-126); any change in BEHAVIOUR of _oracle.py
(blob 6b4ce94e on the base branch) or diff_real_roots.py (9859cccf) -- even a
new function, which changes the AST that grading_code_drift compares -- makes
grading_code_drift report every recorded results*.json / regrade artefact as
"not a grade of the current grading code". This module only IMPORTS the
oracle's log line model (_unwrap_log); it changes neither file.

THE RECORD IS A DIAGNOSTIC, NOT EVIDENCE (C-99): pdfTeX prints whatever a
document `\\message`s, so a "! ..." or "l.N ..." line in a log can be forged.
Nothing here decides a grade. `consistent` (halting_consistent) and
`verified` (verify_location, plus the stack-certainty and ambiguity checks in
diag_record) are how a forged, ambiguous or unparseable record is EXCLUDED
from scoring rather than approximated.

ONE PATH NORMALISATION (canon_path). Every path that is compared -- the gold
top frame, the CLI's claimed file, a stack entry -- goes through canon_path:
relative to the document root, `normpath`ed, with an absolute path under one
of the run's roots (the host work directory, its resolved form, and the
container's RUN_DIR /lp/run) made relative; `..` escapes and absolute paths
outside the run are None, and None never matches anything.
"""
from __future__ import annotations

import math
import posixpath
import re
import sys
from pathlib import Path
from typing import Callable

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
from _oracle import _unwrap_log  # noqa: E402  (the one 79-byte line model)

SCHEMA = "p2-diag/2"
# Bumped whenever a definition the pre-registration names changes.
DEFINITIONS_VERSION = "p2-defs/2"

WRAP = 79  # max_print_line: the oracle's line model joins a line of exactly this
FATAL_PREFIX = "!  ==>"
FATAL_REPORT = "!  ==> Fatal error occurred, no output PDF file produced!"
_L_LINE = re.compile(r"^l\.(\d+) ?(.*)$")
# TeX's non-file context markers (show_context): <*>, <read N>, <insert>,
# <inserted text>, <to be read again>, <recently read>, <argument>, <template>,
# <output>, <write>, <everypar> ... (tex.web §314).
_CTX_MARK = re.compile(r"^<[^<>\n]{1,24}> ")
_ELLIPSIS_CTX = re.compile(r"^ \.\.\.\s*$")


# ── paths ────────────────────────────────────────────────────────────────────

def canon_path(p, roots: tuple = ()) -> str | None:
    """THE path normalisation (module docstring). None when `p` is not a
    path inside the document tree."""
    if not isinstance(p, str) or not p or "\x00" in p:
        return None
    s = p
    for r in sorted((str(x).rstrip("/") for x in roots if x), key=len, reverse=True):
        if s == r:
            return None
        if s.startswith(r + "/"):
            s = s[len(r) + 1:]
            break
    else:
        if s.startswith("/") or re.match(r"[A-Za-z]:[\\/]", s):
            return None
    n = posixpath.normpath(s)
    if n in (".", "", "..") or n.startswith("../") or n.startswith("/"):
        return None
    return n


# kept for callers of the first version: the same function
def tree_path(name: str, work_prefixes: tuple = ()) -> str | None:
    return canon_path(name, work_prefixes)


# ── log reading ──────────────────────────────────────────────────────────────

def log_lines(data: bytes) -> list[str]:
    """The log's RAW lines, decoded latin-1 so every byte survives.

    Raw, not un-wrapped: a line of exactly 79 bytes is EITHER TeX's hard wrap
    OR a full-width line followed by a new one (MEASURED: the second line of
    a context pair is padded to error_line = 79 and the help text follows it
    directly). Context pairs are never wrapped (show_context truncates them to
    error_line), so they are read raw; `!` lines, message text and the file
    stack are read UN-WRAPPED (groups)."""
    return data.decode("latin-1").split("\n")


def unwrap(lines: list[str]) -> list[str]:
    """`lines` with TeX's 79-byte wrap inverted (the oracle's _unwrap_log)."""
    data = "\n".join(lines).encode("latin-1")
    return [b.decode("latin-1") for b in _unwrap_log(data)]


def groups(lines: list[str]) -> list[tuple[int, int, str]]:
    """The un-wrapped lines as (first raw index, end raw index, text): the
    oracle's rule, a raw line of exactly WRAP bytes continues on the next."""
    out, i = [], 0
    while i < len(lines):
        j, text = i, lines[i]
        while len(lines[j]) == WRAP and j + 1 < len(lines):
            j += 1
            text += lines[j]
        out.append((i, j + 1, text))
        i = j + 1
    return out


def _is_error_text(s: str) -> bool:
    return s.startswith("!") and not s.startswith(FATAL_PREFIX)


def _context_start(lines: list[str], i: int) -> bool:
    """Is raw line i the first line of one of TeX's two-line context pairs?
    tex.web §317: the second line is the first line's length in spaces
    followed by the rest of the input."""
    s = lines[i]
    if _L_LINE.match(s) or _CTX_MARK.match(s) or _ELLIPSIS_CTX.match(s):
        return True
    if i + 1 < len(lines) and s.strip():
        nxt = lines[i + 1]
        return len(nxt) >= len(s) and nxt[:len(s)] == " " * len(s)
    return False


def _stop_line(s: str) -> bool:
    return s.startswith(FATAL_PREFIX) or s.startswith("Here is how much of TeX's memory")


def error_blocks(lines: list[str]) -> list[dict]:
    """Every `!` block of the log, in order. A block STARTS at an un-wrapped
    line beginning with `!` (a raw line beginning with `!` that continues a
    79-byte line is not a start: see swallowed_bang_lines). Its message is
    un-wrapped; its context pairs are read raw."""
    gs = groups(lines)
    starts = [g for g in gs if _is_error_text(g[2])]
    out = []
    for k, (r0, r1, _t) in enumerate(starts):
        end = starts[k + 1][0] if k + 1 < len(starts) else len(lines)
        for j in range(r0 + 1, end):
            if _stop_line(lines[j]):
                end = j
                break
        # the message: the un-wrapped groups from r0 until a group whose first
        # raw line starts a context pair
        msg, j = [], r0
        for (a, b, text) in gs:
            if a < r0:
                continue
            if a >= end or (a > r0 and _context_start(lines, a)):
                j = a
                break
            msg.append(text)
            j = b
        para = []
        for s in msg:
            if not s.strip():
                break
            para.append(s)
        ctx, lno, lbefore, lafter = [], None, None, None
        while j < end and _context_start(lines, j):
            top = lines[j]
            bot = lines[j + 1] if j + 1 < end else ""
            ctx.append([top, bot])
            m = _L_LINE.match(top)
            if m and lno is None:
                lno = int(m.group(1))
                lbefore = m.group(2)
                lafter = bot[len(top):] if bot.startswith(" " * len(top)) else bot.lstrip()
            j += 2
        out.append({
            "index": r0,
            "message": "\n".join(para),
            "message_lines": msg,
            "context_pairs": ctx,
            "l_line": lno,
            "l_before": lbefore,
            "l_after": lafter,
            "context_kind": ("file" if lno is not None else
                             "terminal" if any(c[0].startswith("<*>") for c in ctx) else
                             "read" if any(c[0].startswith("<read") for c in ctx) else
                             "macro" if ctx else "none"),
        })
    return out


def swallowed_bang_lines(lines: list[str]) -> int:
    """Raw lines that begin with `!` but continue a 79-byte line: TeX's
    output is AMBIGUOUS there (a wrap of a longer line, or a full-width line
    followed by a new `!` line). Counted so the record can be excluded."""
    n = 0
    for i in range(1, len(lines)):
        if len(lines[i - 1]) == WRAP and _is_error_text(lines[i]):
            n += 1
        if _stop_line(lines[i]):
            break
    return n


def halting_consistent(blocks: list[dict], lines: list[str]) -> tuple[bool, str]:
    """Is the FIRST `!` block the error pdfTeX actually stopped on?

    Under -halt-on-error pdfTeX stops at its first error and prints its
    final report FATAL_REPORT, so a consistent log has (i) the final report
    after the last block, (ii) no `!` line hidden in a 79-byte wrap, and
    (iii) exactly one block -- or the one legitimate two-block shape, LaTeX's
    missing-file path: `\\typeout` of "! LaTeX Error: File `x' not found."
    followed by "Enter file name:" and the fatal "! Emergency stop." with
    "*** (cannot \\read from terminal in nonstop modes)". A `\\typeout`ed `!`
    line in a run that ended without the final report, or any other extra
    block, is text a document or package printed (C-99): the record is then
    excluded from cause and location scoring, never guessed at."""
    if not blocks:
        return False, "no error block"
    last = blocks[-1]["index"]
    if not any(s.startswith(FATAL_REPORT) for s in lines[last:]):
        return False, "no halt: pdfTeX's fatal-error report does not follow the block"
    if swallowed_bang_lines(lines):
        return False, "a `!` line continues a 79-byte line (ambiguous wrap)"
    if len(blocks) == 1:
        return True, "one error block"
    if len(blocks) == 2:
        a, b = blocks
        tail = "\n".join(lines[b["index"]:b["index"] + 12])
        between = lines[a["index"] + 1:b["index"]]
        if (b["message"].startswith("! Emergency stop.")
                and "cannot \\read from terminal in nonstop modes" in tail
                and any(s.startswith("Enter file name:") for s in between)):
            return True, "missing-file prompt then Emergency stop"
    return False, f"{len(blocks)} error blocks (a printed `!` line precedes the halting error)"


# ── the file stack ───────────────────────────────────────────────────────────

_FILE_START = re.compile(r"\(([^\s()]+)")
_BOX_DUMP = re.compile(r"^(Overfull|Underfull) \\[hv]box")
_CLOSERS = {"[": "]", "{": "}", "<": ">"}
# Page markers ("[1", "]") and their numbers are pdfTeX's own output around
# file closes, not document text.
_CLEAN = set("[]{}<>0123456789")


def file_stack(lines: list[str], upto: int, in_tree: Callable[[str], bool] | None = None
               ) -> tuple[list[str], dict]:
    """The input-file stack pdfTeX had open at raw log line `upto`
    (exclusive): the outermost file first. Every `(` pushes (a file when the
    text after it names one, otherwise a TEXT marker); every `)` pops.

    A name is a file when it starts with ./ ../ / or a drive letter, or when
    `in_tree(name)` says the document tree has it. Box-content dumps after an
    Overfull/Underfull warning and "Missing character:" lines print DOCUMENT
    text with unbalanced parentheses and are skipped up to their blank line.

    STACK CERTAINTY. pdfTeX prints a file's `)` right after its last output,
    so a `)` that closes a FILE frame is expected at the start of a line, after
    other closers, page markers ([n], {map}, <image>) or the file's own open
    on the same line. A `)` that pops a file frame after other printed text
    ("item a)") may be the document's text instead: it is counted in
    stats["suspect_file_pops"], and diag_record then refuses to certify the
    location. stats also counts underflows and skipped lines; `opened` lists
    every file pushed before `upto` (for the ambiguity check)."""
    stack: list[tuple[str, str | None, int]] = []
    underflow = skipped = suspect = 0
    opened: list[str] = []
    skipping = False
    for ln, s in enumerate(unwrap(lines[:upto])):
        if skipping:
            if not s.strip():
                skipping = False
            else:
                skipped += 1
            continue
        if _BOX_DUMP.match(s):
            skipping = True
            continue
        if s.startswith("Missing character:"):
            skipped += 1
            continue
        k, dirty = 0, False
        while k < len(s):
            c = s[k]
            if c == "(":
                m = _FILE_START.match(s, k)
                name = m.group(1) if m else ""
                is_file = bool(name) and bool(
                    name.startswith(("./", "../", "/")) or re.match(r"[A-Za-z]:[\\/]", name)
                    or (in_tree is not None and in_tree(name)))
                if is_file:
                    stack.append(("file", name, ln))
                    opened.append(name)
                    k += 1 + len(name)
                    continue
                stack.append(("text", None, ln))
                dirty = True
                k += 1
                continue
            if c == ")":
                if stack:
                    kind, _n, opened_on = stack.pop()
                    if kind == "file" and dirty and opened_on != ln:
                        suspect += 1
                else:
                    underflow += 1
                k += 1
                continue
            if c in _CLOSERS:
                e = s.find(_CLOSERS[c], k + 1)
                if e >= 0:
                    k = e + 1
                    continue
            if not (c.isspace() or c in _CLEAN):
                dirty = True
            k += 1
    files = [n for kind, n, _ in stack if kind == "file"]
    return files, {"underflow": underflow, "skipped_lines": skipped,
                   "suspect_file_pops": suspect, "opened": opened,
                   "open_text_parens": sum(1 for kind, _, _ in stack if kind == "text")}


# ── source-line verification ─────────────────────────────────────────────────

def tex_unprint(s: str) -> bytes:
    """Invert pdfTeX's printing of a buffer: ^^xx (two lowercase hex digits)
    and ^^c (c +/- 64) back to bytes; every other char is its latin-1 byte."""
    out, k = bytearray(), 0
    b = s.encode("latin-1", errors="replace")
    while k < len(b):
        if b[k:k + 2] == b"^^" and k + 2 < len(b):
            h = b[k + 2:k + 4]
            if len(h) == 2 and re.fullmatch(rb"[0-9a-f]{2}", h):
                out.append(int(h, 16))
                k += 4
                continue
            c = b[k + 2]
            out.append(c + 64 if c < 64 else c - 64)
            k += 3
            continue
        out.append(b[k])
        k += 1
    return bytes(out)


def verify_location(src: bytes | None, line: int, before: str | None, after: str | None
                    ) -> tuple[bool, str]:
    """Does line `line` of `src` carry the text pdfTeX printed around the
    error point? tex.web §318: the l.N line shows the buffer from the line's
    start to the read point (left-truncated to "..." + tail when long), the
    line below it the rest (right-truncated with "..."). pdfTeX strips
    trailing spaces and the end-of-line character (printed ^^M when shown)."""
    if src is None:
        return False, "source not readable"
    rows = src.splitlines()
    if not (1 <= line <= len(rows)):
        return False, f"l.{line} is outside the file's {len(rows)} lines"
    row = rows[line - 1].rstrip(b" ")
    bef = tex_unprint(before or "")
    aft = tex_unprint(after or "")
    if aft.endswith(b"\r"):  # the end-of-line character, printed ^^M
        aft = aft[:-1]
    aft = aft.rstrip(b" ")
    if aft.endswith(b"..."):
        aft = aft[:-3]
    if bef.startswith(b"..."):
        tail = bef[3:]
        pos = row.find(tail)
        if not tail or pos < 0:
            return False, "the printed (truncated) text before the error point is not on that line"
        cut = pos + len(tail)
    else:
        if not row.startswith(bef):
            return False, "the printed text before the error point does not start that line"
        cut = len(bef)
    if not row[cut:].startswith(aft):
        return False, "the printed text after the error point does not follow it on that line"
    return True, "verified"


# ── cause classes (the pre-registered taxonomy) ──────────────────────────────

_PKG = r"(?:Fatal |Critical )?(?:Package|Class) (?P<obj>[\w.-]+) Error: "
# An engine requirement in a package's error text (MEASURED in the pinned
# pdfTeX build on every FEATURE_PACKAGES package: fontspec, unicode-math,
# polyglossia via fontspec, luacode, luatexja-core, xeCJK, ctex).
_ENGINE_WORDS = re.compile(r"XeTeX|LuaTeX|XeLaTeX|LuaLaTeX|Lua\(HB\)\(La\)TeX|"
                           r"\bpdf(?:la)?tex\b|unavailable in current mode", re.I)
# Primitives of another engine: undefined under pdfTeX, so a package that
# tests one dies "Undefined control sequence" (MEASURED: luatexbase.sty,
# \luatexversion).
ENGINE_PRIMITIVES = frozenset({
    "\\luatexversion", "\\luatexrevision", "\\directlua", "\\latelua", "\\luaescapestring",
    "\\luafunction", "\\XeTeXversion", "\\XeTeXrevision", "\\XeTeXinterchartoks",
    "\\XeTeXcharclass", "\\Umathcode", "\\Umathchardef", "\\Ucharcat"})
# (class, regex on the FLAT message, optional predicate on the match). FIRST
# MATCH WINS; the order is part of the definition. `obj` is the named object.
CAUSE_RULES = [(c, re.compile(p), f) for c, p, f in [
    ("missing-file", r"^! LaTeX Error: File `(?P<obj>[^']+)' not found", None),
    ("missing-file", r"^! I can't find file `(?P<obj>[^']+)'", None),
    ("missing-file", r"^! (?:Fatal |Critical )?(?:Package|Class) [\w.-]+ Error: File "
                     r"`(?P<obj>[^']+)' not found", None),
    ("engine-incompatible", r"^! " + _PKG + r"(?P<body>.*)$",
     lambda m: bool(_ENGINE_WORDS.search(m.group("body")))),
    ("undefined-cs", r"^! Undefined control sequence", None),
    ("undefined-env", r"^! LaTeX Error: Environment (?P<obj>\S+) undefined", None),
    ("env-mismatch", r"^! LaTeX Error: \\begin\{(?P<obj>[^}]*)\}.* ended by \\end\{", None),
    ("missing-begin-document", r"^! LaTeX Error: Missing \\begin\{document\}", None),
    ("command-already-defined", r"^! LaTeX Error: Command (?P<obj>\\\S+?) already defined", None),
    ("option-clash", r"^! LaTeX Error: Option clash for package (?P<obj>[^\s.]+)", None),
    ("encoding", r"^! (?:Package inputenc|LaTeX) Error: (?:Unicode character|Invalid UTF-8"
                 r"|Keyboard character used is undefined)", None),
    ("encoding", r"^! Text line contains an invalid character", None),
    ("brace-imbalance", r"^! (?:Missing \} inserted|Extra \}, or forgotten|Too many \}'s"
                        r"|Argument of \S+ has an extra \}|Paragraph ended before \S+ was "
                        r"complete|File ended while scanning|Missing \{ inserted)", None),
    ("left-right-imbalance", r"^! (?:Missing \\right\. inserted|Extra \\right|Extra \\middle)",
     None),
    ("math-mode", r"^! (?:Missing \$ inserted|Display math should end with \$\$"
                  r"|LaTeX Error: Bad math environment delimiter|Double superscript"
                  r"|Double subscript)", None),
    ("alignment", r"^! (?:Misplaced alignment tab character &|Extra alignment tab)", None),
    ("tex-capacity", r"^! TeX capacity exceeded", None),
    ("package-error", r"^! (?:Fatal |Critical )?Package (?P<obj>[\w.-]+) Error", None),
    ("class-error", r"^! (?:Fatal |Critical )?Class (?P<obj>[\w.-]+) Error", None),
    ("latex-error", r"^! LaTeX Error", None),
    ("emergency-stop", r"^! Emergency stop", None),
    ("other", r"^!", None),
]]
CLASSES = sorted({c for c, _, _ in CAUSE_RULES})
_CS_AT_END = re.compile(r"(\\(?:[A-Za-z@]+|.))\s*$")
_CONT_PREFIX = re.compile(r"^\([\w.-]+\)\s+")
# Extensions LaTeX/pdfTeX add or the author omits: a missing file is
# compared by its basename without one of these.
_FILE_EXT = (".tex", ".sty", ".cls", ".def", ".clo", ".fd", ".cfg", ".ltx", ".bib", ".bst",
             ".bbl", ".aux", ".pdf", ".png", ".jpg", ".jpeg", ".eps", ".mps", ".pgf", ".tikz")


def flat_message(message: str) -> str:
    """The message's lines joined by a space, with LaTeX's "(pkg)   "
    continuation prefixes removed: "...requires either XeTeX or" +
    "(fontspec)  LuaTeX." reads as one sentence."""
    ls = message.split("\n")
    return " ".join([ls[0]] + [_CONT_PREFIX.sub("", s).strip() for s in ls[1:]]).strip()


def norm_object(cls: str, obj: str | None) -> str | None:
    """Objects compare after this normalisation: a file by basename without
    an extension from _FILE_EXT, a package or feature lower-cased with - and _
    removed, a control sequence verbatim."""
    if obj is None:
        return None
    o = obj.strip().strip("`'\"")
    if cls == "missing-file":
        o = posixpath.basename(o)
        low = o.lower()
        for ext in _FILE_EXT:
            if low.endswith(ext):
                o = o[:-len(ext)]
                break
        return o
    if cls in ("engine-incompatible", "package-error", "class-error", "option-clash"):
        return re.sub(r"[-_]", "", o.lower())
    return o


def classify_message(message: str, context: list | None = None) -> dict:
    """(class, object) of one TeX error message. For an undefined control
    sequence the object is the control sequence at the end of the first
    context line (TeX breaks the context right after the offending token)."""
    flat = flat_message(message)
    for cls, rx, pred in CAUSE_RULES:
        m = rx.match(flat)
        if not m or (pred is not None and not pred(m)):
            continue
        obj = m.groupdict().get("obj")
        if cls == "undefined-cs" and context:
            mm = _CS_AT_END.search(context[0][0])
            obj = mm.group(1) if mm else None
        return {"class": cls, "object": norm_object(cls, obj)}
    return {"class": None, "object": None}


# ── the oracle-side record ───────────────────────────────────────────────────

def diag_record(log: bytes | None, *, read_source: Callable[[str], bytes | None] | None = None,
                in_tree: Callable[[str], bool] | None = None,
                work_prefixes: tuple = ()) -> dict:
    """The P2 ground-truth record of one oracle run's LAST-pass log:

      first_error  the full first `!` block: message (first paragraph, NOT
                   truncated), message_lines, context pairs, its own l.N
      location     the l.N of the error (the first l.N at or after the first
                   block; LaTeX's missing-file prompt puts it in the following
                   Emergency-stop block), the file stack at the first block,
                   the top frame's canon_path (None for a TeX Live file), the
                   innermost in-tree frame, and `verified`: the source line
                   carries the printed context AND the stack is certain (no
                   suspect file pop, no underflow) AND no other opened tree
                   file carries the same context at that line
      cause        the pre-registered class and object of the first message
      consistent   halting_consistent's verdict, and why

    `read_source(relpath)` returns a tree file's bytes (None if absent);
    `in_tree(name)` says whether a bare stack name is a tree file;
    `work_prefixes` are the run's roots for canon_path."""
    rec = {"schema": SCHEMA, "definitions": DEFINITIONS_VERSION,
           "has_error": False, "first_error": None, "halting_message": None,
           "consistent": None, "consistent_why": None, "location": None, "cause": None}
    if not log:
        rec["consistent_why"] = "no log"
        return rec
    lines = log_lines(log)
    blocks = error_blocks(lines)
    if not blocks:
        rec["consistent_why"] = "no error block"
        return rec
    first = blocks[0]
    rec["has_error"] = True
    rec["first_error"] = {k: first[k] for k in (
        "message", "message_lines", "context_pairs", "l_line", "l_before", "l_after",
        "context_kind")}
    rec["halting_message"] = blocks[-1]["message"]
    ok, why = halting_consistent(blocks, lines)
    rec["consistent"], rec["consistent_why"] = ok, why
    loc_block = next((b for b in blocks if b["l_line"] is not None), None)
    stack, stats = file_stack(lines, first["index"], in_tree)
    top = stack[-1] if stack else None
    top_rel = canon_path(top, work_prefixes) if top else None
    author = next((canon_path(f, work_prefixes) for f in reversed(stack)
                   if canon_path(f, work_prefixes) is not None), None)
    loc = {"line": loc_block["l_line"] if loc_block else None,
           "line_from_block": blocks.index(loc_block) if loc_block else None,
           "file_stack": stack, "stack_stats": stats,
           "top": top, "file": top_rel,
           "frame": ("none" if top is None else "document" if top_rel is not None else "system"),
           "author_file": author, "verified": None, "verify_why": None}
    if loc["line"] is not None and top_rel is not None:
        src = read_source(top_rel) if read_source else None
        v, vw = verify_location(src, loc["line"], loc_block["l_before"], loc_block["l_after"])
        if v and (stats["suspect_file_pops"] or stats["underflow"]):
            v, vw = False, (f"stack uncertain ({stats['suspect_file_pops']} suspect file pops, "
                            f"{stats['underflow']} underflows)")
        if v and read_source:
            others = {canon_path(f, work_prefixes) for f in stats["opened"]} - {top_rel, None}
            twins = sorted(f for f in others if verify_location(
                read_source(f), loc["line"], loc_block["l_before"], loc_block["l_after"])[0])
            if twins:
                v, vw = False, f"ambiguous: {len(twins)} other opened file(s) match at that line"
        loc["verified"], loc["verify_why"] = v, vw
    rec["location"] = loc
    cause = classify_message(first["message"], first["context_pairs"])
    if cause["class"] == "undefined-cs" and cause["object"] in ENGINE_PRIMITIVES:
        pkg = posixpath.basename(top).rsplit(".", 1)[0] if top else None
        cause = {"class": "engine-incompatible",
                 "object": norm_object("engine-incompatible", pkg)}
    rec["cause"] = cause
    return rec


# ── the CLI-side prediction ──────────────────────────────────────────────────

# Compile-blocking T5 rules whose meaning names a TeX-level cause class. Every
# other rule id is "unmapped": it predicts NOT-READY without a class that can
# match, so it can never be cause-correct (pre-registration §4.3).
T5_CLASS = {"DELIM-001": "brace-imbalance", "DELIM-002": "brace-imbalance",
            "DELIM-003": "left-right-imbalance", "DELIM-004": "left-right-imbalance",
            "DELIM-009": "left-right-imbalance", "DELIM-011": "left-right-imbalance"}
T5_CLASS.update({f"ENC-{i:03d}": "encoding" for i in (1, 2, 4, 5, 6, 9, 12, 14)})
# CLI feature names (Project_model.feature_to_string) -> the packages whose
# engine error the feature predicts, normalised (norm_object). MEASURED: the
# package that RAISES the error under pdfTeX, not only the one loaded
# (polyglossia dies in fontspec; luatexja in luatexja-core); every entry is
# checked against a recorded pdfTeX log by check_p2_diag.py.
FEATURE_PACKAGES = {"opentype_fonts": {"fontspec"}, "unicode_math": {"unicodemath"},
                    "polyglossia": {"polyglossia", "fontspec"},
                    "lua_scripting": {"luacode", "luatexbase", "ltluatex"},
                    "japanese_cjk": {"xecjk", "luatexja", "luatexjacore", "ctex"}}

_LOC_FILE_LINE = re.compile(r"([\w./-]+\.(?:tex|sty|cls|bbl|aux|ltx)):(\d+)\b")
_LOC_IN_FILE = re.compile(r"\bin (\S+\.(?:tex|sty|cls|bbl|aux|ltx))\b")
_LOC_LINE = re.compile(r"\(line (\d+)\)")


def _located(text: str, file_hint: str | None) -> tuple[str | None, int | None]:
    m = _LOC_FILE_LINE.search(text)
    if m:
        return m.group(1), int(m.group(2))
    f = file_hint
    if f is None:
        mf = _LOC_IN_FILE.search(text)
        f = mf.group(1) if mf else None
    ml = _LOC_LINE.search(text)
    return f, (int(ml.group(1)) if ml else None)


def _reason_predictions(text: str, source: str) -> list[dict]:
    """One printed reason line -> its predictions (a T5 line names several
    rules; each is its own prediction, in printed order). `file` is the RAW
    printed path here; cli_prediction canonicalises it."""
    t = text.strip()

    def p(cls, obj=None, file=None, line=None, code=None):
        return {"source": source, "code": code, "text": t, "class": cls,
                "object": norm_object(cls, obj) if cls else None, "file": file, "line": line}

    if t.startswith("T5 rule violations:"):
        ids = re.findall(r"[A-Z]{2,8}-\d{3}", t)
        return [p(T5_CLASS.get(i), code=i) for i in ids] or [p(None, code="T5")]
    if t.startswith("structural-fatal"):
        body = t[t.find("[") + 1:t.rfind("]")] if "[" in t else t
        out = []
        for part in body.split("; "):
            k = part.find(": !")
            c = classify_message(part[k + 2:]) if k >= 0 else {"class": None, "object": None}
            f, ln = _located(part, None)
            out.append({**p(c["class"], None, f, ln, code="structural"), "object": c["object"]})
        return out
    m = re.match(r"T2 project not closed: missing file (.+)$", t)
    if m:
        return [p("missing-file", m.group(1), code="T2")]
    m = re.match(r"(?:T3 profile incompatible: feature (\S+) not supported"
                 r"|T3 body-required feature\(s\) \[([^\]]*)\] not admitted)", t)
    if m:
        feats = [x.strip() for x in (m.group(1) or m.group(2) or "").split(";") if x.strip()]
        return [{**p("engine-incompatible", code="T3"), "object": None,
                 "object_set": sorted(FEATURE_PACKAGES.get(f, {re.sub(r"[-_]", "", f)}))}
                for f in feats] or [p(None, code="T3")]
    m = re.match(r"artefact-fatal \(([^)]+)\): (.*)$", t)
    if m:
        return [p("artefact", None, m.group(1), None, code="artefact")]
    m = re.match(r"T0 (?:parse fails|LP-Foreign construct\(s\)) in (\S+?)[ :]", t)
    if m:
        f, ln = _located(t, m.group(1))
        return [p(None, file=f, line=ln, code="T0")]
    code = (re.match(r"(T\d)\b", t).group(1) if re.match(r"T\d\b", t) else
            "model" if source == "model" else "other")
    f, ln = _located(t, None)
    return [p(None, file=f, line=ln, code=code)]


def cli_prediction(stdout: str, stderr: str = "", run_roots: tuple = ()) -> dict:
    """The CLI's `--compile-check` answer as the P2 prediction.

    Read from the FROZEN SURFACE only (ADR-012 M0; the same scope as
    diff_real_roots.scrape_reasons): the lines before `TIER\\t`. The TIER and
    "why not strict:" lines name constructs that block a PROOF, not causes of
    an error, and are not predictions (pre-registration §4.2). Predictions,
    in the order a user reads them: the indented reasons under the NOT-READY
    line; then, when the model rejected, the indented lines under
    MODEL-CONNECTED; the file-not-found branch writes its reasons to stderr.
    Every claimed file goes through canon_path with `run_roots` (the
    directory the CLI ran in, as it printed it); `file_raw` keeps the text."""
    def frozen(text):
        out = []
        for line in (text or "").split("\n"):
            if line.startswith("TIER\t"):
                break
            out.append(line)
        return out
    head, err = frozen(stdout), frozen(stderr)
    verdict = ("READY" if any(s.startswith("READY\t") for s in head) else
               "NOT-READY" if any(s.startswith("NOT-READY") for s in head + err) else None)
    blocking, model, cur = [], [], None
    for s in head + err:
        if s.startswith("NOT-READY"):
            cur = blocking
            continue
        if s.startswith("MODEL-CONNECTED"):
            cur = model
            continue
        if not s.startswith("  "):
            cur = None
            continue
        if cur is not None:
            t = s.strip()
            if t.startswith("advisory (non-blocking)") or t.startswith("(model-connected checks"):
                continue
            cur.append(t)
    preds = [x for t in blocking for x in _reason_predictions(t, "blocking")]
    preds += [x for t in model for x in _reason_predictions(t, "model")]
    for x in preds:
        x["file_raw"] = x["file"]
        x["file"] = canon_path(x["file"], run_roots) if x["file"] else None
    return {"definitions": DEFINITIONS_VERSION, "verdict": verdict, "predictions": preds}


# ── matching (pre-registration §5) ───────────────────────────────────────────

def cause_correct(pred: dict, gold: dict) -> bool:
    """§5.1: the classes are equal, and when both sides name an object the
    objects are equal after norm_object (a T3 feature names a SET of packages;
    the gold package must be in it)."""
    if not pred.get("class") or pred["class"] != gold.get("class"):
        return False
    go = gold.get("object")
    if "object_set" in pred:
        return go is None or go in pred["object_set"]
    po = pred.get("object")
    return po is None or go is None or po == go


def location_correct(pred: dict, gold_loc: dict, level: str = "line") -> bool:
    """§5.1: canon_path(predicted file) equals canon_path(gold file), both
    not None, and at level "line" the predicted line equals l.N exactly."""
    pf, gf = canon_path(pred.get("file")), canon_path(gold_loc.get("file"))
    if pf is None or gf is None or pf != gf:
        return False
    if level == "file":
        return True
    ln = pred.get("line")
    return isinstance(ln, int) and not isinstance(ln, bool) and ln == gold_loc.get("line")


def clopper_pearson(k: int, n: int, alpha: float = 0.05) -> tuple[float | None, float | None]:
    """Exact ONE-SIDED (1-alpha) bounds (lower, upper) of a binomial rate,
    by bisection on the binomial tail (no scipy in the pure jobs)."""
    if n <= 0:
        return None, None

    def tail_ge(p):  # P(X >= k)
        return sum(math.comb(n, i) * p ** i * (1 - p) ** (n - i) for i in range(k, n + 1))

    def tail_le(p):  # P(X <= k)
        return sum(math.comb(n, i) * p ** i * (1 - p) ** (n - i) for i in range(0, k + 1))

    def solve(f, target, increasing):
        lo, hi = 0.0, 1.0
        for _ in range(80):
            mid = (lo + hi) / 2
            if (f(mid) < target) == increasing:
                lo = mid
            else:
                hi = mid
        return (lo + hi) / 2
    lower = 0.0 if k == 0 else solve(tail_ge, alpha, True)
    upper = 1.0 if k == n else solve(tail_le, alpha, False)
    return lower, upper


def score_rows(rows: list[dict]) -> dict:
    """§5 metrics over the GRADED rows of the records (record-time
    exclusions are counted by the scorer, p2_baseline.score). Each row:
    {"compiles", "graded", "agrees_with_record", "gold": diag_record,
    "pred": cli_prediction}. Every count comes with its denominator."""
    ex = {"ungraded": 0, "disagrees_with_record": 0}
    fails, comp = [], []
    for r in rows:
        if not r.get("graded"):
            ex["ungraded"] += 1
            continue
        if not r.get("agrees_with_record"):
            ex["disagrees_with_record"] += 1
            continue
        (comp if r["compiles"] else fails).append(r)
    c_ex = {"no_error_block": 0, "inconsistent": 0, "unclassified": 0}
    cause_rows = []
    for r in fails:
        g = r["gold"]
        if not g.get("has_error"):
            c_ex["no_error_block"] += 1
        elif not g.get("consistent"):
            c_ex["inconsistent"] += 1
        elif not (g.get("cause") or {}).get("class"):
            c_ex["unclassified"] += 1
        else:
            cause_rows.append(r)
    l_ex = {"no_line": 0, "system_frame": 0, "unverified": 0}
    loc_rows = []
    for r in cause_rows:
        L = r["gold"].get("location") or {}
        if L.get("line") is None:
            l_ex["no_line"] += 1
        elif L.get("file") is None:
            l_ex["system_frame"] += 1
        elif not L.get("verified"):
            l_ex["unverified"] += 1
        else:
            loc_rows.append(r)

    def nr(r):
        return r["pred"].get("verdict") == "NOT-READY"

    def top1(r):
        p = r["pred"].get("predictions") or []
        return p[0] if p else None

    def top1_located(r):
        p = top1(r)
        return p if p and p.get("file") and p.get("line") is not None else None

    k1 = sum(1 for r in cause_rows if nr(r) and top1(r) and cause_correct(top1(r), r["gold"]["cause"]))
    # Cause precision: every row whose TOP-1 prediction names a class; a class
    # named on a compiling document is wrong; FAILS rows excluded from cause
    # scoring are excluded here too.
    cause_ids = {id(r) for r in cause_rows}
    named = [r for r in comp + fails if nr(r) and top1(r) and top1(r).get("class")
             and (r["compiles"] or id(r) in cause_ids)]
    kp = sum(1 for r in named if not r["compiles"]
             and cause_correct(top1(r), r["gold"]["cause"]))
    # Localisation precision: every row whose TOP-1 prediction carries (file,
    # line); a located claim on a compiling document is wrong; FAILS rows
    # whose gold location is excluded are excluded here too.
    loc_ids = {id(r) for r in loc_rows}
    claimed = [r for r in comp if nr(r) and top1_located(r)]
    claimed += [r for r in fails if nr(r) and top1_located(r) and id(r) in loc_ids]
    kl = sum(1 for r in claimed if not r["compiles"]
             and location_correct(top1_located(r), r["gold"]["location"]))
    krec = sum(1 for r in loc_rows if nr(r) and top1_located(r)
               and location_correct(top1_located(r), r["gold"]["location"]))
    kfile = sum(1 for r in loc_rows if nr(r) and top1(r)
                and location_correct(top1(r), r["gold"]["location"], "file"))

    def rate(k, n):
        lo, hi = clopper_pearson(k, n)
        return {"k": k, "n": n, "lower95": lo, "upper95": hi}
    return {"definitions": DEFINITIONS_VERSION,
            "inputs": {"rows": len(rows), "fails": len(fails), "compiles": len(comp),
                       "cause_scored": len(cause_rows), "location_scored": len(loc_rows)},
            "excluded": {**ex, **{"cause_" + k: v for k, v in c_ex.items()},
                         **{"location_" + k: v for k, v in l_ex.items()}},
            "cause_recall_top1": rate(k1, len(cause_rows)),
            "cause_precision_top1": rate(kp, len(named)),
            "location_precision_line": rate(kl, len(claimed)),
            "location_recall_line": rate(krec, len(loc_rows)),
            "location_recall_file": rate(kfile, len(loc_rows))}
