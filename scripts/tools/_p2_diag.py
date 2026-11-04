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
DEFINITIONS_VERSION = "p2-defs/6"

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


def _tree_name_at(s: str, k: int, in_tree) -> str | None:
    """The LONGEST tree file named after the `(` at s[k], when `in_tree`
    knows one. pdfTeX prints a file name verbatim, spaces and parentheses
    included (MEASURED: `(./my file.tex`, `(./fig(1).tex`), so the name can
    end at any space, parenthesis or the line's end; the tree decides."""
    if in_tree is None:
        return None
    ends = [j for j in range(k + 2, min(len(s), k + 1 + 1024) + 1)
            if j == len(s) or s[j] in " ()"]
    for j in reversed(ends):
        cand = s[k + 1:j]
        if cand.strip() == cand and in_tree(cand):
            return cand
    return None


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
                name = _tree_name_at(s, k, in_tree)
                if name is None:
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
        # No CLASS (review L4): the gold taxonomy has no "artefact" class --
        # TeX reports the error inside the artefact as whatever it is -- so a
        # class here could never be cause-correct. The file is a claim.
        return [p(None, None, m.group(1), None, code="artefact")]
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
    diff_real_roots.scrape_reasons): the lines before `TIER\\t`, on stdout and
    then on stderr (the file-not-found branch writes there). The TIER and
    "why not strict:" lines name constructs that block a PROOF, not causes
    of an error, and are not predictions (pre-registration §4.2).

    THE PREDICTIONS, IN THE ORDER THE CLI PRINTS THEM (review L6): the CLI
    prints the MODEL-CONNECTED line first, then READY/NOT-READY and its
    reasons. A prediction is
      * an indented line under MODEL-CONNECTED, ONLY when its state is
        PREMISE-REJECTED (under PREMISE-CERTIFIED the only indented line is
        the non-blocking duplicate-label advisory: certified premises
        predict no error), and
      * an indented reason under NOT-READY,
    skipping the non-blocking advisory and the "(model-connected checks
    ...)" pointer line, which only point back. TOP-1 is the FIRST prediction
    in that printed order. A READY answer predicts nothing.
    Every claimed file goes through canon_path with `run_roots` (the
    directory the CLI ran in, as it printed it); `file_raw` keeps the text."""
    def frozen(text):
        out = []
        for line in (text or "").split("\n"):
            if line.startswith("TIER\t"):
                break
            out.append(line)
        return out
    lines = frozen(stdout) + frozen(stderr)
    tier_lines = [ln for ln in (stdout or "").split("\n") + (stderr or "").split("\n")
                  if ln.startswith("TIER")]
    verdict = ("READY" if any(s.startswith("READY\t") for s in lines) else
               "NOT-READY" if any(s.startswith("NOT-READY") for s in lines) else None)
    printed, cur = [], None
    for s in lines:
        if s.startswith("NOT-READY"):
            cur = "blocking"
            continue
        if s.startswith("MODEL-CONNECTED"):
            fields = s.split("\t")
            cur = "model" if len(fields) > 1 and fields[1] == "PREMISE-REJECTED" else None
            continue
        if not s.startswith("  "):
            cur = None
            continue
        if cur is not None:
            t = s.strip()
            if t.startswith("advisory (non-blocking)") or t.startswith("(model-connected checks"):
                continue
            printed.append((t, cur))
    preds = ([x for t, src in printed for x in _reason_predictions(t, src)]
             if verdict == "NOT-READY" else [])
    for x in preds:
        x["tier"] = "heuristic"
    preds += certified_predictions(tier_lines, verdict)
    for x in preds:
        x["file_raw"] = x["file"]
        x["file"] = canon_path(x["file"], run_roots) if x["file"] else None
        if x["tier"] == "certified" and x["file_raw"] and x["file"] is None:
            # review 2, H2(a): a certified location outside the run is not
            # dropped; it is a claim that can never be exact.
            x["location_outside_run"] = True
    vt = tier_lines[0].split("\t")[1] if tier_lines and len(tier_lines[0].split("\t")) > 1 else None
    return {"definitions": DEFINITIONS_VERSION, "verdict": verdict, "verdict_tier": vt,
            "predictions": preds}


_PROVEN_HEAD = re.compile(r"^PROVEN NOT-READY (?P<loc>.*) \[(?P<rest>[^\]]*)\]$")
_PROVEN_READY_HEAD = re.compile(r"^PROVEN READY \(decided by .+ under contract .+, pin .+\)$")
_LOC_SPLIT = re.compile(r":([0-9]+):([0-9]+) ")
# Verdict.e_code: the proof's reason codes. Any other code, or none, makes a
# certified claim malformed (review 3).
E_CODES = frozenset(f"E{i}" for i in range(15))
# The E-codes that name one gold class; a message of another class contradicts
# the proof and makes the claim malformed. (The class is a HEURISTIC-tier
# notion: certified correctness is the exact error identity, error_identity.)
E_CODE_CLASS = {"E1": "undefined-cs", "E2": "undefined-env", "E4": "math-mode",
                "E8": "command-already-defined", "E10": "missing-file", "E11": "encoding",
                "E14": "tex-capacity"}
OBJECT_CLASSES = frozenset({"missing-file", "engine-incompatible", "undefined-cs",
                            "undefined-env", "env-mismatch", "command-already-defined",
                            "option-clash", "package-error", "class-error"})


def certified_predictions(tier_lines: list[str], verdict) -> list[dict]:
    """THE CLAIM TIER (ruling R4). A prediction is CERTIFIED only when a TIER
    line names the proven tier (Verdict.render). The CLI prints ONE TIER line;
    as of v27.1.64 the strict tier is a stub (M0) and the channel is empty.

    FAIL CLOSED (reviews 2 and 3). Every TIER line that mentions the proven
    tier or a PROVEN kind is a certified claim, and it is MALFORMED (hence
    wrong) when:
      * it is not the only TIER line (a PROVEN line after another TIER line);
      * its fields are not exactly `TIER`, `proven`, `PROVEN-NOT-READY` |
        `PROVEN-READY`, headline (a PROVEN kind under another tier token, a
        short line, padding);
      * a PROVEN-NOT-READY stands beside a READY or missing verdict, or a
        PROVEN-READY beside a NOT-READY or missing one;
      * a PROVEN-NOT-READY headline does not parse, has an ambiguous
        `:line:col ` split, an unknown or missing E-code, an E-code whose class
        the message contradicts, or no file or message;
      * a PROVEN-READY headline does not parse.
    A PROVEN-READY is a certified claim that the document compiles (M5)."""
    out = []
    proven = [t for t in tier_lines
              if "proven" in t.split("\t")[1:2] or "PROVEN" in "\t".join(t.split("\t")[2:3])]
    for t in proven:
        f = t.split("\t")
        base = {"source": "tier", "tier": "certified", "code": "PROVEN", "text": t,
                "class": None, "object": None, "file": None, "line": None, "message": None}

        def bad(why, base=base):
            return dict(base, malformed=True, malformed_why=why)
        if len(tier_lines) != 1:
            out.append(bad(f"{len(tier_lines)} TIER lines: a PROVEN line beside another"))
            continue
        if len(f) != 4 or f[0] != "TIER" or f[1] != "proven" \
                or f[2] not in ("PROVEN-NOT-READY", "PROVEN-READY"):
            out.append(bad("the TIER line is not exactly TIER, proven, a PROVEN kind, headline"))
            continue
        if f[2] == "PROVEN-READY":
            c = dict(base, code="PROVEN-READY", claims="READY")
            if not _PROVEN_READY_HEAD.match(f[3]):
                c = bad("the PROVEN READY headline does not parse", c)
            elif verdict != "READY":
                c = bad(f"certified READY beside verdict {verdict!r}", c)
            out.append(c)
            continue
        if verdict != "NOT-READY":
            out.append(bad(f"certified NOT-READY beside verdict {verdict!r}"))
            continue
        m = _PROVEN_HEAD.match(f[3])
        if not m:
            out.append(bad("the PROVEN headline does not parse"))
            continue
        seps = list(_LOC_SPLIT.finditer(m.group("loc")))
        if len(seps) != 1:
            out.append(bad(f"{len(seps)} `:line:col ` separators: the location is ambiguous"))
            continue
        sp = seps[0]
        file, line = m.group("loc")[:sp.start()], int(sp.group(1))
        msg = m.group("loc")[sp.end():]
        ecode = m.group("rest").split(",")[0].strip()
        if ecode not in E_CODES:
            out.append(bad(f"unknown or missing E-code {ecode!r}"))
            continue
        full = msg if msg.startswith("!") else "! " + msg
        c = classify_message(full)
        if ecode in E_CODE_CLASS and c["class"] not in (None, "other", E_CODE_CLASS[ecode]):
            out.append(bad(f"E-code {ecode} names {E_CODE_CLASS[ecode]} but the message "
                           f"says {c['class']}"))
            continue
        if not file or not msg.strip():
            out.append(bad("the claim names no file or no message"))
            continue
        out.append(dict(base, **{"class": E_CODE_CLASS.get(ecode, c["class"]),
                                 "object": c["object"], "file": file, "line": line,
                                 "e_code": ecode, "message": full,
                                 "identity": error_identity(full, claim=True)}))
    return out


_ISSUER = re.compile(r"^(?:(?:Fatal |Critical )?(?P<kind>Package|Class) (?P<name>[\w.-]+) Error"
                     r"|(?P<latex>LaTeX Error)|(?P<pdftex>pdfTeX (?:error|warning)[^:]*)): "
                     r"(?P<body>.*)$")


def error_identity(message: str, context: list | None = None, claim: bool = False) -> list:
    """THE ERROR IDENTITY (review 3, H1): what a certified claim must equal.
    The normalised `!` message -- its first line plus LaTeX's `(pkg)`
    continuation lines (the \\MessageBreak parts, prefix removed); NOT the
    generic second line LaTeX adds without a prefix ("Or name \\end... illegal,
    see p.192 of the manual") -- split into
      [issuer, body, control sequence]
    issuer: "tex", "latex", "package <name>", "class <name>" or the pdfTeX
    issuer; body: the rest, spaces collapsed, one trailing "." removed. The
    object is IN the body: the character, the capacity name, the counter, the
    file name with its extension. For "Undefined control sequence" the
    control sequence is the third field: from the context's first line on the
    gold side, from the end of the message on the claim side."""
    msg = message or ""
    if not claim:
        # the gold side is a pdfTeX log read as latin-1 (log_lines): its bytes,
        # with ^^xx notation undone, are UTF-8 text (as the CLI's output is)
        msg = tex_unprint(msg).decode("utf-8", errors="replace")
    ls = msg.split("\n")
    parts = [ls[0]] + [_CONT_PREFIX.sub("", s) for s in ls[1:] if _CONT_PREFIX.match(s)]
    text = " ".join(" ".join(parts).split())
    text = text[1:].strip() if text.startswith("!") else text
    cs = None
    if claim:
        mm = re.match(r"^(Undefined control sequence)\.?\s+(\\(?:[A-Za-z@]+|.))\.?$", text)
        if mm:
            text, cs = mm.group(1), mm.group(2)
    elif text.rstrip(".") == "Undefined control sequence" and context:
        mm = _CS_AT_END.search(context[0][0])
        cs = mm.group(1) if mm else None
    if text.endswith("."):
        text = text[:-1]
    m = _ISSUER.match(text)
    if m:
        issuer = (f"{m.group('kind').lower()} {m.group('name')}" if m.group("kind") else
                  "latex" if m.group("latex") else m.group("pdftex"))
        body = m.group("body")
    else:
        issuer, body = "tex", text
    return [issuer, body.strip(), cs]


def certified_judgement(c: dict, r: dict) -> tuple[bool, str]:
    """(exact, why) of one CERTIFIED claim against its row (§5.6). EXACT,
    FAIL CLOSED (reviews 2 and 3): a certified NOT-READY is right only when
    the live oracle FAILED the document, the gold record is consistent, the
    claim's ERROR IDENTITY (error_identity: issuer, normalised message with
    its object, control sequence) equals the gold first error's, its file is
    the gold top frame's full canonical path, and its line is the gold's
    verified l.N. A certified READY (PROVEN-READY) is right only when the
    live oracle compiled the document; on a failing one it is the worst
    certified error (M5). Anything that cannot be confirmed is WRONG, with its
    reason; the grade of record is not consulted."""
    if c.get("malformed"):
        return False, f"malformed: {c.get('malformed_why', 'unparseable')}"
    if c.get("location_outside_run"):
        return False, "location outside the run"
    if r.get("rc") == -1 or r.get("compiles") is None:
        return False, "not confirmable: the oracle did not grade the document"
    if c.get("code") == "PROVEN-READY":
        return ((True, "exact") if r["compiles"] else
                (False, "certified READY on a document the live oracle fails"))
    if r["compiles"]:
        return False, "the document compiles under the live oracle"
    g = r.get("gold") or {}
    if not g.get("has_error") or not g.get("consistent"):
        return False, "not confirmable: the gold record is absent or inconsistent"
    fe = g.get("first_error") or {}
    gid = error_identity(fe.get("message") or "", fe.get("context_pairs"))
    if c.get("identity") != gid:
        return False, "error identity differs from TeX's first error"
    L = g.get("location") or {}
    if L.get("line") is None:
        return False, "not confirmable: the gold has no l.N"
    if L.get("file") is None:
        return False, "not confirmable: the gold's top frame is a system file"
    if not L.get("verified"):
        return False, "not confirmable: the gold location is unverified"
    if not location_correct(c, L):
        return False, "location is not the gold l.N"
    return True, "exact"


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

    # LOG SPACE (review L5): the direct sum overflows a float at n ~ 1030.
    lc = [math.lgamma(n + 1) - math.lgamma(i + 1) - math.lgamma(n - i + 1) for i in range(n + 1)]

    def tail(p, lo_i, hi_i):  # P(lo_i <= X <= hi_i)
        if p <= 0.0:
            return 1.0 if lo_i == 0 else 0.0
        if p >= 1.0:
            return 1.0 if hi_i == n else 0.0
        lp, lq = math.log(p), math.log1p(-p)
        t = [lc[i] + i * lp + (n - i) * lq for i in range(lo_i, hi_i + 1)]
        m = max(t)
        return math.exp(m) * math.fsum(math.exp(x - m) for x in t)

    def tail_ge(p):  # P(X >= k)
        return tail(p, k, n)

    def tail_le(p):  # P(X <= k)
        return tail(p, 0, k)

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


def unverified_reason(why) -> str:
    """The category of an unverified location (review L3: exclusions are
    counted by reason): a file the stack names that the tree does not have
    (a mis-parsed name), an uncertain stack, an ambiguous match, a line
    outside the file, or printed context that is not on the line."""
    w = str(why or "")
    for key, cat in (("source not readable", "file not in the tree"),
                     ("stack uncertain", "stack uncertain"), ("ambiguous", "ambiguous"),
                     ("outside the file", "line outside the file")):
        if key in w:
            return cat
    return "context not on the line" if w else "unknown"


def score_rows(rows: list[dict], cause_labels: dict | None = None) -> dict:
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
    unv: dict = {}
    loc_rows = []
    for r in cause_rows:
        L = r["gold"].get("location") or {}
        if L.get("line") is None:
            l_ex["no_line"] += 1
        elif L.get("file") is None:
            l_ex["system_frame"] += 1
        elif not L.get("verified"):
            l_ex["unverified"] += 1
            why = unverified_reason(L.get("verify_why"))
            unv[why] = unv.get(why, 0) + 1
        else:
            loc_rows.append(r)

    def nr(r):
        return r["pred"].get("verdict") == "NOT-READY"

    for r in rows:   # review 2, M2: no default tier, no unknown tier
        for p in (r.get("pred") or {}).get("predictions") or []:
            if p.get("tier") not in ("certified", "heuristic"):
                raise ValueError(f"a prediction with tier {p.get('tier')!r}")

    def first(r, tier):
        """The first prediction of `tier`, in the CLI's printed order."""
        return next((p for p in r["pred"].get("predictions") or []
                     if p["tier"] == tier), None)

    def top(r):
        """The row's claim: the certified one if there is one, else the
        first heuristic one (recall is on certified ∪ heuristic, R4)."""
        return first(r, "certified") or first(r, "heuristic")

    def located(p):
        return p if p and p.get("file") and p.get("line") is not None else None

    cause_ids = {id(r) for r in cause_rows}
    loc_ids = {id(r) for r in loc_rows}
    k1 = sum(1 for r in cause_rows if nr(r) and top(r) and cause_correct(top(r), r["gold"]["cause"]))
    krec = sum(1 for r in loc_rows if nr(r) and located(top(r))
               and location_correct(located(top(r)), r["gold"]["location"]))
    kfile = sum(1 for r in loc_rows if nr(r) and top(r)
                and location_correct(top(r), r["gold"]["location"], "file"))

    def rate(k, n):
        lo, hi = clopper_pearson(k, n)
        return {"k": k, "n": n, "lower95": lo, "upper95": hi}

    out_prec = {}
    for tier in ("heuristic",):
        # cause precision: rows whose first `tier` prediction names a class; a
        # class named on a compiling document is wrong; FAILS rows excluded
        # from cause scoring are excluded here too
        named = [r for r in comp + fails if nr(r) and first(r, tier) and first(r, tier).get("class")
                 and (r["compiles"] or id(r) in cause_ids)]
        kp = sum(1 for r in named if not r["compiles"]
                 and cause_correct(first(r, tier), r["gold"]["cause"]))
        # location precision against TeX's stopping line l.N
        claimed = [r for r in comp + fails if nr(r) and located(first(r, tier))
                   and (r["compiles"] or id(r) in loc_ids)]
        kl = sum(1 for r in claimed if not r["compiles"]
                 and location_correct(located(first(r, tier)), r["gold"]["location"]))
        out_prec[f"cause_precision_top1_{tier}"] = rate(kp, len(named))
        out_prec[f"location_precision_line_{tier}"] = rate(kl, len(claimed))

    # SOUNDNESS (R4, §5.6): a certified claim is exact or it is a defect.
    # EVERY row's certified claims are judged -- ungraded, disagreeing and
    # compiling rows included (review 2, H3) -- by certified_judgement.
    snd = {"certified_claims": 0, "certified_wrong": 0, "certified_malformed": 0,
           "wrong_rows": [], "wrong_by_reason": {}}
    for r in rows:
        for c in (r.get("pred") or {}).get("predictions") or []:
            if c.get("tier") != "certified":
                continue
            snd["certified_claims"] += 1
            ok, why = certified_judgement(c, r)
            if c.get("malformed"):
                snd["certified_malformed"] += 1
            if not ok:
                snd["certified_wrong"] += 1
                snd["wrong_rows"].append(r.get("arxiv_id"))
                key = why.split(":")[0] if why.startswith(("malformed", "not confirmable")) else why
                snd["wrong_by_reason"][key] = snd["wrong_by_reason"].get(key, 0) + 1

    # Certified precision (§5.6) is the EXACT-claim rate over every certified
    # claim: one claim carries both cause and location, so both certified
    # precision metrics are this one rate.
    cert_rate = rate(snd["certified_claims"] - snd["certified_wrong"], snd["certified_claims"])
    out_prec["cause_precision_top1_certified"] = cert_rate
    out_prec["location_precision_line_certified"] = dict(cert_rate)

    # The CAUSE line (R4): a heuristic location claim scored against the
    # two-labeller gold (cause_line_gold), where a label exists.
    lab = cause_labels or {}
    lab_claimed = [r for r in comp + fails if nr(r) and located(first(r, "heuristic"))
                   and (r["compiles"] or r.get("arxiv_id") in lab)]
    kcl = sum(1 for r in lab_claimed if not r["compiles"]
              and location_correct(located(first(r, "heuristic")), lab[r["arxiv_id"]]))
    return {"definitions": DEFINITIONS_VERSION,
            "inputs": {"rows": len(rows), "fails": len(fails), "compiles": len(comp),
                       "cause_scored": len(cause_rows), "location_scored": len(loc_rows),
                       "cause_line_labelled": sum(1 for r in fails if r.get("arxiv_id") in lab)},
            "excluded": {**ex, **{"cause_" + k: v for k, v in c_ex.items()},
                         **{"location_" + k: v for k, v in l_ex.items()}},
            "location_unverified_by_reason": dict(sorted(unv.items())),
            "soundness": snd,
            "cause_recall_top1": rate(k1, len(cause_rows)),
            **out_prec,
            "location_precision_cause_heuristic": rate(kcl, len(lab_claimed)),
            "location_recall_line": rate(krec, len(loc_rows)),
            "location_recall_file": rate(kfile, len(loc_rows))}


LABEL_SET_SCHEMA = "p2-cause-label-set/1"
ADJUDICATION_SCHEMA = "p2-cause-adjudication/1"


def norm_identity(x) -> str:
    """A labeller identity, compared case- and space-insensitively."""
    return " ".join(str(x or "").split()).casefold()


def _claim_key(c):
    """('loc', file, line) | ('none',) for a valid claim; ValueError otherwise."""
    if isinstance(c, dict) and set(c) == {"none"} and isinstance(c["none"], str):
        return ("none",)
    if isinstance(c, dict) and set(c) == {"file", "line"} and canon_path(c["file"]) \
            and type(c["line"]) is int and c["line"] >= 1:
        return ("loc", canon_path(c["file"]), c["line"])
    raise ValueError(f"an invalid label claim {c!r:.80}")


def cause_line_gold(a: dict, b: dict, adj: dict | None, check_id) -> tuple[dict, dict]:
    """(gold, stats) of the two-labeller cause-line protocol (§5.5).

    `a`, `b`: the labellers' files ({"schema": LABEL_SET_SCHEMA, "role": "A" |
    "B", "labeller": id, "docs": {doc_id: claim}}); `adj`: the adjudicator's
    ({"schema": ADJUDICATION_SCHEMA, "adjudicator": id, "docs": {doc_id:
    claim | "unresolvable"}}) or None. A claim is {"file", "line"} or
    {"none": why}. `check_id(ids)` must raise for any malformed or sealed id.
    FAIL CLOSED (review 2, H4, M4): every id of every file is checked FIRST,
    before any entry is read; the three identities must be distinct after
    norm_identity; every claim must be valid; gold needs BOTH labellers; an
    adjudication entry is allowed only for a genuine disagreement and must
    pick one of the two located claims (or say "unresolvable"). Raises
    ValueError on any violation."""
    for f, schema, role in ((a, LABEL_SET_SCHEMA, "A"), (b, LABEL_SET_SCHEMA, "B")):
        if not isinstance(f, dict) or f.get("schema") != schema or f.get("role") != role \
                or not isinstance(f.get("docs"), dict):
            raise ValueError(f"labeller file {role} is not a {schema} file with role {role}")
    if adj is not None and (not isinstance(adj, dict) or adj.get("schema") != ADJUDICATION_SCHEMA
                            or not isinstance(adj.get("docs"), dict)):
        raise ValueError(f"the adjudication file is not a {ADJUDICATION_SCHEMA} file")
    check_id(list(a["docs"]) + list(b["docs"]) + list((adj or {}).get("docs") or {}))
    ids = [norm_identity(a.get("labeller")), norm_identity(b.get("labeller"))]
    if adj is not None:
        ids.append(norm_identity(adj.get("adjudicator")))
    if not all(ids) or len(set(ids)) != len(ids):
        raise ValueError("the labellers (and the adjudicator) must be distinct, non-empty "
                         "identities")
    ka = {k: _claim_key(v) for k, v in a["docs"].items()}
    kb = {k: _claim_key(v) for k, v in b["docs"].items()}
    gold, st = {}, {"entries": len(set(ka) | set(kb)), "agreed": 0, "adjudicated": 0,
                    "unresolved": 0, "no_cause_line": 0, "incomplete": 0}
    adj_docs = (adj or {}).get("docs") or {}
    for doc_id in sorted(set(ka) | set(kb)):
        if doc_id not in ka or doc_id not in kb:
            st["incomplete"] += 1
            if doc_id in adj_docs:
                raise ValueError("an adjudication entry for a document only one labeller "
                                 "labelled")
            continue
        x, y = ka[doc_id], kb[doc_id]
        if x == y:
            if doc_id in adj_docs:
                raise ValueError("an adjudication entry where the labellers agree")
            if x[0] == "loc":
                st["agreed"] += 1
                gold[doc_id] = {"file": x[1], "line": x[2]}
            else:
                st["no_cause_line"] += 1
            continue
        e = adj_docs.get(doc_id)
        if e is None or e == "unresolvable":
            st["unresolved"] += 1
            continue
        k = _claim_key(e)
        if k[0] != "loc" or k not in (x, y):
            raise ValueError("an adjudication that is not one of the two located labels")
        st["adjudicated"] += 1
        gold[doc_id] = {"file": k[1], "line": k[2]}
    for doc_id in adj_docs:
        if doc_id not in ka and doc_id not in kb:
            raise ValueError("an adjudication entry for an unlabelled document")
    return gold, st
