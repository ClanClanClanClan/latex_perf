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
oracle's log line model (_unwrap_log); it changes neither file, so the blobs
the recorded grades name are untouched.

THE RECORD IS A DIAGNOSTIC, NOT EVIDENCE (C-99): pdfTeX prints whatever a
document `\\message`s, so a "! ..." or "l.N ..." line in a log can be forged.
Nothing here decides a grade. The `consistent` flag (see halting_consistent)
and the source-line verification (verify_location) are how a forged or
unparseable record is EXCLUDED from scoring rather than approximated.
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

SCHEMA = "p2-diag/1"
# Bumped whenever a definition the pre-registration names changes.
DEFINITIONS_VERSION = "p2-defs/1"

FATAL_REPORT = "!  ==> Fatal error occurred, no output PDF file produced!"
_L_LINE = re.compile(r"^l\.(\d+) ?(.*)$")
# TeX's non-file context markers (show_context): <*>, <read N>, <insert>,
# <inserted text>, <to be read again>, <recently read>, <argument>, <template>,
# <output>, <write>, <everypar> ... (tex.web §314).
_CTX_MARK = re.compile(r"^<[^<>\n]{1,24}> ")
_ELLIPSIS_CTX = re.compile(r"^ \.\.\.\s*$")


# ── log reading ──────────────────────────────────────────────────────────────

def log_lines(data: bytes) -> list[str]:
    """The log's RAW lines, decoded latin-1 so every byte survives.

    Raw, not un-wrapped: a line of exactly 79 bytes is EITHER TeX's hard wrap
    OR a full-width line followed by a new one (MEASURED: the second line of
    a context pair is padded to error_line = 79 and the help text follows it
    directly), so un-wrapping a whole log glues a context line to the help
    text. Context pairs are never wrapped (show_context truncates them to
    error_line), so they are read raw; message text and the file stack, which
    can exceed 79 bytes, are un-wrapped locally (unwrap)."""
    return data.decode("latin-1").split("\n")


def unwrap(lines: list[str]) -> list[str]:
    """`lines` with TeX's 79-byte wrap inverted (the oracle's _unwrap_log)."""
    data = "\n".join(lines).encode("latin-1")
    return [b.decode("latin-1") for b in _unwrap_log(data)]


def _is_error_line(s: str) -> bool:
    return s.startswith("!") and not s.startswith("!  ==>")


def _context_start(lines: list[str], i: int) -> bool:
    """Is lines[i] the first line of one of TeX's two-line context pairs?
    tex.web §317: the second line is the first line's length in spaces
    followed by the rest of the input."""
    s = lines[i]
    if _L_LINE.match(s) or _CTX_MARK.match(s) or _ELLIPSIS_CTX.match(s):
        return True
    if i + 1 < len(lines) and s.strip():
        nxt = lines[i + 1]
        return len(nxt) >= len(s) and nxt[:len(s)] == " " * len(s)
    return False


def error_blocks(lines: list[str]) -> list[dict]:
    """Every `!` block of the log, in order: its message lines, its context
    pairs, and its l.N line when the block has one. The pdfTeX final report
    line ("!  ==> Fatal error ...") is not a block."""
    starts = [i for i, s in enumerate(lines) if _is_error_line(s)]
    out = []
    for k, i in enumerate(starts):
        end = starts[k + 1] if k + 1 < len(starts) else len(lines)
        for j in range(i + 1, end):
            if lines[j].startswith("!  ==>") or lines[j].startswith(
                    "Here is how much of TeX's memory"):
                end = j
                break
        msg, j = [lines[i]], i + 1
        while j < end and not _context_start(lines, j):
            msg.append(lines[j])
            j += 1
        msg = unwrap(msg)
        # The message's first paragraph is the error text; LaTeX's
        # "See the ... documentation" / "Type H <return>" lines follow a blank.
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
            "index": i,
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


def halting_consistent(blocks: list[dict], lines: list[str]) -> tuple[bool, str]:
    """Is the FIRST `!` block the error pdfTeX actually stopped on?

    Under -halt-on-error pdfTeX stops at its first error, so a log has
    exactly one TeX error block. The one legitimate two-block shape is
    LaTeX's missing-file path: `\\typeout` of "! LaTeX Error: File `x' not
    found." (a MESSAGE, not a TeX error) followed by a terminal `\\read` that
    nonstopmode turns into the fatal "! Emergency stop." with
    "*** (cannot \\read from terminal in nonstop modes)". Any other extra
    block is text a document or package printed (a forgery in the C-99
    sense) and makes the record inconsistent: it is then excluded from cause
    and location scoring, never guessed at."""
    if not blocks:
        return False, "no error block"
    if len(blocks) == 1:
        return True, "one error block"
    if len(blocks) == 2:
        a, b = blocks
        tail = "\n".join(lines[b["index"]:b["index"] + 12])
        between = [s for s in lines[a["index"] + 1:b["index"]]]
        if (b["message"].startswith("! Emergency stop.")
                and "cannot \\read from terminal in nonstop modes" in tail
                and any(s.startswith("Enter file name:") for s in between)):
            return True, "missing-file prompt then Emergency stop"
    return False, f"{len(blocks)} error blocks (a printed `!` line precedes the halting error)"


# ── the file stack ───────────────────────────────────────────────────────────

_FILE_START = re.compile(r"\(([^\s()]+)")
_BOX_DUMP = re.compile(r"^(Overfull|Underfull) \\[hv]box")


def file_stack(lines: list[str], upto: int, in_tree: Callable[[str], bool] | None = None
               ) -> tuple[list[str], dict]:
    """The input-file stack pdfTeX had open at log line `upto` (exclusive):
    the outermost file first. Every `(` pushes (a file when the text after it
    names one, otherwise a TEXT marker, so the `)` that closes a printed
    "(badness 10000)" pops the marker and not a file); every `)` pops.

    A name is a file when it starts with ./ ../ / or a drive letter, or when
    `in_tree(name)` says the document tree has it. Box-content dumps after an
    Overfull/Underfull warning and "Missing character:" lines print DOCUMENT
    text with unbalanced parentheses and are skipped up to their blank line.
    Returns (stack, stats); stats counts underflows (a `)` with nothing open)
    and skipped lines, which the record carries so an unreliable parse is
    visible."""
    stack: list[tuple[str, str | None]] = []
    underflow = skipped = 0
    skipping = False
    for s in unwrap(lines[:upto]):
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
        k = 0
        while k < len(s):
            c = s[k]
            if c == "(":
                m = _FILE_START.match(s, k)
                name = m.group(1) if m else ""
                is_file = bool(name) and (
                    name.startswith(("./", "../", "/")) or re.match(r"[A-Za-z]:[\\/]", name)
                    or (in_tree is not None and in_tree(name)))
                stack.append(("file", name) if is_file else ("text", None))
                k += 1 + (len(name) if is_file else 0)
                continue
            if c == ")":
                if stack:
                    stack.pop()
                else:
                    underflow += 1
            k += 1
    files = [n for kind, n in stack if kind == "file"]
    return files, {"underflow": underflow, "skipped_lines": skipped,
                   "open_text_parens": sum(1 for kind, _ in stack if kind == "text")}


def tree_path(name: str, work_prefixes: tuple[str, ...] = ()) -> str | None:
    """The path of a stack entry relative to the document root, or None when
    it is outside the tree (a TeX Live file). Relative entries are relative to
    the root (the oracle runs with cwd = the root); an absolute entry under one
    of `work_prefixes` (the run directory as pdfTeX saw it) is made relative."""
    p = name
    for w in work_prefixes:
        w = w.rstrip("/") + "/"
        if p.startswith(w):
            p = p[len(w):]
            break
    else:
        if p.startswith("/") or re.match(r"[A-Za-z]:[\\/]", p):
            return None
    p = posixpath.normpath(p)
    if p.startswith("../") or p == "..":
        return None
    return p


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
    trailing spaces and the end-of-line character (printed ^^M when shown).
    A record whose location fails this is EXCLUDED from location scoring."""
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

# (class, regex on the first message line). FIRST MATCH WINS; the order is part
# of the definition. `obj` is the named object when the class has one.
CAUSE_RULES: list[tuple[str, re.Pattern]] = [(c, re.compile(p)) for c, p in [
    ("missing-file", r"^! LaTeX Error: File `(?P<obj>[^']+)' not found"),
    ("missing-file", r"^! I can't find file `(?P<obj>[^']+)'"),
    ("missing-file", r"^! (?:Package|Class) [\w.-]+ Error: File `(?P<obj>[^']+)' not found"),
    ("undefined-cs", r"^! Undefined control sequence"),
    ("undefined-env", r"^! LaTeX Error: Environment (?P<obj>\S+) undefined"),
    ("env-mismatch", r"^! LaTeX Error: \\begin\{(?P<obj>[^}]*)\}.* ended by \\end\{"),
    ("missing-begin-document", r"^! LaTeX Error: Missing \\begin\{document\}"),
    ("command-already-defined", r"^! LaTeX Error: Command (?P<obj>\\\S+?) already defined"),
    ("option-clash", r"^! LaTeX Error: Option clash for package (?P<obj>[^\s.]+)"),
    ("encoding", r"^! (?:Package inputenc|LaTeX) Error: (?:Unicode character|Invalid UTF-8"
                 r"|Keyboard character used is undefined)"),
    ("encoding", r"^! Text line contains an invalid character"),
    ("engine-incompatible", r"^! (?:Fatal )?Package (?P<obj>[\w.-]+) Error: .*requires? "
                            r".*(?:XeTeX|LuaTeX|XeLaTeX|LuaLaTeX)"),
    ("brace-imbalance", r"^! (?:Missing \} inserted|Extra \}, or forgotten|Too many \}'s"
                        r"|Argument of \S+ has an extra \}|Paragraph ended before \S+ was "
                        r"complete|File ended while scanning|Missing \{ inserted)"),
    ("left-right-imbalance", r"^! (?:Missing \\right\. inserted|Extra \\right|Extra \\middle)"),
    ("math-mode", r"^! (?:Missing \$ inserted|Display math should end with \$\$"
                  r"|LaTeX Error: Bad math environment delimiter|Double superscript"
                  r"|Double subscript)"),
    ("alignment", r"^! (?:Misplaced alignment tab character &|Extra alignment tab)"),
    ("tex-capacity", r"^! TeX capacity exceeded"),
    ("package-error", r"^! (?:Fatal )?Package (?P<obj>[\w.-]+) Error"),
    ("class-error", r"^! (?:Fatal )?Class (?P<obj>[\w.-]+) Error"),
    ("latex-error", r"^! LaTeX Error"),
    ("emergency-stop", r"^! Emergency stop"),
    ("other", r"^!"),
]]
CLASSES = sorted({c for c, _ in CAUSE_RULES})
_CS_AT_END = re.compile(r"(\\(?:[A-Za-z@]+|.))\s*$")


def norm_object(cls: str, obj: str | None) -> str | None:
    """Objects compare after this normalisation: a file by basename without a
    .tex/.sty/.cls extension (pdfTeX and LaTeX add them), a package or feature
    lower-cased with - and _ removed, a control sequence verbatim."""
    if obj is None:
        return None
    o = obj.strip().strip("`'\"")
    if cls == "missing-file":
        o = posixpath.basename(o)
        for ext in (".tex", ".sty", ".cls"):
            if o.endswith(ext):
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
    first = message.split("\n", 1)[0]
    for cls, rx in CAUSE_RULES:
        m = rx.match(first)
        if not m:
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
                work_prefixes: tuple[str, ...] = ()) -> dict:
    """The P2 ground-truth record of one oracle run's LAST-pass log:

      first_error  the full first `!` block: message (first paragraph, NOT
                   truncated), message_lines, context pairs, its own l.N
      location     the l.N of the error (the first l.N at or after the first
                   block; LaTeX's missing-file prompt puts it in the following
                   Emergency-stop block), the file stack at the first block,
                   the top frame's path in the tree (None when it is a TeX
                   Live file), the innermost in-tree frame, and whether the
                   source line carries the printed context (`verified`)
      cause        the pre-registered class and object of the first message
      consistent   halting_consistent's verdict, and why

    `read_source(relpath)` returns a tree file's bytes (None if absent);
    `in_tree(name)` says whether a bare stack name is a tree file."""
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
        "message", "message_lines", "context_pairs", "l_line", "l_before", "l_after", "context_kind")}
    rec["halting_message"] = blocks[-1]["message"]
    ok, why = halting_consistent(blocks, lines)
    rec["consistent"], rec["consistent_why"] = ok, why
    loc_block = next((b for b in blocks if b["l_line"] is not None), None)
    stack, stats = file_stack(lines, first["index"], in_tree)
    top = stack[-1] if stack else None
    top_rel = tree_path(top, work_prefixes) if top else None
    author = next((tree_path(f, work_prefixes) for f in reversed(stack)
                   if tree_path(f, work_prefixes) is not None), None)
    loc = {"line": loc_block["l_line"] if loc_block else None,
           "line_from_block": blocks.index(loc_block) if loc_block else None,
           "file_stack": stack, "stack_stats": stats,
           "top": top, "file": top_rel,
           "frame": ("none" if top is None else "document" if top_rel is not None else "system"),
           "author_file": author, "verified": None, "verify_why": None}
    if loc["line"] is not None and top_rel is not None:
        src = read_source(top_rel) if read_source else None
        loc["verified"], loc["verify_why"] = verify_location(
            src, loc["line"], loc_block["l_before"], loc_block["l_after"])
    rec["location"] = loc
    rec["cause"] = classify_message(first["message"], first["context_pairs"])
    return rec


# ── the CLI-side prediction ──────────────────────────────────────────────────

# Compile-blocking T5 rules whose meaning names a TeX-level cause class. Every
# other rule id (DELIM-005/006/008/010, PRT-*, and ENC rules whose byte class
# pdflatex accepts) is "unmapped": it predicts NOT-READY without a class that
# can match, so it can never be cause-correct (pre-registration §4.3).
T5_CLASS = {"DELIM-001": "brace-imbalance", "DELIM-002": "brace-imbalance",
            "DELIM-003": "left-right-imbalance", "DELIM-004": "left-right-imbalance",
            "DELIM-009": "left-right-imbalance", "DELIM-011": "left-right-imbalance"}
T5_CLASS.update({f"ENC-{i:03d}": "encoding" for i in (1, 2, 4, 5, 6, 9, 12, 14)})
# CLI feature names (Project_model.feature_to_string) -> the packages whose
# engine error they predict.
FEATURE_PACKAGES = {"opentype_fonts": {"fontspec"}, "unicode_math": {"unicodemath"},
                    "polyglossia": {"polyglossia"}, "lua_scripting": {"luacode", "luatexbase"},
                    "japanese_cjk": {"xecjk", "luatexja", "ctex"}}

_LOC_FILE_LINE = re.compile(r"\b([\w./-]+\.(?:tex|sty|cls|bbl|aux|ltx)):(\d+)\b")
_LOC_IN_FILE = re.compile(r"\bin ([^\s:]+\.(?:tex|sty|cls|bbl|aux|ltx))\b")
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
    rules; each is its own prediction, in printed order)."""
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
            out.append(p(c["class"], c["object"], f, ln, code="structural"))
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


def cli_prediction(stdout: str, stderr: str = "") -> dict:
    """The CLI's `--compile-check` answer as the P2 prediction.

    Read from the FROZEN SURFACE only (ADR-012 M0; the same scope as
    diff_real_roots.scrape_reasons): the lines before `TIER\\t`. The TIER and
    "why not strict:" lines name constructs that block a PROOF, not causes of
    an error, and are not predictions (pre-registration §4.2). Predictions,
    in the order a user reads them: the indented reasons under the NOT-READY
    line; then, when the model rejected, the indented lines under
    MODEL-CONNECTED (the blocking line then only points at them); the
    file-not-found branch writes its reasons to stderr and is read there."""
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
    return {"definitions": DEFINITIONS_VERSION, "verdict": verdict, "predictions": preds}


# ── matching (pre-registration §4) ───────────────────────────────────────────

def cause_correct(pred: dict, gold: dict) -> bool:
    """§4.3: the classes are equal, and when both sides name an object the
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
    """§4.4: the predicted file equals the gold top frame's tree path
    (normalised), and at level "line" the predicted line equals l.N exactly."""
    if not pred.get("file") or not gold_loc.get("file"):
        return False
    if posixpath.normpath(pred["file"].lstrip("./") or ".") != posixpath.normpath(
            gold_loc["file"].lstrip("./") or "."):
        return False
    if level == "file":
        return True
    return pred.get("line") is not None and pred["line"] == gold_loc.get("line")


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
    """§5 metrics over joined rows {"compiles": bool, "graded": bool,
    "agrees_with_record": bool, "gold": diag_record, "pred": cli_prediction}.
    Every count is returned with its denominator; nothing is a bare rate."""
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
    kany = sum(1 for r in cause_rows if nr(r) and any(
        cause_correct(p, r["gold"]["cause"]) for p in r["pred"].get("predictions") or []))
    # Cause precision: every row whose TOP-1 prediction names a class; a class
    # named on a compiling document is wrong; FAILS rows excluded from cause
    # scoring are excluded here too.
    cause_ids = {id(r) for r in cause_rows}
    named = [r for r in comp + fails if nr(r) and top1(r) and top1(r).get("class")
             and (r["compiles"] or id(r) in cause_ids)]
    kp = sum(1 for r in named if not r["compiles"]
             and cause_correct(top1(r), r["gold"]["cause"]))
    # Localisation precision: every row whose TOP-1 prediction carries (file,
    # line), graded or compiling; a located claim on a compiling document is
    # wrong; FAILS rows whose gold location is excluded are excluded here too.
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
            "cause_recall_any": rate(kany, len(cause_rows)),
            "cause_precision_top1": rate(kp, len(named)),
            "location_precision_line": rate(kl, len(claimed)),
            "location_recall_line": rate(krec, len(loc_rows)),
            "location_recall_file": rate(kfile, len(loc_rows))}
