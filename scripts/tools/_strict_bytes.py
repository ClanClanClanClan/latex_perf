"""Byte-level documents for the strict fragment L_S0 (ADR-012, M2 phase 2).

Used by strict_differential.py --bytes-rules and --bytes N. It GENERATES
files as bytes; it decides nothing (every verdict is the extracted
`decide_bytes`'s, through strict_decide.exe --bytes) and grades nothing (the
one oracle does, through _strict_s0.grade_bytes).

Four sources of documents:

* `lexer_families`: directed documents per constructor of the declarative
  reader and front matter (proofs/Strict/Lexer.v, Front.v; families
  `L0/<constructor>`), plus the bounds family L0/bounds (a 10,000-byte line,
  a 1,000,000-byte file) and the near-misses outside the fragment;
* `relayout`: a phase-1 document's rendered bytes (Syntax.render: one token
  per line) re-laid out: lines joined, joined through comments, ended by
  CR LF or CR, padded with spaces and tabs, blank lines varied, the front
  matter and \\end{document} split and commented, trailing bytes after
  \\end{document};
* `direct`: files generated directly as byte strings from byte-level atoms
  (characters, spaces, tabs, line ends of the three kinds, comments holding
  any byte, control words followed by spaces, line ends or comments, the
  four delimiter symbols, \\par, blank-line runs, $, $$, scripts with spaced
  or commented arguments);
* `near_miss`: an in-fragment file with one construct outside the fragment
  put where TeX reads it (the first body line); every one must be decided
  NOT-IN-FRAGMENT, never a verdict.
"""
from __future__ import annotations

import random

HEADER = b"\\documentclass{article}\n\\begin{document}\n"
END = b"\\end{document}"
SAFE = b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789.,;:!?()/+-="
LETTERS = SAFE[:52]
MAX_LINE_BYTES = 10_000        # proofs/Strict/Lexer.v max_line_bytes
MAX_FILE_BYTES = 1_000_000     # proofs/Strict/DecideBytes.v max_file_bytes


def comment_junk(rng: random.Random, k: int | None = None) -> bytes:
    """Bytes a comment may hold: anything but a line terminator."""
    k = rng.randint(0, 12) if k is None else k
    pool = [b for b in range(256) if b not in (10, 13)]
    return bytes(rng.choice(pool) for _ in range(k))


def ends_word(prefix: bytes) -> bool:
    """Does `prefix` end with a control word (so a letter after it would
    extend the name)?"""
    i = len(prefix) - 1
    while i >= 0 and prefix[i:i + 1].isalpha() and prefix[i] < 128:
        i -= 1
    return i >= 0 and i < len(prefix) - 1 and prefix[i:i + 1] == b"\\" and \
        (i == 0 or prefix[i - 1:i] != b"\\")


# ------------------------------------------------------------ front matter --

def prologue(rng: random.Random, kind: str | None = None) -> bytes:
    """A front matter of the fragment (Front.v P_prologue), measured to
    compile: fillers (blank lines, spaces, tabs, comments, \\par) before and
    between the two commands, commands split by comments or a line end."""
    kinds = ["plain", "leading", "comments", "between", "split", "spaced",
             "crlf", "same_line", "par_between", "tabs"]
    kind = kind or rng.choice(kinds)
    dc, bd = b"\\documentclass{article}", b"\\begin{document}"
    if kind == "plain":
        return HEADER
    if kind == "leading":
        return b"\n\n  \n\t\n" + dc + b"\n" + bd + b"\n"
    if kind == "comments":
        # (a file whose first two bytes are %& is outside: Lexer.v FirstLine)
        return b"%c" + comment_junk(rng) + b"\n  % x\n" + dc + b"%" + comment_junk(rng) + \
            b"\n" + bd + b"%" + comment_junk(rng) + b"\n"
    if kind == "between":
        return dc + b"\n\n\n  \n" + bd + b"\n"
    if kind == "split":
        return b"\\documentclass{art%\nicle}\n\\begin{doc%" + comment_junk(rng) + \
            b"\nument}\n"
    if kind == "spaced":
        return b"\\documentclass  {article}\n\\begin\n{document}\n"
    if kind == "crlf":
        return dc + b"\r\n" + bd + b"\r\n"
    if kind == "same_line":
        return dc + bd
    if kind == "par_between":
        return dc + b"\n\\par\n" + bd + b"\n"
    return b"\t" + dc + b" \t " + bd + b"\n"


def end_variant(rng: random.Random, kind: str | None = None) -> bytes:
    kind = kind or rng.choice(["plain", "space", "newline", "comment", "split",
                               "split2"])
    return {"plain": END, "space": b"\\end {document}",
            "newline": b"\\end\n{document}", "comment": b"\\end%\n{document}",
            "split": b"\\end{docu%\nment}",
            "split2": b"\\end{%" + comment_junk(rng) + b"\ndocument}"}[kind]


def trailing(rng: random.Random) -> bytes:
    """Bytes after \\end{document}: never read by TeX (measured), so
    anything, on its line and after (the line stays within the bound)."""
    kind = rng.choice(["none", "newline", "junk_line", "junk_lines", "tex_code"])
    if kind == "none":
        return b""
    if kind == "newline":
        return b"\n"
    if kind == "junk_line":
        return comment_junk(rng, rng.randint(1, 40)) + b"\n"
    if kind == "junk_lines":
        return b"\n" + bytes(rng.randrange(256) for _ in range(rng.randint(1, 200)))
    return b" \\zzundefined $ } ^^ \\begin{document}\n\\end{document}\n"


# ---------------------------------------------------------------- relayout --

def relayout(tex: bytes, rng: random.Random, mode: str) -> bytes:
    """Re-lay out a phase-1 rendered document (Syntax.render: the header, then
    one token per line; a blank line is a paragraph break). Only the line
    ends are changed, never a token's bytes, except the front matter and
    \\end{document}, which are replaced by variants."""
    assert tex.startswith(HEADER), "not a phase-1 rendering"
    body = tex[len(HEADER):]
    out = bytearray(prologue(rng) if mode != "render" else HEADER)
    if mode == "render":
        return tex
    parts = body.split(b"\n")
    # parts[i] is followed by a line end, except the last one
    i = 0
    while i < len(parts):
        seg = parts[i]
        last = i == len(parts) - 1
        if seg.startswith(END):
            out += end_variant(rng) if rng.random() < 0.6 else END
            seg = seg[len(END):]
        out += seg
        if last:
            break
        # a run of line ends: an empty part means a blank line follows
        j = i + 1
        blanks = 0
        while j < len(parts) - 1 and parts[j] == b"":
            blanks += 1
            j += 1
        out += sep(rng, mode, bytes(out), parts[j] if j < len(parts) else b"", blanks)
        i = j
    if tex.rstrip(b"\n").endswith(END) and mode != "render" and rng.random() < 0.5:
        out = out.rstrip(b"\n") + trailing(rng)
    return bytes(out)


def sep(rng: random.Random, mode: str, before: bytes, after: bytes, blanks: int) -> bytes:
    """The bytes replacing one line end followed by `blanks` empty lines."""
    m = mode if mode != "mixed" else rng.choice(
        ["tight", "comment", "crlf", "cr", "spaces", "keep"])
    word = ends_word(before)
    starts_letter = after[:1].isalpha() and after[:1] < b"\x80"
    hat = before.endswith(b"^") and after.startswith(b"^")
    if blanks:
        # a paragraph break must stay one: an empty line, spaces allowed
        eol = {"crlf": b"\r\n", "cr": b"\r"}.get(m, b"\n")
        pad = rng.choice([b"", b"  ", b"\t", b" \t "]) if m in ("spaces", "mixed") else b""
        head = b"%" + comment_junk(rng) + eol if m == "comment" else eol
        return head + (pad + eol) * blanks
    if m == "tight":
        if word and starts_letter:
            return rng.choice([b" ", b"  ", b"\t"])
        if hat:
            return b" "
        return b""
    if m == "comment":
        return b"%" + comment_junk(rng) + b"\n"
    if m == "crlf":
        return b"\r\n"
    if m == "cr":
        return b"\r"
    if m == "spaces":
        return rng.choice([b" \n", b"\t\n", b"\n  ", b"\n\t", b"  %" + comment_junk(rng) + b"\n",
                           b" \t\n \t"])
    return b"\n"


# ------------------------------------------------------------------ direct --

class Direct:
    """Files generated as byte strings from byte-level atoms."""

    def __init__(self, rng: random.Random, names: dict):
        self.r = rng
        self.n = names  # {"text_ok": [...], "math_ok": [...], "all": [...], "undefined": [...]}

    def eol(self) -> bytes:
        return self.r.choice([b"\n", b"\n", b"\n", b"\r\n", b"\r"])

    def sp(self) -> bytes:
        return self.r.choice([b" ", b"  ", b"\t", b" \t"])

    def comment(self) -> bytes:
        return b"%" + comment_junk(self.r) + self.eol()

    def word(self) -> bytes:
        k = self.r.randint(1, 4)
        pool = SAFE if self.r.random() < 0.3 else LETTERS
        return bytes(self.r.choice(pool) for _ in range(k))

    def cw(self, mode: str, clean: bool) -> bytes:
        if not clean and self.r.random() < 0.25:
            name = self.r.choice(self.n["undefined"])
        else:
            pool = self.n["text_ok" if mode == "text" else "math_ok"] if clean else self.n["all"]
            name = self.r.choice(pool or self.n["all"])
        tail = self.r.choice([b"", b" ", b"  ", b"\t", b"\n", b"%" + comment_junk(self.r) + b"\n",
                              b" \n "])
        return b"\\" + name.encode() + tail

    def filler(self) -> bytes:
        return self.r.choice([self.sp(), self.eol(), self.comment(), b""])

    # ADR-012 step 2, slice A: a one-argument command and its argument, the
    # argument spread over lines (the line of an error inside it is the line
    # of its closing brace), with the hazards of step 2 in failing files.
    def argcmd(self, where: str, depth: int, clean: bool) -> bytes:
        runs = self.n.get(f"arg_run_{where}", [])
        pool = runs if (clean or self.r.random() < 0.7) else self.n.get("arg_all", [])
        if not pool:
            return b""
        name, pm = self.r.choice(pool)
        gap = self.r.choice([b"", b"", b" ", b"\n", b"%" + comment_junk(self.r) + b"\n",
                             b" \n "])
        if pm == "math":
            body = self.math(depth + 1, clean)
        else:
            body = self.text(depth + 1, clean, self.r.randint(0, 4))
        if not clean and self.r.random() < 0.5:
            hz = self.r.choice([b"\\" + self.r.choice(self.n["undefined"]).encode() + b" ",
                                self.blank(), b"\\par ", b"$x$", b"^2", b"$$y$$",
                                b"\\[y\\]", b"\\[y", b"$y"])
            body = body + hz if self.r.random() < 0.5 else hz + body
        if ends_word(body):
            body += self.r.choice([b" ", b"\n", b"%\n"])
        return b"\\" + name.encode() + gap + b"{" + body + self.r.choice([b"", b"\n"]) + b"}"

    def blank(self) -> bytes:
        e = self.eol()
        return e + self.r.choice([b"", b"  ", b"\t"]) + e

    def script(self, clean: bool) -> bytes:
        up = self.r.choice([b"^", b"_"])
        gap = self.r.choice([b"", b"", b" ", b"\n", b"%" + comment_junk(self.r) + b"\n", b" \n "])
        if self.r.random() < 0.6:
            arg = bytes([self.r.choice(SAFE)])
        else:
            arg = b"{" + self.math(1, clean) + b"}"
        return up + gap + arg

    def math(self, depth: int, clean: bool) -> bytes:
        out = bytearray()
        for _ in range(self.r.randint(0, 5)):
            ch = self.r.random()
            if ch < 0.3:
                out += self.word()
            elif ch < 0.45:
                out += self.filler()
            elif ch < 0.65:
                out += self.script(clean)
            elif ch < 0.8:
                out += self.cw("math", clean)
            elif ch < 0.9 and depth < 3:
                out += (self.argcmd("math", depth, clean)
                        if self.n.get("arg_run_math") and self.r.random() < 0.35
                        else b"{" + self.math(depth + 1, clean) + b"}")
            elif not clean:
                out += self.r.choice([b"}", self.blank(), b"$", b"\\par ", b"^", b"\\)"])
            if ends_word(bytes(out)) and self.r.random() < 0.5:
                out += b" "
        return bytes(out)

    def text(self, depth: int, clean: bool, k: int) -> bytes:
        out = bytearray()
        for _ in range(k):
            ch = self.r.random()
            if ch < 0.25:
                out += self.word()
            elif ch < 0.4:
                out += self.filler()
            elif ch < 0.47:
                out += self.blank()
            elif ch < 0.55:
                out += self.cw("text", clean)
            elif ch < 0.72:
                kind = self.r.choice(["$", "$$", "\\(", "\\["])
                close = {"$": b"$", "$$": b"$$", "\\(": b"\\)", "\\[": b"\\]"}[kind]
                if not clean and self.r.random() < 0.15:
                    close = self.r.choice([b"$", b"$$", b"\\)", b"\\]", b""])
                out += kind.encode() + self.math(depth + 1, clean) + close
            elif ch < 0.8 and depth < 4:
                out += (self.argcmd("text", depth, clean)
                        if self.n.get("arg_run_text") and self.r.random() < 0.4
                        else b"{" + self.text(depth + 1, clean, self.r.randint(0, 4)) + b"}")
            elif ch < 0.84:
                out += b"\\par" + self.r.choice([b" ", b"\n", b"%\n", b""])
            elif not clean:
                out += self.r.choice([b"}", b"^x", b"_{y}", b"\\zz", b"$", b"{"])
            # a letter right after a control word would extend its name
            if ends_word(bytes(out)):
                out += self.r.choice([b" ", b"\n", b"%\n"])
        return bytes(out)

    def document(self) -> bytes:
        clean = self.r.random() < 0.45
        body = self.text(0, clean, self.r.randint(1, 12))
        has_end = self.r.random() > 0.05
        doc = prologue(self.r) + body
        if has_end:
            doc += self.r.choice([b"", b"\n", b"\r\n", b" "]) + end_variant(self.r) + \
                trailing(self.r)
        else:
            doc += self.r.choice([b"", b"\n", b"%\n"])
        return doc


# --------------------------------------------------------------- near-miss --

NEAR_MISS = [
    # (construct, why) -- a line put right after \begin{document}
    (b"x ~ y", "active character ~"),
    (b"x # y", "parameter character"),
    (b"x & y", "alignment character"),
    (b"x \x00 y", "invalid character (byte 0)"),
    (b"x \x7f y", "invalid character (byte 127)"),
    (b"x \x0c y", "active form feed"),
    (b"x \x01 y", "control byte"),
    (b"x \x1b y", "control byte"),
    (b"caf\xc3\xa9", "UTF-8 (active bytes >= 128)"),
    (b"x \xff y", "byte 255"),
    (b"$x^^41$", "^^ notation"),
    (b"$x^^$", "^^ before the end of the line"),
    (b"\\zz^^41", "^^ after a control word"),
    (b"\\^^41", "^^ after the escape character"),
    (b"x\\", "escape at the end of a line (control symbol ^^M)"),
    (b"x \\, y", "control symbol \\,"),
    (b"x \\  y", "control space"),
    (b"x \\\\ y", "control symbol \\\\"),
    (b"x \\{ y", "control symbol \\{"),
    (b"x \\% y", "control symbol \\%"),
    (b"x \\$ y", "control symbol \\$"),
    (b"x \\' y", "control symbol \\'"),
    (b"\\end x", "\\end without {document}"),
    (b"\\end{Document}", "\\end of another environment"),
    (b"\\end{ document}", "\\end{ document}"),
    (b"\\end{document }", "\\end{document }"),
    (b"\\begin{document}", "\\begin in the body"),
    (b"\\documentclass{article}", "\\documentclass in the body"),
    (b"x [y]", "character [ outside the fragment's set"),
    (b"x *", "character * outside the fragment's set"),
    (b"x 'y'", "quote"),
    (b"x `y", "backquote"),
    (b"x @ y", "@"),
    (b"x \"y\"", "double quote"),
    (b"x < y", "<"),
    (b"x | y", "|"),
    (b"$x^$", "script without an argument"),
    (b"$x^\n\ny$", "script before a blank line"),
    (b"$x^\\alpha$", "script with a control word argument"),
    (b"$x^ }$", "script before }"),
    (b"x" * (MAX_LINE_BYTES + 1), "line one past the bound"),
]
FIRST_LINE_NEAR = [b"%&latex\n", b"%&etex\n", b"%&tex\n", b"%&  latex\n", b"%&latex x\n"]


def near_miss_docs(rng: random.Random) -> list[tuple[str, bytes]]:
    out = []
    for construct, why in NEAR_MISS:
        out.append((why, HEADER + construct + b"\nz\n" + END + b"\n"))
        out.append((why + " (after a prologue variant)",
                    prologue(rng) + b"a " + construct + b" b\n" + END + b"\n"))
    # front matter outside the fragment
    for bad in (b"\\documentclass\n\n{article}\\begin{document}",
                b"\\documentclass[12pt]{article}\\begin{document}",
                b"\\documentclass{report}\\begin{document}",
                b"\\documentclass{article}\\usepackage{amsmath}\\begin{document}",
                b"\\documentclass{article} x \\begin{document}",
                b"\\documentclass{article}",
                b"\\begin{document}\\documentclass{article}",
                b"\\documentclass{ article}\\begin{document}",
                b"\\documentclass{article}\\begin\n\n{document}",
                b"x\\documentclass{article}\\begin{document}",
                b""):
        out.append(("front matter", bad + b"\nx\n" + END + b"\n"))
    # every construct outside the reader, in each state of the line reader:
    # N (line start), M (after a character), S (after a space; after a word)
    for construct in (b"&", b"#", b"~", b"\x00", b"\x7f", b"^^41", b"\\zz^^41",
                      b"\\^^41", b"\xe9"):
        for pre in (b"", b"x", b"x ", b"\\zzq "):
            out.append(("reader cell", HEADER + pre + construct + b"\nz\n" + END + b"\n"))
    # TeX Live's first-line directive (Lexer.v FirstLine, C-89)
    for first in FIRST_LINE_NEAR:
        out.append(("first line %&", first + HEADER + b"x\n" + END + b"\n"))
    # the file ends right after $ (DecideBytes.v: outside)
    out.append(("ends with $", HEADER + b"$$x$%"))
    out.append(("ends with $ (inline)", HEADER + b"x $%"))
    # one past the file bound
    big = HEADER + (b"%" + b"c" * 98 + b"\n") * ((MAX_FILE_BYTES - len(HEADER)) // 100 + 1)
    out.append(("file one past the bound", big + b"x\n" + END + b"\n"))
    # capacity bounds of the kernel (Decide.v)
    out.append(("brace nesting past the bound", HEADER + b"{" * 201 + b"x" + b"}" * 201 + b"\n" + END))
    # C-94: the group bound counts a formula as a group: $ and 200 braces,
    # and the reviewer's box-and-formula shape one level past 200 groups
    out.append(("formula and 200 braces past the group bound",
                HEADER + b"$" + b"{" * 200 + b"x" + b"}" * 200 + b"$\n" + END))
    out.append(("box and formula past the group bound",
                HEADER + b"\\mbox{$" * 101 + b"x" + b"$}" * 101 + b"\n" + END))
    # C-98: the round-2 reviewer's file: 197 box levels around 6,427 empty
    # frames (19,983 tokens, 200 groups) overflow main memory: argument copies
    frames = b"\n".join(b"\\frame{}" * 60 for _ in range(6427 // 60)) + b"\\frame{}" * (6427 % 60)
    out.append(("argument copies past the memory account",
                HEADER + b"\\mbox{" * 197 + b"\n" + frames + b"\n" + b"}" * 197 + b"\n" + END + b"\n"))
    out.append(("tokens past the bound", HEADER + (b"x" * 5_000 + b"%\n") * 4 + b"xx\n" + END))
    return out


def file_at_bound() -> bytes:
    """A file of exactly MAX_FILE_BYTES bytes, in the fragment and READY."""
    tail = b"x\n" + END + b"\n"
    fill = MAX_FILE_BYTES - len(HEADER) - len(tail)
    lines, rest = divmod(fill, 100)
    body = (b"%" + b"c" * 98 + b"\n") * lines
    if rest:
        body += b"%" + b"c" * (rest - 2) + b"\n" if rest >= 2 else b"\n"
    doc = HEADER + body + tail
    assert len(doc) == MAX_FILE_BYTES, len(doc)
    return doc


# --------------------------------------------------------- lexer families --

# Constructors of the reader whose use puts a file outside the fragment (a
# RBad token, Lexer.v), and LL_end, which the article contract reaches only
# after a control symbol consumed the end-of-line character (\endlinechar is
# of category 5 and ends every buffer otherwise; the symbol is then ^^M, not
# one of the four delimiters). Their families are decided, never graded.
OUTSIDE_FAMILIES = ["LL_hathat", "LL_word_hathat", "LL_sym_hathat", "LL_bad",
                    "LL_end", "LX_long", "FL_directive", "L0-NEAR"]


def lexer_families(names: dict, rng: random.Random) -> list[tuple[str, bytes]]:
    """Directed documents per constructor of Lexer.v and Front.v (family =
    constructor name), the bounds family L0-bounds, and the outside ones."""
    U = names["undefined"][0].encode()
    TM = names["text_material"].encode()      # text: material, math: noad
    MA = names["math_only"].encode()          # text: fatal E3, math: noad
    H = HEADER

    def d(body: bytes, end: bool = True) -> bytes:
        return H + body + (END + b"\n" if end else b"")

    f: list[tuple[str, bytes]] = []

    def add(fam, b):
        f.append((fam, b))

    for body in (b"x\n", b"$x\n\ny$\n", b"x\n\\" + U + b"\n", b"$$x$\ny$$\n"):
        add("Lines_lf", d(body))
        add("Lines_crlf", d(body).replace(b"\n", b"\r\n"))
        add("Lines_cr", d(body).replace(b"\n", b"\r"))
    add("Lines_cr", d(b"$x\r\n\ry$\n"))          # CR LF then CR: a blank line
    add("Lines_crlf", d(b"$x\r\n\r\ny$\n"))      # CR LF CR LF: one blank line
    add("Lines_lf", d(b"$x\n\ry$\n"))              # LF then CR: a blank line
    add("Lines_last", H + b"x\n" + END)            # no final line end
    add("Lines_last", H + b"x")                      # no \end, no line end: E5
    add("Lines_last", H + b"$$x$")                   # display $ on the last line
    add("Lines_last", H + b"\\" + U)                # E1 on the last line
    for b in (H + b"x\n", H + b"x\n\n", H + b"$x\n", H + b"{x\n"):
        add("Lines_nil", b)
        add("LX_nil", b)
        add("B_eof", b)
    add("LX_line", d(b"x\n"))
    # TeX Live's first-line directive (C-89): outside; any other first line
    for first in (b"%&latex\n", b"%&etex\n", b"%&\n", b"%&%&latex\n", b"%&latex\r\n"):
        add("FL_directive", first + d(b"x\n"))
    add("FL_none", d(b"x\n"))
    add("FL_none", b" %&latex\n" + d(b"x\n"))
    add("FL_none", b"\t%&latex\n" + d(b"x\n"))
    add("FL_none", b"%x\n%&latex\n" + d(b"x\n"))
    add("FL_none", b"%%&latex\n" + d(b"\\" + U + b"\n"))
    add("LL_eol_new", d(b"x\n\ny\n"))
    add("LL_eol_new", d(b"$x\n\ny$\n"))
    add("LL_eol_new", d(b"$x\n  \t \ny$\n"))
    add("LL_eol_new", d(b"$$x\n\n$$\n"))
    add("LL_eol_new", d(b"{$x\n\n}$\n"))
    add("LL_eol_mid", d(b"x\ny\n"))
    add("LL_eol_mid", d(b"$$x$\ny$$\n"))
    add("LL_eol_skip", d(b"x\\" + TM + b"\ny\n"))
    add("LL_eol_skip", d(b"$x\\" + MA + b"\n\ny$\n"))
    add("LL_eol_skip", d(b"$x \t\n\ny$\n"))
    add("LL_eol_skip", d(b"x\\" + U + b"\ny\n"))
    add("LL_space_skip", d(b"   x\n\t\ty\n"))
    add("LL_space_skip", d(b"x\\" + TM + b"    y\n"))
    add("LL_space_skip", d(b"x  \t  y\n"))
    add("LL_space_skip", d(b"$$x$ \t $$\n"))
    add("LL_space_skip", d(b"$x\\" + MA + b"   ^2$\n"))
    add("LL_space_emit", d(b"x y\n"))
    add("LL_space_emit", d(b"$ $\n"))
    add("LL_space_emit", d(b"$$x$ y$$\n"))
    add("LL_comment", d(b"x%" + bytes(c for c in range(256) if c not in (10, 13)) + b"\ny\n"))
    add("LL_comment", d(b"$x^%c\n2$\n"))
    add("LL_comment", d(b"$$x$%c\n$\n"))
    add("LL_comment", d(b"x%\\" + U + b" $ } ^^ ~\n"))
    add("LL_comment", d(b"$x%\n\ny$\n"))
    add("LL_comment", H + b"x%")
    add("LL_char", d(SAFE + b"\n"))
    add("LL_char", d(b"$" + SAFE + b"$\n"))
    add("LL_bgroup", d(b"{x}\n"))
    add("LL_bgroup", d(b"{{x}\n"))
    add("LL_egroup", d(b"x}\n"))
    add("LL_egroup", d(b"$x}$\n"))
    add("LL_math", d(b"$x$ $$y$$\n"))
    add("LL_math", d(b"$x$$y$\n"))
    add("LL_sub", d(b"$x_1$\n"))
    add("LL_sub", d(b"x_1\n"))
    add("LL_sup", d(b"$x^2$\n"))
    add("LL_sup", d(b"$x^1^2$\n"))
    add("LL_word", d(b"\\" + U + b"\n"))
    add("LL_word", d(b"x\\" + TM + b"{}y\n"))
    add("LL_word", d(b"x\\" + TM + b"1\n"))
    add("LL_word", d(b"x\\" + TM + b"%c\ny\n"))
    add("LL_word", d(b"\\" + TM + b"$x$\n"))
    add("LL_word", d(b"$\\" + MA + b"_1$\n"))
    add("LL_sym", d(b"\\(x\\)\n"))
    add("LL_sym", d(b"\\[x\\]\n"))
    add("LL_sym", d(b"\\(x\\]\n"))
    add("LL_sym", d(b"x\\(\n\\)\n"))
    # outside the fragment (decided NOT-IN-FRAGMENT, never graded)
    add("LL_hathat", d(b"$x^^41$\n"))
    add("LL_word_hathat", d(b"\\zz^^41\n"))
    add("LL_sym_hathat", d(b"\\^^41\n"))
    for bad in (b"x ~\n", b"x #\n", b"x &\n", b"\xc3\xa9\n", b"\x00\n", b"\x7f\n", b"\x0c\n"):
        add("LL_bad", d(bad))
    add("LL_end", d(b"x\\\ny\n"))
    add("LX_long", d(b"x" * (MAX_LINE_BYTES + 1) + b"\n"))
    # front matter and body
    for k in ("plain", "leading", "comments", "between", "split", "spaced", "crlf",
              "same_line", "par_between", "tabs"):
        add("P_prologue", prologue(rng, k) + b"x\n" + END + b"\n")
        add("P_prologue", prologue(rng, k) + b"\\" + U + b"\n" + END + b"\n")
    for k in ("plain", "space", "newline", "comment", "split", "split2"):
        add("B_end", H + b"x\n" + end_variant(rng, k) + b"\n")
        add("B_end", H + b"$x\n" + end_variant(rng, k) + b"\n")
        add("B_end", H + b"$$x$%\n" + end_variant(rng, k) + b"\n")
        add("B_end", H + b"\n" + end_variant(rng, k) + b"\n")
        add("B_end", H + b"x" + end_variant(rng, k) + trailing(rng))
    add("B_space", d(b"x y\n"))
    add("B_space_script", d(b"$x^ 2$\n"))
    add("B_space_script", d(b"$x^\n2$\n"))
    add("B_space_script", d(b"$x_ %c\n{1}$\n"))
    add("B_space_script", d(b"$x^ \n 2^3$\n"))
    add("B_space_script", d(b"$x^\t{a}^ b$\n"))
    add("B_par_line", d(b"x\n\ny\n"))
    add("B_par_word", d(b"x\\par y\n"))
    add("B_par_word", d(b"$x\\par$\n"))
    add("B_par_word", d(b"$x\\par\n$\n"))
    add("B_word", d(b"\\" + U + b"\n"))
    add("B_word", d(b"\\" + TM + b"\n"))
    add("B_word", d(b"\\" + MA + b"\n"))
    add("B_sym", d(b"\\(x\\)\\[y\\]\n"))
    add("B_sym", d(b"\\[x$$\n"))
    add("B_char", d(b"x\n"))
    add("B_open", d(b"{x}\n"))
    add("B_close", d(b"}\n"))
    add("B_math", d(b"$x$\n"))
    add("B_script", d(b"$x^2_3$\n"))
    # the bounds of Lexer.v / DecideBytes.v, at the bound (graded)
    add("L0-bounds", d(b"x" * MAX_LINE_BYTES + b"\n"))
    add("L0-bounds", d(b"%" + b"c" * (MAX_LINE_BYTES - 1) + b"\nx\n"))
    add("L0-bounds", d(b" " * (MAX_LINE_BYTES - 1) + b"x\n"))
    add("L0-bounds", d(b"$" + b"x" * (MAX_LINE_BYTES - 2) + b"$\n"))
    add("L0-bounds", file_at_bound())
    # the kernel's bounds (Decide.v) at the byte level: exactly 20,000 kernel
    # tokens (19,999 characters and \end{document}; comment-joined lines give
    # no space tokens), in text and in one formula; 200 TeX groups (C-94: a
    # formula is one of them) of braces, of a formula and braces, and of
    # box-and-formula levels (the header's line ends in a comment: its
    # end-of-line space would be a 20,001st token)
    H0 = b"\\documentclass{article}\n\\begin{document}%\n"
    chars = (b"x" * 5000 + b"%\n") * 3 + b"x" * 4999 + b"%\n"
    add("L0-bounds", H0 + chars + END + b"\n")
    add("L0-bounds", H0 + b"$" + (b"x" * 5000 + b"%\n") * 3 + b"x" * 4997 + b"$%\n" + END + b"\n")
    add("L0-bounds", d(b"{" * 200 + b"x" + b"}" * 200 + b"\n"))
    add("L0-bounds", d(b"$" + b"{" * 199 + b"x" + b"}" * 199 + b"$\n"))
    add("L0-bounds", d(b"\\mbox{$" * 100 + b"x" + b"$}" * 100 + b"\n"))
    return f
