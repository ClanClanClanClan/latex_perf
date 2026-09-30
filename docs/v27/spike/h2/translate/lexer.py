"""Lexer for the tangled Pascal that web2c reads (spike H.2, ADR-015).

Follows texk/web2c/web2c/web2c-lexer.l of the pinned revision (r78081) rule by
rule where the rule changes meaning:
  - `{...}` is a comment (tangle's section markers);
  - `ifdef('X')` / `endif('X')` / `ifndef('X')` / `endifn('X')` become C
    preprocessor conditionals in web2c's output; here they are evaluated against
    the pinned build's configuration (DEFINED below, read from the build's
    pdftexd.h and c-auto.h), because that is what the C compiler did;
  - `#...;` is copied to the C output verbatim (one occurrence:
    `#include "texmfmem.h"`); here it is a token the parser skips inside a type
    section;
  - `procedure x; forward;` and `function ...; forward;` are dropped;
  - a `-` directly followed by a digit, when the previous token cannot end an
    operand, is folded into a negative numeric literal (web2c's `negbuf`); the
    `+` in that position is unary plus;
  - identifiers are case-sensitive; keywords are lower case.
"""
import re

DEFINED = {"STAT": True, "INITEX": True, "IPC": True, "TEXMF_DEBUG": False}

KEYWORDS = {
    "and", "array", "begin", "case", "const", "div", "break", "do", "downto", "else", "end", "file",
    "for", "function", "goto", "if", "label", "mod", "noreturn", "not", "of", "or", "procedure",
    "program", "record", "repeat", "then", "to", "type", "until", "var", "while", "others",
}
# web2c-lexer.l: {W} = ({WHITE}|"packed ")+ is skipped, so "packed " is whitespace.

# web2c-lexer.l: last_tok in undef_id_tok..field_id_tok (every identifier kind, hh.b0, hh.b1),
# i_num_tok, r_num_tok, ')' or ']'; NOT a string or character literal
OPERAND_END = {"id", "num", "real", ")", "]"}


class Tok:
    __slots__ = ("kind", "val", "line")

    def __init__(self, kind, val, line):
        self.kind, self.val, self.line = kind, val, line

    def __repr__(self):
        return f"Tok({self.kind},{self.val!r},{self.line})"


_forward = re.compile(r"(procedure|function) [(),:a-z_]+;[ \n\t]*forward;")


def lex(text):
    toks = []
    i, n, line = 0, len(text), 1
    cond = []  # stack of booleans: are we emitting?
    last = None

    def emitting():
        return all(cond)

    def add(kind, val):
        nonlocal last
        if emitting():
            toks.append(Tok(kind, val, line))
            last = kind
    while i < n:
        c = text[i]
        if c == "\n":
            line += 1
            i += 1
            continue
        if c in " \t\r\f":
            i += 1
            continue
        if c == "{":
            j = text.index("}", i)
            line += text.count("\n", i, j)
            i = j + 1
            continue
        m = _forward.match(text, i)
        if m and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] == "_")):
            line += m.group(0).count("\n")
            i = m.end()
            continue
        if c == "#":
            j = text.index(";", i)
            add("cpp", text[i:j])
            line += text.count("\n", i, j)
            i = j  # the ';' is lexed normally, as web2c's rule stops before it
            # web2c: `while ((c = webinput()) && c != ';')` consumes the ';' too
            i += 1
            continue
        m = re.match(r"(ifdef|endif|ifndef|endifn)\('([A-Za-z_]+)'\)", text[i:i + 40])
        if m and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] == "_")):
            kw, name = m.group(1), m.group(2)
            if name not in DEFINED:
                raise SyntaxError(f"line {line}: unknown conditional {name}")
            if kw == "ifdef":
                cond.append(DEFINED[name])
            elif kw == "ifndef":
                cond.append(not DEFINED[name])
            else:
                if not cond:
                    raise SyntaxError(f"line {line}: unbalanced {kw}")
                cond.pop()
            i += m.end()
            continue
        if c == "'":
            j = i + 1
            s = []
            while True:
                if text[j] == "'":
                    if j + 1 < n and text[j + 1] == "'":
                        s.append("'")
                        j += 2
                        continue
                    break
                s.append(text[j])
                j += 1
            val = "".join(s)
            add("char" if len(val) == 1 else "str", val)
            i = j + 1
            continue
        if c.isdigit():
            m = re.match(r"\d+(\.\d+([eE][-+]?\d+)?|[eE][-+]?\d+)?", text[i:])
            s = m.group(0)
            # "1..2": the '..' is a subrange, not a real
            if "." in s and text[i + len(s.split(".")[0]) + 1:i + len(s.split(".")[0]) + 2] == ".":
                s = s.split(".")[0]
            if "." in s or "e" in s.lower():
                add("real", s)
            else:
                add("num", int(s))
            i += len(s)
            continue
        if c.isalpha() or c == "_" or c == "@":
            m = re.match(r"@?[A-Za-z_][A-Za-z_0-9]*", text[i:])
            s = m.group(0)
            if s == "packed" and text[i + 6:i + 7] == " ":  # {W}: "packed " is whitespace
                i += 7
                continue
            if s in KEYWORDS or s in ("@define", "@field"):
                add(s, s)
            else:
                add("id", s)
            i += len(s)
            continue
        two = text[i:i + 2]
        if two in (":=", "..", "<=", ">=", "<>"):
            add(two, two)
            i += 2
            continue
        if c == "-" or c == "+":
            if last in OPERAND_END:
                add(c, c)
                i += 1
                continue
            # unary: web2c folds '-' + digits into a negative literal
            j = i + 1
            while j < n and text[j] in " \t":
                j += 1
            if c == "-" and j < n and text[j].isdigit():
                m = re.match(r"\d+(\.\d+([eE][-+]?\d+)?)?", text[j:])
                s = m.group(0)
                if "." in s and text[j + len(s.split(".")[0]) + 1:j + len(s.split(".")[0]) + 2] == ".":
                    s = s.split(".")[0]
                if "." in s:
                    add("real", "-" + s)
                else:
                    add("num", -int(s))
                i = j + len(s)
                continue
            add("u" + c, c)
            i += 1
            continue
        if c in "*/=<>()[],.;:^":
            add(c, c)
            i += 1
            continue
        raise SyntaxError(f"line {line}: unexpected character {c!r}")
    if cond:
        raise SyntaxError("unterminated ifdef")
    toks.append(Tok("eof", None, line))
    return toks
