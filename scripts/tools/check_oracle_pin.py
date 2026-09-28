#!/usr/bin/env python3
"""Gate: every pdflatex grade the project publishes names the ONE oracle.

WHY (ADR-012 decision 7, OPEN-118). Every earlier pin check compared the
`pdflatex --version` banner with `pdfTeX 3.141592653-2.6-1.40.29`. The banner
pins the engine binary and nothing else: the maintainer's laptop printed that
exact banner while its macro layer differed from CI's image in 190 TeX Live
packages (89 at newer revisions, 94 absent from its package database,
pdfmanagement among them). So a banner check passed while the thing it was
meant to guarantee -- that two graders agree -- was false.

The oracle is now the digest-pinned image in tex-oracle.yml, run through
`scripts/tools/_oracle.py`. This gate is pure (no TeX, no docker, no corpus)
and checks four things:

  1. `_oracle.py`'s recorded tree fingerprints were measured for the digest
     tex-oracle.yml pins, for both platform images (arm64 and amd64), and the
     two agree on the macro layer. A re-pin that forgets to re-measure fails.
  2. Every graded artefact in GRADED records `image` equal to the pinned
     digest, the pinned engine version, a `backend` in {container, native},
     and, for its recorded `arch`, the `tlpdb_sha256`, `macro_layer_sha256`
     and `fmt_sha256` that `_oracle.TREE_FINGERPRINTS` holds for that
     architecture. The image string alone is not evidence: two of these
     blocks were stamped by hand, and a hand edit of `image` satisfied the
     old check. An artefact still carrying a host-graded block fails, unless
     it is in PRE_BASELINE with the ledger row that removes it.
  3. PRE_BASELINE is pinned to its exact contents: widening it silently fails,
     and an entry whose artefact has since been re-graded fails too.
  4. No tracked code starts a TeX engine or passes a FORMAT SELECTOR outside
     `_oracle.py` and `_oracle.sh`. The vocabulary is ONE table,
     `_oracle.TEX_ENGINE_BINARIES` (measured from the pinned image's
     bin/<arch>/: every engine, every format-named link such as `mllatex`,
     `pdflatex-dev`, `pdfjadetex`, and every shipped front end such as
     `latexmk`, `arara`, `fmtutil`), the same table image_command refuses;
     the selector is `_oracle.FMT_SELECTOR` (`&fmt`, `-fmt=`/`--fmt`,
     `-progname=`). Scanned: every tracked .py, .sh/.bash/.zsh/.ksh/.command,
     Makefile/.mk, .ml, other-language and workflow file, and any tracked
     file without a known extension whose shebang names a shell or python.
     The rules, each with a kill-test in check_gate_selftests.py:
       Python  every string literal that names an engine, found by the
               tokenizer (so a list split over lines is still one list), is a
               finding unless it is data: a dict key (`"pdflatex": ...`), the
               value of a recorded-metadata key (`"engine": "pdflatex"`, the
               keys in DATA_KEYS only), a subscript (`x["pdflatex"]`), an
               argument of .get/.setdefault/.pop, an operand of ==, !=, in,
               or an argument of the oracle's own `run_engine(...)`. Bytes
               literals, adjacent literals (`"pdf" "latex"`) and `+`/join
               chains of literals are joined first. THEN every non-literal
               EXPRESSION whose value is a function of literals only is
               EVALUATED by a small interpreter (no eval): + * % on strings,
               f-strings, str methods (join/format/replace/split/decode/...),
               slicing, chr/bytes/str, base64/b16/b32/hex decoding, a
               comprehension or generator over a literal iterable, either
               branch of a conditional, and a name bound exactly once in the
               file (`P = "pdf"; P + "latex"`). Data positions are exempt as
               for literals.
       shell   a bare engine token anywhere on a code line (comments
               stripped), except inside an echo/printf message. The message
               exemption covers ONE command (the line is split at `;`, `&&`,
               `||`, `|` outside quotes) and none at all when a later stage of
               the pipeline RUNS its input (`echo 'pdflatex t' | sh`, `| xargs`,
               `| bash`); `printf -v` is an assignment, and its value is
               computed. An engine the SHELL makes is resolved: assembled from
               a variable (`${P}latex`), dequoted from one word (`"pdf"latex`,
               `pdf\\latex`, an ANSI-C `$'pdf\\x6catex'`), a parameter
               expansion's default (`${E:-pdftex}`), a brace expansion
               (`pdf{latex,}`), a glob matching an engine name (`pdfla[t]ex`,
               at least three literal letters). A `case` label is a pattern;
               the value of `jq --arg NAME VALUE` is data. Makefiles are
               scanned as shell after GNU make's text functions over literal
               arguments are evaluated (`$(subst X,,pdfXlatex)`).
       other   in a tracked .c/.h/.rs/.js/.ts/.rb/.pl/.go/.lua file, a
               quoted literal that is an engine or an engine command line.
       OCaml   a file that spawns processes (Sys.command, Unix.create_process,
               Unix.open_process*, Unix.exec*) must not name an engine as a
               word of a string literal.
       workflow  as shell, minus `name:` keys and YAML mapping KEYS (their
               values are scanned), with an exact allow-list of the in-image
               canary lines of tex-oracle.yml.
     KNOWN RESIDUALS (OPEN-118 known limit (g)): a static scan cannot see a
     value that is not a function of the file's literals -- a name read from
     the environment, a file, argv or the network; a variable bound more than
     once or by a parameter/loop/import; a call the interpreter does not
     model (any function of one's own, `codecs.decode(s, "rot13")`, `ord`
     arithmetic through a loop); `eval`/`exec`/`sh -c`/`bash -c` of a string
     built at run time; a `DATA_KEYS` value later used as argv; a function of
     one's own named `run_engine`; shell variables assigned in one command
     and expanded in another (`E=pdf; ${E}latex` IS caught by the `${P}latex`
     rule, `read E; $E` is not), `eval`, `source` of a generated file, and
     make's `$(shell ...)`/`$(call ...)`/`$(eval ...)`; other languages'
     string operations (only literals are scanned there); an untracked file;
     and `aleph`, the one vocabulary word not scanned (SCAN_DATA_WORDS: it is
     also the LaTeX symbol \\aleph, listed as data in this repository).

Run: python3 scripts/tools/check_oracle_pin.py --repo .
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import _oracle  # noqa: E402

# (artefact, key path to the recorded oracle block)
GRADED = (
    ("corpora/real_roots/results.json", ("oracle",)),
    ("corpora/real_roots/manifest.json", ("oracle",)),
    ("corpora/real_roots/results_sample2.json", ("oracle",)),
    # Sample 3, the VIRGIN North-Star sample (OPEN-119): graded once, under
    # the pinned image, and both of its files record who graded it.
    ("corpora/real_roots/results_sample3.json", ("oracle",)),
    ("corpora/real_roots/manifest_sample3.json", ("oracle",)),
    ("corpora/apply_fixes_real/results.json", ("provenance", "oracle")),
    ("corpora/apply_fixes_real/results_virgin.json", ("provenance", "oracle")),
    ("corpora/apply_fixes_real/results_fresh.json", ("provenance", "oracle")),
    ("corpora/strict_battery/manifest.json", ("provenance", "oracle_provenance")),
    ("corpora/false_ready/manifest.json", ("oracle",)),
    ("corpora/apply_fixes/manifest.json", ("oracle",)),
    ("corpora/oracle_baseline/equivalence.json", ("oracle",)),
)

# Graded artefacts NOT re-graded in the oracle-baseline change, each with the
# reason and the ledger row that removes it. Exact contents are pinned.
PRE_BASELINE = {
    "corpora/apply_fixes_real/rule_attribution_400_719.json":
        "OPEN-118: a greedy per-rule bisection over 320 papers (thousands of "
        "compiles); its conclusions are per-rule, and re-grading it is a new "
        "experiment, not a re-grade. Its engine field names the host TeX Live.",
    "corpora/apply_fixes_real/guard_simulation.json":
        "OPEN-118: a hunk-reversion SIMULATION of a guard that was never built "
        "(OPEN-109); historical evidence for a decision already taken.",
    "corpora/apply_fixes_real/policy_confirmation_2600.json":
        "OPEN-118: the sealed-window confirmation of OPEN-112's allow-list, "
        "taken under the host TeX Live.",
    "corpora/apply_fixes_real/fix_meaning_audit.json":
        "OPEN-118: the per-rule meaning audit (word/layout diffs of PDFs); its "
        "rc columns were graded by the host TeX Live.",
}
PRE_BASELINE_SIZE = 4

# Files allowed to start pdflatex: the oracle itself. And files not scanned
# because they NAME engines as data about this scan: this gate (its ENGINES
# tuple) and the selftest harness (its kill-test payloads are the evasion
# shapes, written out).
ORACLE_FILES = {"scripts/tools/_oracle.py", "scripts/tools/_oracle.sh"}
SCANNER_FILES = {"scripts/tools/check_oracle_pin.py",
                 "scripts/tools/check_gate_selftests.py"}
# THE ENGINE VOCABULARY IS _oracle.TEX_ENGINE_BINARIES (C-91 review round 4):
# one table, measured from the pinned image's bin/<arch>/, which image_command
# refuses too. Until round 4 this gate kept its own 11 names while _oracle kept
# 30, and `pdflatex-dev`, `mllatex`, `pdfjadetex`, `lualatex-dev` (each a link
# to pdfTeX that loads a LaTeX format) scanned clean (MEASURED RC 0).
# One exception, pinned: `aleph` (the Omega-successor engine, shipped in the
# image) is also the LaTeX symbol \aleph, and this repository lists it as a
# macro name in data (scripts/test/validate_v24_integration.py). It stays in
# the vocabulary image_command refuses; the scan does not look for it.
# RESIDUAL, recorded in OPEN-118 (g).
SCAN_DATA_WORDS = frozenset({"aleph"})
ENGINES = tuple(sorted(_oracle.TEX_ENGINE_BINARIES - SCAN_DATA_WORDS))
_ENG_ALT = "|".join(re.escape(e) for e in sorted(ENGINES, key=len, reverse=True))
ENGINE_LITERAL = re.compile(rf"^(\S*/)?({_ENG_ALT})$")
# A FORMAT SELECTOR (`&fmt`, `-fmt=`/`--fmt`, `-progname=`): _oracle's, the
# same one image_command refuses. A literal that is one is a finding like an
# engine name: it has no use but as an argument to a TeX engine.
FMT_SELECTOR = _oracle.FMT_SELECTOR
# A string that is a shell command line starting with an engine.
ENGINE_CMDLINE = re.compile(rf"^\s*(\S*/)?({_ENG_ALT})\s+(-|&|\S+\.tex\b|\{{|\$|\"|')")
BARE_TOKEN = re.compile(rf"(^|[^A-Za-z0-9_./-])({_ENG_ALT})([^A-Za-z0-9_.-]|$)")
# `printf -v VAR` ASSIGNS the formatted string: not a message (see
# _sh_printf_v). A message stops being one when the pipeline feeds it to a
# shell (see SH_RUNS_STDIN).
SH_MESSAGE = re.compile(r"^\s*(echo|printf(?!\s+-v\b)|die_infra|die|warn|log)\b")
# A pipeline stage that RUNS its standard input as code or as arguments.
SH_RUNS_STDIN = re.compile(r"^\s*(\S*/)?(sudo\s+)?(env\s+)?(\S*/)?"
                           r"(sh|bash|dash|zsh|ksh|mksh|busybox|eval|source|xargs|"
                           r"python3?|perl|ruby|tclsh)\b")
ML_SPAWN = re.compile(r"Sys\.command|create_process|open_process|Unix\.exec")
# The engine as a WORD of the literal: not `.tex`/`main.tex` (a file name),
# which `\b` matched once `tex` joined ENGINES; a path prefix still counts.
ML_LITERAL = re.compile(rf'"[^"\n]*(?<![A-Za-z0-9_.-])({_ENG_ALT})(?![A-Za-z0-9_.-])[^"\n]*"')
DATA_CALLS = {"get", "setdefault", "pop"}
# Dict keys whose engine-valued VALUE is recorded metadata, not a command.
DATA_KEYS = {"engine", "declared_compiler", "compiler", "protocol"}
# An engine name assembled at run time in shell: `${P}latex`, `$P"latex"`,
# `pdf${X}`, `pdf$X`.
SH_BUILT = re.compile(r"(\$\{?[A-Za-z_][A-Za-z0-9_]*\}?|\$\([^)]*\))[\"']?(la)?tex(mk)?\b"
                      r"|\b(pdf|xe|lua)[\"']?\$\{?[A-Za-z_(]")
SH_SPLIT = re.compile(r"&&|\|\||;|\|")
OTHER_CODE_EXT = (".c", ".h", ".rs", ".js", ".mjs", ".ts", ".rb", ".pl",
                  ".pm", ".go", ".lua", ".java")
OTHER_LITERAL = re.compile(r"\"((?:[^\"\\\n]|\\.)*)\"|'((?:[^'\\\n]|\\.)*)'")
COMPARE_OPS = {"==", "!=", "in"}
# Workflow lines that run an engine INSIDE the pinned image (the oracle
# itself). Exact stripped lines, pinned by count: a new one fails.
WORKFLOW_ALLOW = {
    ".github/workflows/tex-oracle.yml": (
        'got=$(docker run --rm "$TEX_IMAGE" pdflatex --version | head -1)',
        'if ! pdflatex -interaction=nonstopmode -halt-on-error canary.tex >canary.stdout 2>&1 \\',
        '&& pdflatex -interaction=nonstopmode -halt-on-error t.tex >t.log 2>&1 \\',
    ),
}
FINGERPRINT_KEYS = ("tlpdb_sha256", "macro_layer_sha256", "fmt_sha256")
BACKENDS = {"container", "native"}


def _is_engine_literal(val: str) -> bool:
    return bool(ENGINE_LITERAL.match(val) or ENGINE_CMDLINE.match(val)
                or FMT_SELECTOR.match(val))


def _py_string_value(tok: str) -> str | None:
    """The text of a string token, prefixes and quotes removed. f-strings
    keep their `{...}` fields verbatim, which is what ENGINE_CMDLINE needs."""
    m = re.match(r"^([rRbBuUfF]*)('\'\'|\"\"\"|'|\")(.*)\2$", tok, re.S)
    if not m:
        return None
    # Bytes literals are scanned too: `subprocess.run([b"pdflatex", t])`
    # starts an engine exactly as the str literal does.
    return m.group(3)


def scan_python(text: str) -> list[tuple[int, str]]:
    """(line, literal) for every engine literal in executable position."""
    import io
    import tokenize
    try:
        toks = list(tokenize.generate_tokens(io.StringIO(text).readline))
    except (tokenize.TokenError, SyntaxError, IndentationError):
        # Untokenizable file: fall back to a line scan for engine literals.
        return [(n, m.group(0)) for n, line in enumerate(text.split("\n"), 1)
                for m in [re.search(rf"[\"']({_ENG_ALT})[\s\"']", line)] if m
                and not line.lstrip().startswith("#")]
    skip = (tokenize.NL, tokenize.NEWLINE, tokenize.COMMENT, tokenize.INDENT,
            tokenize.DEDENT)
    raw = [t for t in toks if t.type not in skip]
    # Python >= 3.12 tokenizes an f-string as FSTRING_START ... FSTRING_END;
    # collapse each into ONE string unit carrying its source text, so
    # `f"pdflatex {t}"` is seen exactly as it is on 3.11.
    fs_start = getattr(tokenize, "FSTRING_START", None)
    fs_end = getattr(tokenize, "FSTRING_END", None)
    lines = text.split("\n")

    def src(a, b):
        (l0, c0), (l1, c1) = a, b
        if l0 == l1:
            return lines[l0 - 1][c0:c1]
        return "\n".join([lines[l0 - 1][c0:]] + lines[l0:l1 - 1] + [lines[l1 - 1][:c1]])

    class _U:
        def __init__(self, type_, string, start):
            self.type, self.string, self.start = type_, string, start
    sig, j = [], 0
    while j < len(raw):
        t = raw[j]
        if fs_start is not None and t.type == fs_start:
            depth, k = 1, j + 1
            while k < len(raw) and depth:
                depth += (raw[k].type == fs_start) - (raw[k].type == fs_end)
                k += 1
            sig.append(_U(tokenize.STRING, src(t.start, raw[k - 1].end), t.start))
            j = k
            continue
        sig.append(t)
        j += 1
    # Implicit concatenation: `"pdf" "latex"` is ONE literal to Python, so
    # adjacent string units are joined before matching (quotes re-added so
    # _py_string_value can strip them).
    joined = []
    for t in sig:
        if (t.type == tokenize.STRING and joined
                and joined[-1].type == tokenize.STRING):
            a = _py_string_value(joined[-1].string)
            b = _py_string_value(t.string)
            if a is not None and b is not None:
                joined[-1] = _U(tokenize.STRING, '"' + a + b + '"', joined[-1].start)
                continue
        joined.append(t)
    sig = _fold_python_concat(joined, _U)
    oracle_args = _oracle_call_spans(sig)
    hits = []
    for i, t in enumerate(sig):
        if t.type != tokenize.STRING or i in oracle_args:
            continue
        val = _py_string_value(t.string)
        if val is None or not _is_engine_literal(val):
            continue
        prev = sig[i - 1].string if i else ""
        nxt = sig[i + 1].string if i + 1 < len(sig) else ""
        before_prev = sig[i - 2].string if i >= 2 else ""
        if True:  # data positions exempt both an engine name and a command line
            if nxt == ":" and prev in ("{", ","):
                continue                       # dict key
            if (prev == ":" and i >= 2 and sig[i - 2].type == tokenize.STRING
                    and _py_string_value(sig[i - 2].string) in DATA_KEYS):
                continue                       # recorded metadata {"engine": ...}
            if prev == "[" and nxt == "]" and before_prev not in ("", "=", "(", ",", "[", "return"):
                continue                       # subscript x["pdflatex"]
            if prev == "(" and before_prev in DATA_CALLS:
                continue                       # d.get("pdflatex")
            if prev in COMPARE_OPS or nxt in COMPARE_OPS or (prev == "not" and nxt != ","):
                continue                       # comparison operand
        hits.append((t.start[0], val))
    seen = {n for n, _ in hits}
    hits += [(n, v) for n, v in scan_python_folded(text) if n not in seen]
    return sorted(hits)


# The oracle's own engine API. Its ARGUMENTS name an engine and its flags
# (`run_engine(jd, _oracle.ENGINE_PDFTEX, ["-ini", "-progname=pdflatex", ...])`
# in gen_contract.py), which is the one legitimate place for them: the oracle
# runs them in the pinned image. RESIDUAL: a function of one's own named
# `run_engine` that spawns what it is given is exempt too.
ORACLE_CALLS = {"run_engine"}


def _oracle_call_spans(sig: list) -> set:
    """Indices of the tokens inside the parentheses of an ORACLE_CALLS call."""
    inside = set()
    for k in range(len(sig) - 1):
        if sig[k].string in ORACLE_CALLS and sig[k + 1].string == "(":
            depth, j = 0, k + 1
            while j < len(sig):
                if sig[j].string in ("(", "[", "{"):
                    depth += 1
                elif sig[j].string in (")", "]", "}"):
                    depth -= 1
                    if depth == 0:
                        break
                inside.add(j)
                j += 1
    return inside


# STATICALLY RESOLVABLE EXPRESSIONS (C-91 review round 4). The token scan sees
# literals; the round-4 review MEASURED expressions of literals that it did
# not resolve: `('pdf') + ('latex')`, `''.join(p for p in ('pdf', 'latex'))`,
# `b'pdf%slatex' % b''`. So every expression whose value is a function of
# literals only is EVALUATED (a small interpreter, no eval()) and its value
# matched like a literal: + and * on strings, % formatting, f-strings, str
# methods (join/format/replace/upper/lower/strip/split/decode/encode/...),
# indexing and slicing, chr, bytes/bytearray/str of literals, base64/b16/b32
# and bytes.fromhex decoding, a generator or list comprehension over a literal
# iterable, a conditional expression (either branch), and a NAME bound exactly
# once in the file to such an expression (`P = "pdf"; P + "latex"`). Data
# positions are exempt as in the token scan (a comparison operand, a dict key,
# a DATA_KEYS value, a subscript, an argument of .get/.setdefault/.pop, an
# ORACLE_CALLS argument).
_STR_METHODS = {"join", "format", "replace", "upper", "lower", "strip",
                "lstrip", "rstrip", "split", "rsplit", "decode", "encode",
                "removeprefix", "removesuffix", "title", "casefold",
                "capitalize", "swapcase", "zfill", "center", "ljust", "rjust",
                "translate", "expandtabs"}
_DECODERS = {"b64decode", "b32decode", "b16decode", "a85decode", "b85decode",
             "urlsafe_b64decode", "standard_b64decode", "unhexlify", "fromhex"}
_FOLD_MAX = 4096


class _NoFold(Exception):
    pass


def _fold(node, names, env, depth=0):
    """The value of `node` if it is a function of literals only, else raise
    _NoFold. `names` maps a once-bound module name to its value node."""
    import ast
    import base64
    import binascii
    if depth > 40:
        raise _NoFold
    f = lambda n, e=env: _fold(n, names, e, depth + 1)  # noqa: E731
    if isinstance(node, ast.Constant):
        return node.value
    if isinstance(node, ast.Name):
        if node.id in env:
            return env[node.id]
        if node.id in names:
            return f(names[node.id])
        raise _NoFold
    if isinstance(node, (ast.Tuple, ast.List, ast.Set)):
        return tuple(f(e) for e in node.elts)
    if isinstance(node, ast.JoinedStr):
        out = ""
        for v in node.values:
            if isinstance(v, ast.Constant):
                out += v.value
            else:
                x = f(v.value)
                x = {115: str, 114: repr, 97: ascii}.get(v.conversion, lambda y: y)(x)
                spec = f(v.format_spec) if v.format_spec is not None else ""
                out += format(x, spec)
        return out
    if isinstance(node, ast.BinOp):
        a, b = f(node.left), f(node.right)
        if isinstance(node.op, ast.Add) and type(a) is type(b) and isinstance(a, (str, bytes, tuple)):
            r = a + b
        elif isinstance(node.op, ast.Mult) and isinstance(a, (str, bytes)) and isinstance(b, int) and 0 <= b * len(a) <= _FOLD_MAX:
            r = a * b
        elif isinstance(node.op, ast.Mult) and isinstance(b, (str, bytes)) and isinstance(a, int) and 0 <= a * len(b) <= _FOLD_MAX:
            r = b * a
        elif isinstance(node.op, ast.Mod) and isinstance(a, (str, bytes)):
            try:
                r = a % b
            except (TypeError, ValueError, KeyError):
                raise _NoFold
        elif isinstance(a, int) and isinstance(b, int) and not isinstance(node.op, (ast.Pow, ast.LShift)):
            try:
                r = {ast.Add: int.__add__, ast.Sub: int.__sub__, ast.Mult: int.__mul__,
                     ast.FloorDiv: int.__floordiv__, ast.Mod: int.__mod__,
                     ast.BitOr: int.__or__, ast.BitAnd: int.__and__,
                     ast.BitXor: int.__xor__}[type(node.op)](a, b)
            except (KeyError, ZeroDivisionError):
                raise _NoFold
        else:
            raise _NoFold
        return r
    if isinstance(node, ast.Subscript):
        v = f(node.value)
        sl = node.slice
        if isinstance(sl, ast.Slice):
            idx = slice(*(f(x) if x is not None else None for x in (sl.lower, sl.upper, sl.step)))
        else:
            idx = f(sl)
        try:
            return v[idx]
        except (TypeError, IndexError, KeyError, ValueError):
            raise _NoFold
    if isinstance(node, ast.IfExp):
        # Either branch may run: return the first that is an engine literal.
        vals = []
        for br in (node.body, node.orelse):
            try:
                vals.append(f(br))
            except _NoFold:
                pass
        for v in vals:
            if _folded_is_engine(v):
                return v
        raise _NoFold
    if isinstance(node, (ast.GeneratorExp, ast.ListComp)):
        if len(node.generators) != 1 or node.generators[0].ifs or node.generators[0].is_async:
            raise _NoFold
        g = node.generators[0]
        if not isinstance(g.target, ast.Name):
            raise _NoFold
        it = f(g.iter)
        if not isinstance(it, (str, bytes, tuple)) or len(it) > _FOLD_MAX:
            raise _NoFold
        return tuple(f(node.elt, dict(env, **{g.target.id: x})) for x in it)
    if isinstance(node, ast.Call) and not node.keywords:
        fn = node.func
        args = [f(a) for a in node.args]
        if isinstance(fn, ast.Name):
            try:
                if fn.id == "chr" and len(args) == 1 and isinstance(args[0], int):
                    return chr(args[0])
                if fn.id in ("str", "bytes", "bytearray") and len(args) <= 3:
                    if fn.id == "str" and len(args) == 1:
                        return str(args[0])
                    return {"str": str, "bytes": bytes, "bytearray": bytes}[fn.id](*args)
                if fn.id in ("tuple", "list", "reversed", "sorted") and len(args) == 1:
                    return tuple({"reversed": reversed, "sorted": sorted}.get(fn.id, tuple)(args[0]))
            except (TypeError, ValueError, OverflowError, UnicodeError):
                raise _NoFold
            raise _NoFold
        if isinstance(fn, ast.Attribute):
            if fn.attr in _DECODERS and len(args) == 1:
                try:
                    if fn.attr == "fromhex":
                        return bytes.fromhex(args[0])
                    if fn.attr == "unhexlify":
                        return binascii.unhexlify(args[0])
                    return getattr(base64, fn.attr)(args[0])
                except (TypeError, ValueError, binascii.Error, AttributeError):
                    raise _NoFold
            if fn.attr in _STR_METHODS:
                recv = f(fn.value)
                if not isinstance(recv, (str, bytes)):
                    raise _NoFold
                try:
                    r = getattr(recv, fn.attr)(*args)
                except (TypeError, ValueError, AttributeError, UnicodeError):
                    raise _NoFold
                return tuple(r) if isinstance(r, list) else r
        raise _NoFold
    raise _NoFold


def _folded_is_engine(v) -> bool:
    if isinstance(v, bytes):
        v = v.decode("latin-1")
    return isinstance(v, str) and _is_engine_literal(v)


def _once_bound_names(tree) -> dict:
    """Module-wide: name -> value node, for a name bound EXACTLY once, by a
    plain `NAME = expr` / `NAME: T = expr`, and in no other way."""
    import ast
    count, value = {}, {}
    for n in ast.walk(tree):
        if isinstance(n, ast.Name) and isinstance(n.ctx, (ast.Store, ast.Del)):
            count[n.id] = count.get(n.id, 0) + 1
        elif isinstance(n, ast.arg):
            count[n.arg] = count.get(n.arg, 0) + 2
        elif isinstance(n, (ast.Import, ast.ImportFrom)):
            for a in n.names:
                nm = (a.asname or a.name).split(".")[0]
                count[nm] = count.get(nm, 0) + 2
        elif isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            count[n.name] = count.get(n.name, 0) + 2
        elif isinstance(n, (ast.Global, ast.Nonlocal)):
            for nm in n.names:
                count[nm] = count.get(nm, 0) + 2
        if isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name):
            value[n.targets[0].id] = n.value
        elif isinstance(n, ast.AnnAssign) and isinstance(n.target, ast.Name) and n.value is not None:
            value[n.target.id] = n.value
    return {k: v for k, v in value.items() if count.get(k) == 1}


def scan_python_folded(text: str) -> list[tuple[int, str]]:
    """(line, value) for every NON-literal expression that folds (see _fold)
    to an engine name, an engine command line or a format selector, outside
    a data position."""
    import ast
    try:
        tree = ast.parse(text)
    except (SyntaxError, ValueError):
        return []
    names = _once_bound_names(tree)
    parent = {}
    for n in ast.walk(tree):
        for c in ast.iter_child_nodes(n):
            parent[c] = n

    def exempt(node) -> bool:
        cur = node
        while cur in parent:
            par = parent[cur]
            if isinstance(par, ast.Compare):
                return True
            if isinstance(par, ast.Dict):
                if cur in par.keys:
                    return True
                i = par.values.index(cur) if cur in par.values else -1
                k = par.keys[i] if i >= 0 else None
                if isinstance(k, ast.Constant) and k.value in DATA_KEYS:
                    return True
            if isinstance(par, ast.Subscript) and cur is par.slice:
                return True
            if isinstance(par, ast.Call):
                fn = par.func
                nm = fn.attr if isinstance(fn, ast.Attribute) else getattr(fn, "id", None)
                if nm in ORACLE_CALLS:
                    return True
                if nm in DATA_CALLS and cur in par.args and cur is par.args[0]:
                    return True
                if cur is not fn:
                    return False
            if isinstance(par, (ast.stmt,)):
                return False
            cur = par
        return False

    hits = []

    def visit(node):
        composite = not isinstance(node, (ast.Constant, ast.Name, ast.Tuple,
                                          ast.List, ast.Set, ast.expr_context))
        if isinstance(node, ast.expr) and composite:
            try:
                v = _fold(node, names, {})
            except (_NoFold, RecursionError, MemoryError, OverflowError):
                v = None
            vals = v if isinstance(v, tuple) else (v,)
            if any(_folded_is_engine(x) for x in vals) and not exempt(node):
                shown = next(x for x in vals if _folded_is_engine(x))
                hits.append((node.lineno, shown.decode("latin-1")
                             if isinstance(shown, bytes) else shown))
                return
        for c in ast.iter_child_nodes(node):
            visit(c)
    visit(tree)
    return hits


def _fold_python_concat(sig: list, unit) -> list:
    """Statically resolvable string CONCATENATION, folded into one unit
    (OPEN-118 known limit (g), C-91): `"pdf" + "latex"` (a chain of string
    literals joined by `+`) and `"SEP".join([...])` / `"SEP".join((...))` over
    string literals only. Before this the scan saw two harmless literals
    (MEASURED RC 0 by the round-3 re-review). The folded unit keeps the
    tokens around the WHOLE expression as its neighbours, so the data-position
    exemptions still apply to it. A concatenation with any non-literal operand
    (a variable, a call, `%`, an f-string field) is not resolvable here."""
    import tokenize
    S = tokenize.STRING

    def val(t):
        return _py_string_value(t.string) if t.type == S else None
    out, i = [], 0
    while i < len(sig):
        t = sig[i]
        # "SEP".join(["a", "b"])  or  "SEP".join(("a", "b"))
        if (val(t) is not None and i + 3 < len(sig) and sig[i + 1].string == "."
                and sig[i + 2].string == "join" and sig[i + 3].string == "("):
            j = i + 4
            close = None
            if j < len(sig) and sig[j].string in ("[", "("):
                close = "]" if sig[j].string == "[" else ")"
                j += 1
            parts, ok = [], True
            while j < len(sig) and sig[j].string != (close or ")"):
                v = val(sig[j])
                if v is None:
                    ok = False
                    break
                parts.append(v)
                j += 1
                if j < len(sig) and sig[j].string == ",":
                    j += 1
            if ok and parts and j < len(sig):
                if close:
                    j += 1  # past the inner ] or )
                if j < len(sig) and sig[j].string == ")":
                    out.append(unit(S, '"' + val(t).join(parts) + '"', t.start))
                    i = j + 1
                    continue
        # "a" + "b" + "c"
        if (val(t) is not None and i + 2 < len(sig) and sig[i + 1].string == "+"
                and val(sig[i + 2]) is not None):
            acc, j = val(t), i
            while (j + 2 < len(sig) and sig[j + 1].string == "+"
                   and val(sig[j + 2]) is not None):
                acc += val(sig[j + 2])
                j += 2
            out.append(unit(S, '"' + acc + '"', t.start))
            i = j + 1
            continue
        out.append(t)
        i += 1
    return out


# A shell quoted span: an ANSI-C `$'...'` (backslash escapes ARE processed,
# so `$'pdf\x6catex'` is `pdflatex`), a double-quoted or a single-quoted one.
SH_QUOTED = re.compile(r"""\$'(?:[^'\\]|\\.)*'|\"(?:[^\"\\]|\\.)*\"|'[^']*'""")
_ANSI_C = re.compile(r"\$'((?:[^'\\]|\\.)*)'")
_ANSI_ESC = re.compile(r"\\(x[0-9A-Fa-f]{1,2}|u[0-9A-Fa-f]{1,4}|U[0-9A-Fa-f]{1,8}|"
                       r"[0-7]{1,3}|c.|.)", re.S)
_ANSI_SIMPLE = {"a": "\a", "b": "\b", "e": "\x1b", "E": "\x1b", "f": "\f",
                "n": "\n", "r": "\r", "t": "\t", "v": "\v"}


def _ansi_c_decode(body: str) -> str:
    """The text bash makes of the body of `$'...'`."""
    def one(m):
        e = m.group(1)
        if e[0] in "xuU":
            return chr(int(e[1:], 16))
        if e[0] in "01234567":
            return chr(int(e, 8) & 0xFF)
        if e[0] == "c" and len(e) == 2:
            return chr(ord(e[1]) & 0x1F)
        return _ANSI_SIMPLE.get(e, e)
    return _ANSI_ESC.sub(one, body)


def _sh_quoted_inner(tok: str) -> str:
    """The text a quoted span stands for (ANSI-C escapes decoded)."""
    if tok.startswith("$'"):
        return _ansi_c_decode(tok[2:-1])
    return tok[1:-1]


# A `case` label at the start of a command (`tex)  cp "$f" "$d" ;;`): a
# PATTERN, not a command, so it is removed before the command is scanned.
SH_CASE_LABEL = re.compile(r"^\s*[A-Za-z0-9_.*?|\[\]\"'-]+\)(\s|$)")


YAML_KEY = re.compile(r"^\s*-?\s*[A-Za-z_][A-Za-z0-9_-]*:(?=\s|$)")


def scan_shell(text: str, allow: tuple = (), make: bool = False,
               yaml: bool = False) -> list[tuple[int, str]]:
    """A shell line starts an engine when the engine is a bare word OUTSIDE
    quotes (`pdflatex x.tex`, `PDF=pdflatex`, `cmd=(pdflatex -x)`), or when a
    quoted word IS an engine or an engine command line (`PDF="pdflatex"`,
    `sh -c 'pdflatex x.tex'`). An engine named inside a longer quoted string
    is a message or a pattern (`echo "... pdflatex failed"`, `grep 'pdftex\\|
    pdflatex'`), and `x['pdflatex']` is a subscript."""
    hits = []
    for n, line in enumerate(text.split("\n"), 1):
        code = line.split("#", 1)[0] if not line.lstrip().startswith("#") else ""
        if not code.strip():
            continue
        if re.match(r"^\s*-?\s*name:", code):
            continue                           # a workflow step's display name
        if yaml:
            # A YAML mapping KEY (`context: .`, `with:`) is not a command; its
            # VALUE is still scanned (`run: pdflatex t.tex` is a finding).
            code = YAML_KEY.sub(" ", code, count=1)
        if line.strip() in allow:
            continue
        hit = False
        segs = _sh_commands(code)
        # `echo 'pdflatex t.tex' | sh`: a message the pipeline RUNS is code.
        runs_stdin = any(SH_RUNS_STDIN.match(sg) for sg in segs[1:])
        if make:
            code = _make_eval(code)
            segs = _sh_commands(code)
        for seg in segs:
            seg = SH_CASE_LABEL.sub(" ", seg, count=1)
            seg = SH_JQ_ARG.sub(" ", seg) if re.search(r"(^|[\s(`])jq\s", seg) else seg
            if SH_MESSAGE.match(seg) and not runs_stdin:
                continue                       # this ONE command is a message
            if _sh_expanded_engine(seg):
                hit = True
            unquoted = SH_QUOTED.sub('""', seg)
            # Brace groups expanded first, as the shell does: `pdf{latex,}` is
            # `pdflatex pdf`, and `cp a.{tex,log} d/` is `a.tex a.log` (no
            # bare `tex`, which the raw text `{tex,` looked like).
            unquoted = " ".join(x for w in SH_WORD.findall(unquoted)
                                for x in (_brace_expand(w) if "{" in w else [w]))
            if BARE_TOKEN.search(unquoted) or SH_BUILT.search(
                    SH_QUOTED.sub(lambda m: m.group(0) if m.group(0).startswith('"')
                                  else "''", seg)):
                hit = True
            if _sh_assembled_engine(seg):
                hit = True
            for m in SH_QUOTED.finditer(seg):
                inner = _sh_quoted_inner(m.group(0))
                subscript = (seg[:m.start()].endswith("[")
                             and seg[m.end():].startswith("]"))
                if not subscript and _is_engine_literal(inner):
                    hit = True
            # A format selector as a bare word (`-fmt=pdflatex`, `--fmt`,
            # `\&pdflatex`): an argument only a TeX engine takes.
            for w in SH_WORD.findall(SH_QUOTED.sub('""', seg)):
                if FMT_SELECTOR.match(w.lstrip("\\")):
                    hit = True
        if hit:
            hits.append((n, line.strip()))
    return hits


# `jq --arg NAME VALUE` / `--argjson`: VALUE is a JSON datum jq binds, never a
# command (4 smoke scripts pass `jq --arg k latex`, the service payload key).
SH_JQ_ARG = re.compile(r"--(arg|argjson)\s+\S+\s+\S+")
# A parameter expansion with a default/alternative WORD: `${E:-pdftex}`,
# `${E=pdftex}`, `${E:+pdftex}`. The word is what the shell substitutes.
SH_PARAM_WORD = re.compile(r"\$\{[A-Za-z_][A-Za-z0-9_]*:?[-=+?]([^{}]*)\}")
_GLOB_CHARS = set("*?[")


def _brace_expand(w: str, limit: int = 64) -> list[str]:
    """Bash brace expansion of one word (`pdf{latex,}` -> pdflatex, pdf),
    innermost group first; a `${...}` is not a brace group."""
    out, todo = [], [w]
    while todo and len(out) + len(todo) <= limit:
        cur = todo.pop()
        m = None
        for mm in re.finditer(r"(?<!\$)\{([^{}]*)\}", cur):
            if "," in mm.group(1) or ".." in mm.group(1):
                m = mm
                break
        if m is None:
            out.append(cur)
            continue
        body = m.group(1)
        r = re.fullmatch(r"(-?\d+)\.\.(-?\d+)|([A-Za-z])\.\.([A-Za-z])", body)
        if r and r.group(1) is not None:
            a, b = int(r.group(1)), int(r.group(2))
            alts = [str(i) for i in range(a, b + (1 if b >= a else -1), 1 if b >= a else -1)][:limit]
        elif r:
            a, b = ord(r.group(3)), ord(r.group(4))
            alts = [chr(i) for i in range(a, b + (1 if b >= a else -1), 1 if b >= a else -1)]
        else:
            alts = body.split(",")
        todo += [cur[:m.start()] + x + cur[m.end():] for x in alts]
    return out


def _sh_printf_v(seg: str) -> str | None:
    """The value `printf -v VAR FMT ARGS...` assigns, when FMT and ARGS are
    literal words (`printf -v E '%slatex' pdf` -> pdflatex)."""
    import shlex
    try:
        w = shlex.split(seg, posix=True)
    except ValueError:
        return None
    if len(w) < 4 or w[0] != "printf" or w[1] != "-v" or "$" in seg:
        return None
    fmt, args = w[3], w[4:]
    it = iter(args)
    try:
        return re.sub(r"%[-#0 +]*\d*(?:\.\d+)?[sbdcqi]",
                      lambda m: next(it, ""), fmt).replace("%%", "%")
    except (TypeError, ValueError):
        return None


def _sh_expanded_engine(seg: str) -> bool:
    """An engine name the SHELL produces by EXPANSION of literal text: the
    word of a parameter expansion's default (`${TEXENG:-pdftex}`), a brace
    expansion (`pdf{latex,}`), a glob that matches an engine name
    (`pdfla[t]ex`, resolved against the vocabulary: a glob with at least
    three literal letters, so `*` or `*.log` are not engine names), and the
    value `printf -v` assigns (`printf -v E '%slatex' pdf`). Each MEASURED to
    scan clean by the round-4 review."""
    import fnmatch
    import shlex
    for m in SH_PARAM_WORD.finditer(seg):
        try:
            word = "".join(shlex.split(m.group(1), posix=True))
        except ValueError:
            word = m.group(1)
        if _is_engine_literal(word) or BARE_TOKEN.search(word):
            return True
    v = _sh_printf_v(seg)
    if v is not None and (_is_engine_literal(v.strip()) or BARE_TOKEN.search(v)):
        return True
    for raw in SH_WORD.findall(SH_QUOTED.sub('""', seg)):
        for w in _brace_expand(raw) if "{" in raw else [raw]:
            if w != raw and (ENGINE_LITERAL.match(w) or FMT_SELECTOR.match(w)):
                return True
            base = w.rsplit("/", 1)[-1]
            if (_GLOB_CHARS & set(base) and "=" not in base
                    and len(re.sub(r"\[[^\]]*\]|[*?]", "", base)) >= 3
                    and any(fnmatch.fnmatchcase(e, base) for e in ENGINES)):
                return True
    return False


# GNU make text functions over LITERAL arguments, evaluated before the recipe
# line is scanned: `$(subst X,,pdfXlatex)` is `pdflatex` to make (MEASURED to
# scan clean by the round-4 review). A function with a `$` in its arguments
# is not literal and is left alone (a variable is a residual).
_MAKE_FN = re.compile(r"\$[({](subst|patsubst|strip|addprefix|addsuffix|join|"
                      r"firstword|lastword|word|findstring|filter|sort|notdir|"
                      r"basename|suffix)[ \t]+([^$(){}]*)[)}]")


def _make_eval(code: str) -> str:
    def one(m):
        fn, a = m.group(1), m.group(2)
        parts = a.split(",")
        try:
            if fn == "subst" and len(parts) == 3:
                return parts[2].replace(parts[0], parts[1])
            if fn == "patsubst" and len(parts) == 3:
                pat, rep_ = parts[0].strip(), parts[1].strip()
                rx = "^" + re.escape(pat).replace("%", "(.*)", 1) + "$"
                return " ".join(re.sub(rx, rep_.replace("%", "\\1", 1), w)
                                for w in parts[2].split())
            if fn in ("strip", "sort", "filter"):
                return " ".join(parts[-1].split())
            if fn in ("addprefix", "addsuffix") and len(parts) == 2:
                ws = parts[1].split()
                return " ".join((parts[0] + w) if fn == "addprefix" else (w + parts[0])
                                for w in ws)
            if fn == "join" and len(parts) == 2:
                a1, a2 = parts[0].split(), parts[1].split()
                return " ".join(x + y for x, y in zip(a1, a2))
            if fn in ("firstword", "lastword"):
                ws = a.split()
                return (ws[0] if fn == "firstword" else ws[-1]) if ws else ""
            if fn == "word" and len(parts) == 2:
                ws = parts[1].split()
                i = int(parts[0])
                return ws[i - 1] if 0 < i <= len(ws) else ""
            if fn == "findstring" and len(parts) == 2:
                return parts[0] if parts[0] in parts[1] else ""
            if fn in ("notdir", "basename", "suffix"):
                return a
        except (ValueError, re.error):
            pass
        return m.group(0)
    for _ in range(8):  # innermost first; nested literal calls fold outward
        new = _MAKE_FN.sub(one, code)
        if new == code:
            break
        code = new
    return code


def _sh_assembled_engine(seg: str) -> bool:
    """An engine name the SHELL assembles from quoted or escaped pieces of one
    word: `"pdf"latex`, `pdf\\latex`, `'pdf'"latex"`, `cmd=("pdf"latex -x)`.
    The shell removes the quotes and backslashes and runs `pdflatex`, yet the
    raw text never holds the name, so neither the bare-token nor the
    quoted-literal rule saw it (OPEN-118 review round 3; the shell counterpart
    of Python's adjacent-literal join). A word counts only when its DEQUOTED
    form holds an engine token its RAW form does not, so a pattern such as
    `grep 'pdftex\\|pdflatex'` (the name intact inside quotes) is untouched."""
    import shlex
    for raw in SH_WORD.findall(seg):
        if not any(c in raw for c in "\"'\\"):
            continue
        # `$'...'` first: shlex knows no ANSI-C quoting (C-91).
        dec = _ANSI_C.sub(lambda m: shlex.quote(_ansi_c_decode(m.group(1))), raw)
        try:
            w = "".join(shlex.split(dec, posix=True))
        except ValueError:
            continue
        m = BARE_TOKEN.search(w)
        if (m and m.group(2) not in raw) or FMT_SELECTOR.match(w):
            return True
    return False


# One shell word, quotes and escapes kept: the unit the shell dequotes.
SH_WORD = re.compile(r"""(?:\$'(?:[^'\\]|\\.)*'|"(?:[^"\\]|\\.)*"|'[^']*'|\\.|[^\s"'\\])+""")


def _sh_commands(code: str) -> list[str]:
    """Split a shell line into its commands at `;`, `&&`, `||`, `|` that lie
    OUTSIDE quotes. The echo/printf exemption then applies per command: it
    used to exempt the whole line, so `echo x && pdflatex t.tex` passed."""
    masked = SH_QUOTED.sub(lambda m: "\0" * len(m.group(0)), code)
    out, last = [], 0
    for m in SH_SPLIT.finditer(masked):
        out.append(code[last:m.start()])
        last = m.end()
    out.append(code[last:])
    return [c for c in out if c.strip()]


def scan_other(text: str) -> list[tuple[int, str]]:
    """C, Rust, JS, Ruby, Perl, Go, Lua, Java: a quoted literal that IS an
    engine or an engine command line."""
    hits = []
    for n, line in enumerate(text.split("\n"), 1):
        for m in OTHER_LITERAL.finditer(line):
            inner = m.group(1) if m.group(1) is not None else m.group(2)
            if _is_engine_literal(inner):
                hits.append((n, line.strip()))
                break
    return hits


def scan_ocaml(text: str) -> list[tuple[int, str]]:
    if not ML_SPAWN.search(text):
        return []
    return [(n, m.group(0)) for n, line in enumerate(text.split("\n"), 1)
            for m in [ML_LITERAL.search(line)] if m]


def tracked_files(repo: Path) -> list[str]:
    import subprocess
    r = subprocess.run(["git", "-C", str(repo), "ls-files"], capture_output=True,
                       text=True)
    if r.returncode != 0:
        raise RuntimeError(f"git ls-files failed: {r.stderr.strip()}")
    return r.stdout.split("\n")


def dig(d, path):
    for k in path:
        if not isinstance(d, dict):
            return None
        d = d.get(k)
    return d


SHEBANG = re.compile(rb"^#!\s*(\S+)(?:\s+(\S+))?")
_SHEBANG_SHELLS = {"sh", "bash", "dash", "zsh", "ksh", "mksh", "busybox"}


def _shebang_scanner(p: Path):
    try:
        with open(p, "rb") as fh:
            head = fh.readline(256)
    except OSError:
        return None
    m = SHEBANG.match(head)
    if not m:
        return None
    interp = Path(m.group(1).decode(errors="replace")).name
    if interp == "env" and m.group(2):
        interp = m.group(2).decode(errors="replace")
    if interp in _SHEBANG_SHELLS:
        return scan_shell
    if re.fullmatch(r"python[0-9.]*", interp):
        return scan_python
    return None


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", default=".")
    repo = Path(ap.parse_args().repo).resolve()
    image, version = _oracle.workflow_pin()
    findings: list[str] = []

    # 1. fingerprints measured for THIS digest, both platforms, same macro layer
    if _oracle.FINGERPRINTED_IMAGE != image:
        findings.append(f"tex-oracle.yml pins {image} but _oracle.py's tree "
                        f"fingerprints were measured for "
                        f"{_oracle.FINGERPRINTED_IMAGE}; re-measure both "
                        f"platform images in the re-pin PR")
    fps = _oracle.TREE_FINGERPRINTS
    if set(fps) != {"aarch64", "x86_64"}:
        findings.append(f"_oracle.TREE_FINGERPRINTS covers {sorted(fps)}, "
                        f"expected both aarch64 (local) and x86_64 (CI)")
    elif fps["aarch64"]["macro_layer_sha256"] != fps["x86_64"]["macro_layer_sha256"]:
        findings.append("the arm64 and amd64 images of the pinned digest have "
                        "DIFFERENT macro layers: a local grade would not be the "
                        "CI grade")
    for arch, fp in fps.items():
        for k in FINGERPRINT_KEYS:
            if not re.fullmatch(r"[0-9a-f]{64}", str(fp.get(k, ""))):
                findings.append(f"_oracle.TREE_FINGERPRINTS[{arch}][{k}] is not a sha256")

    # 2./3. every graded artefact names the pinned image
    graded_paths = {p for p, _ in GRADED}
    if len(PRE_BASELINE) != PRE_BASELINE_SIZE:
        findings.append(f"PRE_BASELINE holds {len(PRE_BASELINE)} entries, pinned at "
                        f"{PRE_BASELINE_SIZE}; widening it needs a ledger row and a "
                        f"deliberate edit here")
    for rel in sorted(graded_paths & set(PRE_BASELINE)):
        findings.append(f"{rel} is in both GRADED and PRE_BASELINE")
    for rel, path in GRADED:
        f = repo / rel
        if not f.is_file():
            findings.append(f"{rel}: missing")
            continue
        try:
            block = dig(json.loads(f.read_text()), path)
        except (OSError, json.JSONDecodeError) as e:
            findings.append(f"{rel}: unreadable ({e})")
            continue
        if not isinstance(block, dict):
            findings.append(f"{rel}: no oracle block at {'.'.join(path)}")
            continue
        if block.get("image") != image:
            findings.append(
                f"{rel}: graded by {block.get('image') or 'a host TeX Live (no image recorded)'}"
                f", not the pinned image {image}. Re-grade it through "
                f"scripts/tools/_oracle.py (ADR-012 decision 7).")
        if version not in str(block.get("version", "")):
            findings.append(f"{rel}: oracle version {block.get('version')!r} is not "
                            f"the pin {version!r}")
        if block.get("backend") not in BACKENDS:
            findings.append(f"{rel}: oracle backend {block.get('backend')!r} is not "
                            f"one of {sorted(BACKENDS)}")
        want = fps.get(block.get("arch"))
        if want is None:
            findings.append(f"{rel}: oracle arch {block.get('arch')!r} has no "
                            f"recorded tree fingerprint")
        else:
            for k in FINGERPRINT_KEYS:
                if block.get(k) != want.get(k):
                    findings.append(
                        f"{rel}: oracle {k} {block.get(k)!r} is not the pinned "
                        f"image's {block.get('arch')} tree fingerprint "
                        f"{want.get(k)!r}")
    for rel in sorted(PRE_BASELINE):
        f = repo / rel
        if not f.is_file():
            findings.append(f"{rel}: listed in PRE_BASELINE but missing")
            continue
        if f'"image": "{image}"' in f.read_text():
            findings.append(f"{rel} now records the pinned image but is still in "
                            f"PRE_BASELINE; move it to GRADED")

    # 4. nothing else starts a TeX engine
    scanned = 0
    for rel in sorted(tracked_files(repo)):
        if not rel or rel in ORACLE_FILES or rel in SCANNER_FILES:
            continue
        p = repo / rel
        name = p.name
        if rel.endswith(".py"):
            scan = scan_python
        elif rel.endswith(".mk") or name in ("Makefile", "GNUmakefile", "makefile"):
            scan = (lambda t: scan_shell(t, make=True))
        elif rel.endswith((".sh", ".bash", ".zsh", ".ksh", ".command")):
            scan = scan_shell
        elif rel.endswith(OTHER_CODE_EXT):
            scan = scan_other
        elif rel.endswith(".ml"):
            scan = scan_ocaml
        elif rel.startswith(".github/workflows/") and rel.endswith((".yml", ".yaml")):
            allow = WORKFLOW_ALLOW.get(rel, ())
            scan = (lambda t, a=allow: scan_shell(t, a, yaml=True))
        else:
            # A script without a known extension is scanned by its SHEBANG
            # (round 4 MEASURED an extensionless `#!/bin/sh` file scanning
            # clean): shells as shell, python as Python.
            scan = _shebang_scanner(p)
            if scan is None:
                continue
        if not p.is_file():
            continue
        scanned += 1
        for n, what in scan(p.read_text(errors="replace")):
            findings.append(f"{rel}:{n}: starts a TeX engine directly ({what[:60]!r}); "
                            f"go through scripts/tools/_oracle.py (the host TeX "
                            f"Live is not the oracle)")
    for rel, lines in WORKFLOW_ALLOW.items():
        f = repo / rel
        text = f.read_text() if f.is_file() else ""
        stripped = {ln.strip() for ln in text.split("\n")}
        for ln in lines:
            if ln not in stripped:
                findings.append(f"{rel}: allow-listed in-image line no longer "
                                f"present, prune WORKFLOW_ALLOW: {ln[:60]!r}")

    if findings:
        print("[oracle-pin] FAIL:", file=sys.stderr)
        for f in findings:
            print(f"  - {f}", file=sys.stderr)
        return 1
    print(f"[oracle-pin] OK: {len(GRADED)} graded artefacts name {image} with "
          f"its tree fingerprints; {len(PRE_BASELINE)} pre-baseline artefacts "
          f"pinned; {scanned} tracked code files start no TeX engine directly")
    return 0


if __name__ == "__main__":
    sys.exit(main())
