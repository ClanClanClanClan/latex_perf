#!/usr/bin/env python3
"""Generate a configuration contract under the pinned TeX Live image (ADR-012, M1 slice 1).

A configuration is a document class with its options, followed by an ordered list
of package loads (each with options) and, optionally, preamble definer lines
interleaved with them. The contract records what that exact configuration does
under the oracle, which ADR-012 decision 7 freezes as CI's digest-pinned image
(`TEX_IMAGE` in .github/workflows/tex-oracle.yml, read from there, never
restated here). Every TeX job runs inside that image through docker; the laptop
TeX Live is never used.

Nothing in a contract is hand-listed. Every field comes from a TeX run:

  pin             engine banner, pdflatex.fmt sha256, texlive.tlpdb sha256,
                  image reference and architecture, LaTeX and L3 banners.
  kernel          INITEX re-run of pdflatex.ini under \\tracingassigns and
                  \\tracingrestores; every name it assigns, plus every name
                  referenced from a kernel meaning, is then dumped in format
                  state, and the defined ones are the kernel. Cached by fmt hash.
  load_outcome    the configuration plus \\begin{document}\\end{document} under
                  -interaction=nonstopmode -halt-on-error: ok, or the first
                  `!` error and the load segment it happened in.
  files_read      the .fls (-recorder) of that run, minus the files an empty
                  format-state job reads, minus job-local files; with sha256.
  defined_names   pass 1 traces every assignment from before \\documentclass
                  until after the begin-document hooks, with a marker between
                  loads. Pass 2 dumps \\meaning of every kernel name and every
                  traced name at body start (after AtBeginDocument), guarded
                  by \\ifcsname so the dump defines nothing. A name is in
                  defined_names iff its body-start meaning differs from its
                  format-state meaning (class Undefined = the configuration
                  removed a kernel name). Traced names whose meaning is back
                  to the kernel's by body start are listed in reverted_names.
  catcodes        \\the\\catcode of bytes 0-255 at body start, where it
                  differs from format state.
  active_chars    \\meaning of each active character at body start, where it
                  differs from format state.
  unicode         a \\ifcsname sweep of u8:<bytes> over U+0080..U+FFFF (minus
                  surrogates) at body start, cross-checked against the u8:
                  names in the closed world.
  counters        every c@X register at body start, with \\theX presence and
                  the counters its cl@X list resets.
  key_families    keyval families and keys from \\KV@<family>@<key> names,
                  and declared class/package options from \\ds@<option>.
  self_check      an independent run: \\ifcsname on a seeded 1% sample of the
                  closed world, on every name referenced from a body-start
                  meaning, and on any --use-names, must agree with membership.
                  Any mismatch sets complete=false.

Signature probes (the typed lattice) are M1 slice 2. This slice ships only the
probe HARNESS (`probes` subcommand): solo -halt-on-error probe documents with a
timeout, classified by error class (never by rc), and a batched run whose
polarity is compared with the solo one.

Determinism: every job runs in a fresh directory mounted at a fixed container
path, with SOURCE_DATE_EPOCH=0 and FORCE_SOURCE_DATE=1; output JSON is sorted;
no timing is written into a contract. `check_contracts_reproducible.py`
regenerates a committed contract and diffs it byte for byte.

Usage:
  gen_contract.py generate --class article --package amsmath --package hyperref \\
      --name article-amsmath-hyperref [--out corpora/contracts/NAME.json]
  gen_contract.py generate --config CONFIG.json --name NAME
  gen_contract.py probes --contract corpora/contracts/NAME.json --sample 30 \\
      [--names mathbb,frac] --out corpora/contracts/probe_demo_NAME.json

Needs docker with the pinned image pulled. The work directory must be visible
inside the container (colima mounts only $HOME by default), so it defaults to
~/.cache/lp-oracle/contracts/work.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import random
import re
import shutil
import subprocess
import sys
import time
import uuid
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.dont_write_bytecode = True

SCHEMA = "lp-configuration-contract/1"
KERNEL_SCHEMA = "lp-kernel-names/1"
PROBE_SCHEMA = "lp-probe-report/1"
# A semantic version, bumped by hand when the generator's OUTPUT changes on
# purpose. Deliberately not a hash of this file: a comment edit must not
# invalidate every committed contract (the C-68 lesson).
GENERATOR_VERSION = "1"

REPO = Path(__file__).resolve().parent.parent.parent
WORKFLOW = Path(".github/workflows/tex-oracle.yml")
CONTRACT_DIR = Path("corpora/contracts")
CONTAINER_WORK = "/lpwork"
TEX_ENV = {
    "HOME": "/tmp",
    # No log line wrapping, so a trace record or a dumped meaning is one line.
    "max_print_line": "1000000",
    "error_line": "254",
    "half_error_line": "238",
    # Deterministic \\today, \\time and log banner.
    "SOURCE_DATE_EPOCH": "0",
    "FORCE_SOURCE_DATE": "1",
}
LONG_TIMEOUT = 600
PROBE_TIMEOUT = 15
TIMEOUT_RC = 124

# Control bytes the dump regime reserves (escape, begin group, end group,
# spacer, active); a name containing one of them, or a line break, cannot be
# written into the dump file and is reported as unwritable.
ESC, BGROUP, EGROUP, SPACER, ACTIVE = b"\x01", b"\x02", b"\x03", b"\x04", b"\x05"
UNWRITABLE = set(b"\x01\x02\x03\x04\x05\n\r")
# End sentinel of a dumped meaning (a meaning can contain raw line feeds).
# Lower case, so that \lowercase in the active-character dump leaves it alone.
END = b"|lpe"
# Primitives the dump itself relies on; their meanings are checked in every dump.
DUMP_PRIMITIVES = [b"ifcsname", b"endcsname", b"csname", b"immediate", b"write",
                   b"expandafter", b"meaning", b"else", b"fi", b"begingroup",
                   b"endgroup", b"lccode", b"lowercase", b"catcode", b"the"]


# ---------------------------------------------------------------------------
# Byte and name encodings
# ---------------------------------------------------------------------------

_CARET = re.compile(rb"\^\^(?:([0-9a-f]{2})|([\x3f\x40-\x7f]))")


def decode_carets(b: bytes) -> bytes:
    """Undo TeX's ^^ printing: ^^xx (hex) and ^^X (X = c+64, ^^? = 127)."""
    def rep(m: re.Match) -> bytes:
        if m.group(1) is not None:
            return bytes([int(m.group(1), 16)])
        x = m.group(2)[0]
        return bytes([127 if x == 0x3F else x - 64])
    return _CARET.sub(rep, b)


def name_str(b: bytes) -> str:
    """Canonical text form of a control-sequence name (or any TeX string).

    Valid UTF-8 is kept as text; control bytes, DEL and bytes that are not
    valid UTF-8 are written ^^xx (lower-case hex). `name_bytes` inverts it,
    except for a name that itself contains a literal ^^xx (TeX's own log has
    the same ambiguity)."""
    out = []
    for ch in b.decode("utf-8", errors="surrogateescape"):
        o = ord(ch)
        if 0xDC80 <= o <= 0xDCFF:
            out.append("^^%02x" % (o - 0xDC00))
        elif o < 0x20 or o == 0x7F:
            out.append("^^%02x" % o)
        else:
            out.append(ch)
    return "".join(out)


def name_bytes(s: str) -> bytes:
    return re.sub(rb"\^\^([0-9a-f]{2})", lambda m: bytes([int(m.group(1), 16)]),
                  s.encode("utf-8"))


def sha256_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


# Top-level maps written one entry per line (they hold thousands of entries).
LINE_PER_ENTRY = ("defined_names", "names", "active_chars", "counters", "files_read",
                  "probes")


def canonical_json(obj) -> str:
    """Sorted keys, UTF-8, one line per entry for the large top-level maps, so
    a regeneration diff is one line per changed name."""
    if not isinstance(obj, dict):
        return json.dumps(obj, indent=1, sort_keys=True, ensure_ascii=False) + "\n"

    def one(v):
        return json.dumps(v, sort_keys=True, ensure_ascii=False, separators=(",", ":"))
    out = ["{"]
    keys = sorted(obj)
    for i, k in enumerate(keys):
        v = obj[k]
        comma = "," if i < len(keys) - 1 else ""
        if k in LINE_PER_ENTRY and isinstance(v, dict) and v:
            out.append(" %s: {" % one(k))
            sub = sorted(v)
            for j, sk in enumerate(sub):
                out.append("  %s: %s%s" % (one(sk), one(v[sk]), "," if j < len(sub) - 1 else ""))
            out.append(" }" + comma)
        elif k in LINE_PER_ENTRY and isinstance(v, list) and v:
            out.append(" %s: [" % one(k))
            for j, item in enumerate(v):
                out.append("  %s%s" % (one(item), "," if j < len(v) - 1 else ""))
            out.append(" ]" + comma)
        else:
            body = json.dumps(v, indent=1, sort_keys=True, ensure_ascii=False)
            out.append(" %s: %s%s" % (one(k), body.replace("\n", "\n "), comma))
    out.append("}")
    text = "\n".join(out) + "\n"
    if json.loads(text) != obj:
        raise AssertionError("canonical_json does not round-trip")
    return text


# ---------------------------------------------------------------------------
# Log parsers (unit-tested on recorded fixtures by selftest_gen_contract.py)
# ---------------------------------------------------------------------------

_REC_START = re.compile(
    rb"\{(globally )?(changing|into|reassigning|restoring|retaining) ")
# Quantities (not control-sequence meanings) that \tracingassigns also reports.
_QUANTITY = re.compile(
    rb"(?:count|dimen|skip|muskip|toks|box|catcode|lccode|uccode|sfcode|mathcode|"
    rb"delcode|textfont|scriptfont|scriptscriptfont)\d+")
SEG_MARK = re.compile(rb"^LPSEG:(-?\d+)$")


def parse_trace(log: bytes):
    """Parse a \\tracingassigns/\\tracingrestores log.

    Returns a dict:
      names      {(kind, name_bytes): last_segment}, kind is "cs" or "active";
                 the segment is the index of the last LPSEG marker before the
                 record that last set the name ("changing" records carry the
                 old value and are not counted as setting it).
      records    number of trace records seen
      tracing_toggles  records that assign \\tracingassigns or
                 \\tracingrestores (the caller decides which are its own)
      first_error      (segment, message) of the first `! ` line, or None
      unparsed   number of records with no `=` (name not recoverable)
      multiline  records whose value ran over several log lines (the name is
                 on the first line, so it is still read)

    The escape character is tracked from the trace itself: a record for
    \\escapechar updates it, so names printed while \\escapechar=-1 are still
    read correctly. Under a negative escapechar a one-character name is
    ambiguous between a control symbol and an active character; both
    candidates are reported (the meaning dump settles which exists).
    """
    esc = 92
    seg = -1
    names: dict = {}
    records = 0
    unparsed = 0
    toggles = []
    first_error = None
    multiline = 0
    lines = log.split(b"\n")
    n = 0
    while n < len(lines):
        line = lines[n].rstrip(b"\r")
        n += 1
        m = SEG_MARK.match(line)
        if m:
            seg = int(m.group(1))
            continue
        if first_error is None and line.startswith(b"! ") and _has_context(lines, n):
            first_error = (seg, line[2:].decode("utf-8", "replace").strip())
            continue
        m = _REC_START.search(line)
        if not m:
            continue
        if not line.endswith(b"}"):
            # cp227.tcx prints a line feed literally, so a name or a meaning
            # holding one continues the record over several log lines. Re-join
            # them with the line feed they were; nothing on them is a record
            # or an error.
            multiline += 1
            parts = [line]
            while n < len(lines) and len(parts) < 400:
                parts.append(lines[n].rstrip(b"\r"))
                n += 1
                if parts[-1].endswith(b"}"):
                    break
            line = b"\n".join(parts)
        records += 1
        verb = m.group(2)
        body = line[m.end():-1] if line.endswith(b"}") else line[m.end():]
        # A control symbol named `=` prints as `\==value`: skip its own `=`.
        start = 2 if body[1:2] == b"=" and 0 <= esc <= 255 and body[:1] == bytes([esc]) else 0
        eq = body.find(b"=", start)
        if eq < 0:
            unparsed += 1
            continue
        printed, value = body[:eq], body[eq + 1:]
        dec = decode_carets(printed)
        # escapechar bookkeeping: the "into" record is printed with the NEW
        # escape character, so match the bare name with any one-byte prefix.
        def is_param(x):
            return dec.endswith(x) and len(dec) in (len(x), len(x) + 1)
        if is_param(b"escapechar"):
            if verb != b"changing":
                try:
                    esc = int(value)
                except ValueError:
                    pass
            continue
        for bare in (b"tracingassigns", b"tracingrestores"):
            if is_param(bare):
                toggles.append((seg, verb.decode(), bare.decode(),
                                value.decode("utf-8", "replace")))
        if dec == b"current font":
            continue
        cands = []
        if 0 <= esc <= 255:
            e = bytes([esc])
            if dec.startswith(e) and len(dec) > 1:
                cands.append(("cs", dec[1:]))
            elif len(dec) == 1:
                cands.append(("active", dec))
            else:
                # printed with a different escape than we track: keep the
                # whole string as a candidate name (the dump settles it).
                cands.append(("cs", dec))
        else:
            cands.append(("cs", dec))
            if len(dec) == 1:
                cands.append(("active", dec))
        for kind, nm in cands:
            if kind == "cs" and _QUANTITY.fullmatch(nm):
                continue
            key = (kind, nm)
            if verb == b"changing":
                names.setdefault(key, seg)
            else:
                names[key] = seg
    return {"names": names, "records": records, "tracing_toggles": toggles,
            "first_error": first_error, "unparsed": unparsed,
            "multiline": multiline}


def parse_dump(log: bytes):
    """Parse the output of a dump block (see `dump_block`).

    Returns dict with:
      meanings  {index: meaning_bytes or None (undefined per \\ifcsname)}
      actives   {byte: meaning_bytes}
      catcodes  [256 ints] or None
      u8        set of code points whose u8: name is defined
      tests     {index: bool}
      prims     {primitive_name: meaning}
      error     the first `! ` error line outside a dumped meaning, or None
    """
    meanings: dict = {}
    actives: dict = {}
    catcodes = None
    u8 = set()
    tests: dict = {}
    prims: dict = {}
    error = None
    lines = log.split(b"\n")
    n = 0
    while n < len(lines):
        line = lines[n]
        n += 1
        if line[:4] in (b"LPM:", b"lpa:"):
            # A meaning may hold a raw line feed (cp227.tcx prints ^^J
            # literally), so a record runs until the line ending with the
            # sentinel; the pieces are re-joined with the line feed they were.
            parts = [line]
            while not parts[-1].endswith(END) and n < len(lines):
                parts.append(lines[n])
                n += 1
            rec = b"\n".join(parts)
            if not rec.endswith(END):
                break
            i, _, rest = rec[4:-len(END)].partition(b":")
            (meanings if line[:4] == b"LPM:" else actives)[int(i)] = decode_carets(rest)
            continue
        line = line.rstrip(b"\r")
        if error is None and line.startswith(b"! ") and _has_context(lines, n):
            error = line[2:].decode("utf-8", "replace").strip()
        if line[:4] == b"LPU:":
            meanings[int(line[4:])] = None
        elif line[:4] == b"LPC:":
            catcodes = [int(x) for x in line[4:].split(b",") if x.strip()]
        elif line[:4] == b"LPX:":
            u8.add(int(line[4:], 16))
        elif line[:4] == b"LPS:":
            i, _, v = line[4:].partition(b":")
            tests[int(i)] = v == b"1"
        elif line[:4] == b"LPP:":
            pn, _, rest = line[4:].partition(b":")
            prims[pn.decode()] = rest.decode("utf-8", "replace")
    return {"meanings": meanings, "actives": actives, "catcodes": catcodes,
            "u8": u8, "tests": tests, "prims": prims, "error": error}


def parse_fls(fls: bytes):
    """Return (pwd, sorted unique INPUT paths) from a -recorder .fls file."""
    pwd = None
    inputs = set()
    for raw in fls.split(b"\n"):
        line = raw.rstrip(b"\r").decode("utf-8", "surrogateescape")
        if line.startswith("PWD "):
            pwd = line[4:]
        elif line.startswith("INPUT "):
            inputs.add(line[6:])
    return pwd, sorted(inputs)


def _has_context(lines: list, n: int) -> bool:
    """TeX follows a real error message with its location context (`l.<n>` or
    a `<...>` token-list line) within a few lines; text that merely starts
    with `! ` inside a printed meaning usually has none."""
    for ln in lines[n:n + 12]:
        if re.match(rb"^(l\.\d+ |<[a-z*]|<\S+> )", ln):
            return True
    return False


def first_error(log: bytes):
    lines = log.split(b"\n")
    for n, raw in enumerate(lines):
        if raw.startswith(b"! ") and _has_context(lines, n + 1):
            return raw[2:].rstrip(b"\r").decode("utf-8", "replace").strip()
    return None


# Error classes: the first `! ` line of the log, normalised. The class is what
# a probe outcome is compared on; the return code is never used for it.
_ERROR_CLASSES = [
    (r"^Undefined control sequence\.", "undefined_cs"),
    (r"^LaTeX Error: Environment .* undefined\.", "undefined_env"),
    (r"^LaTeX Error: File `.*' not found\.", "missing_file"),
    (r"^LaTeX Error: .*Unicode character", "unicode_undefined"),
    (r"^LaTeX Error: Missing \\begin\{document\}\.", "missing_begin_document"),
    (r"^LaTeX Error: There's no line here to end\.", "no_line_to_end"),
    (r"^LaTeX Error: Lonely \\item", "lonely_item"),
    (r"^LaTeX Error: Command .* already defined\.", "already_defined"),
    (r"^LaTeX Error: Can be used only in preamble\.", "preamble_only"),
    (r"^LaTeX Error: Option clash", "option_clash"),
    (r"^LaTeX Error: \\begin\{.*\} on input line \d+ ended by \\end\{.*\}\.",
     "env_mismatch"),
    (r"^LaTeX Error: Command .* unavailable in encoding", "unavailable_in_encoding"),
    (r"^LaTeX Error: .* allowed only in math mode\.", "math_only"),
    (r"^LaTeX Error: Command .* invalid in math mode\.", "text_only"),
    (r"^LaTeX Error: (.*)", "latex_error"),
    (r"^Package (\S+) Error: ", "package_error"),
    (r"^Class (\S+) Error: ", "class_error"),
    (r"^Missing \$ inserted\.", "missing_dollar"),
    (r"^Display math should end with \$\$\.", "display_math_end"),
    (r"^Paragraph ended before .* was complete\.", "par_in_argument"),
    (r"^Argument of .* has an extra \}\.", "extra_brace_in_argument"),
    (r"^Use of .* doesn't match its definition\.", "delimiter_mismatch"),
    (r"^Missing number, treated as zero\.", "missing_number"),
    (r"^Illegal unit of measure", "bad_unit"),
    (r"^Double (superscript|subscript)\.", "double_script"),
    (r"^Extra \}, or forgotten", "extra_close"),
    (r"^Too many \}'s\.", "extra_close"),
    (r"^Missing \} inserted\.", "missing_close"),
    (r"^Missing \{ inserted\.", "missing_open"),
    (r"^Missing \\endcsname inserted\.", "missing_endcsname"),
    (r"^Missing \\endgroup inserted\.", "missing_endgroup"),
    (r"^Missing control sequence inserted\.", "missing_control_sequence"),
    (r"^Misplaced alignment tab character &\.", "misplaced_tab"),
    (r"^Extra alignment tab has been changed", "extra_tab"),
    (r"^Misplaced \\(noalign|omit|cr|crcr)", "misplaced_alignment"),
    (r"^You can't use .* in (vertical|horizontal|math|restricted horizontal|"
     r"internal vertical|display math) mode\.", "wrong_mode"),
    (r"^Illegal parameter number", "illegal_parameter"),
    (r"^File ended while scanning", "runaway_eof"),
    (r"^Emergency stop\.", "emergency_stop"),
    (r"^TeX capacity exceeded", "capacity"),
    (r"^Extra \\(else|fi|or)\.", "extra_conditional"),
    (r"^Extra \\endcsname\.", "extra_endcsname"),
    (r"^Undefined font", "undefined_font"),
]
_ERROR_CLASSES_RE = [(re.compile(p), c) for p, c in _ERROR_CLASSES]


def classify_error(msg: str) -> str:
    for rx, cls in _ERROR_CLASSES_RE:
        if rx.search(msg):
            if cls in ("package_error", "class_error"):
                return "%s:%s" % (cls, rx.search(msg).group(1))
            return cls
    return "other"


def classify_outcome(rc: int, log: bytes | None, pdf: bool) -> dict:
    """Probe/oracle outcome by ERROR CLASS (B.4): ok requires rc 0 AND a PDF."""
    if rc == TIMEOUT_RC:
        return {"outcome": "timeout", "error_class": "timeout"}
    msg = first_error(log or b"")
    if msg is not None:
        return {"outcome": "fatal", "error_class": classify_error(msg),
                "message": msg}
    if rc == 0 and pdf:
        return {"outcome": "ok"}
    if rc == 0:
        return {"outcome": "fatal", "error_class": "no_pdf"}
    return {"outcome": "fatal", "error_class": "no_error_line"}


# ---------------------------------------------------------------------------
# Meaning classification
# ---------------------------------------------------------------------------

_MACRO = re.compile(rb"^((?:\\protected|\\long|\\outer)*) ?macro:(.*?)->(.*)$", re.S)
_REG = re.compile(rb"^\\(count|dimen|skip|muskip|toks)(\d+)$")
_CHARDEF = re.compile(rb'^\\char"([0-9A-F]+)$')
_MATHCHARDEF = re.compile(rb'^\\mathchar"([0-9A-F]+)$')
_FONT = re.compile(rb"^select font (.+)$", re.S)
_IMPLICIT = re.compile(
    rb"^(the letter|the character|begin-group character|end-group character|"
    rb"math shift character|alignment tab character|macro parameter character|"
    rb"superscript character|subscript character|blank space) ?(.*)$", re.S)
_PRIM = re.compile(rb"^\\([^ ]+| )$", re.S)
_PARAM = re.compile(rb"#([1-9])")
_LTCMD = re.compile(rb"^\\__cmd_start[^ ]* \{([^{}]*)\}")
_REF = re.compile(rb"\\([^ \\{}]+) ")


def classify_meaning(name: bytes, m: bytes | None) -> dict:
    """Structured meaning. `kind` is one of Undefined, Relax, Primitive, Char,
    MathChar, Register, Font, Macro, Other."""
    if m is None or m == b"undefined":
        return {"kind": "Undefined"}
    if m == b"\\relax":
        return {"kind": "Relax"}
    mm = _MACRO.match(m)
    if mm:
        prefix, params, body = mm.groups()
        d = {"kind": "Macro",
             "long": b"\\long" in prefix,
             "protected": b"\\protected" in prefix,
             "outer": b"\\outer" in prefix,
             "params": name_str(params),
             "arity_hint": len(set(_PARAM.findall(params)))}
        d["delimited"] = bool(_PARAM.sub(b"", params))
        inner = None
        rb_ = re.match(rb"^(?:\\x@protect \\(.+?) )?\\protect \\(.+ ) $", body, re.S)
        if rb_ and rb_.group(2) == name + b" ":
            inner = rb_.group(2)
        d["robust"] = inner is not None
        if inner is not None:
            d["robust_inner"] = name_str(inner)
        lt = _LTCMD.match(body)
        if lt:
            d["ltcmd_spec"] = name_str(lt.group(1))
        return d
    r = _REG.match(m)
    if r:
        return {"kind": "Register", "register": r.group(1).decode(),
                "index": int(r.group(2))}
    r = _CHARDEF.match(m)
    if r:
        return {"kind": "Char", "form": "chardef", "code": int(r.group(1), 16)}
    r = _MATHCHARDEF.match(m)
    if r:
        return {"kind": "MathChar", "code": int(r.group(1), 16)}
    r = _FONT.match(m)
    if r:
        return {"kind": "Font", "font": name_str(r.group(1))}
    r = _IMPLICIT.match(m)
    if r:
        return {"kind": "Char", "form": "implicit",
                "catcode_class": r.group(1).decode(), "char": name_str(r.group(2))}
    r = _PRIM.match(m)
    if r:
        return {"kind": "Primitive", "primitive": name_str(r.group(1))}
    return {"kind": "Other", "meaning": name_str(m)}


def short_kind(d: dict) -> str:
    k = d["kind"]
    if k == "Macro":
        flags = [f for f in ("long", "protected", "outer", "robust") if d.get(f)]
        if "ltcmd_spec" in d:
            flags.append("ltcmd")
        return "+".join(["Macro"] + flags)
    if k == "Register":
        return "Register:" + d["register"]
    if k == "Primitive":
        return "Primitive"
    return k


def referenced_names(meaning: bytes) -> set:
    """Multi-letter control-sequence names printed inside a meaning (TeX prints
    them as `\\name ` with a trailing space). Over-approximate on purpose: a
    wrong split is just another name whose membership the self-check tests."""
    out = {decode_carets(x) for x in _REF.findall(meaning)}
    # A primitive (or a \let copy of one) prints as the bare `\name`, with no
    # trailing space; this is how primitives reachable only through an alias
    # such as \tex_badness:D enter the kernel set.
    m = _PRIM.match(meaning)
    if m:
        out.add(decode_carets(m.group(1)))
    return out


# ---------------------------------------------------------------------------
# Dump documents
# ---------------------------------------------------------------------------

def _w(*parts: bytes) -> bytes:
    return b"".join(parts)


def regime_open() -> bytes:
    """Enter a catcode regime where every byte is a letter (A-Z, a-z) or other,
    except ^^A escape, ^^B/^^C braces, ^^D spacer and ^^E active; no end-of-line
    character. Any byte string without those five bytes and line breaks can
    then be written literally inside \\csname...\\endcsname."""
    out = [b"\\begingroup\\catcode1=0 \\catcode2=1 \\catcode3=2 \\catcode4=10 "
           b"\\catcode5=13 \\endlinechar=-1 \\relax%\n"]
    parts = []
    for b in range(256):
        if b in (1, 2, 3, 4, 5):
            continue
        cc = 11 if (65 <= b <= 90 or 97 <= b <= 122) else 12
        parts.append(ESC + b"catcode%d=%d" % (b, cc) + SPACER)
    parts.append(ESC + b"escapechar=92" + SPACER + ESC + b"newlinechar=-1" + SPACER)
    out.append(b"".join(parts) + b"\n")
    for p in DUMP_PRIMITIVES:
        out.append(_w(ESC, b"immediate", ESC, b"write-1", BGROUP, b"LPP:", p, b":",
                      ESC, b"meaning", ESC, p, EGROUP, b"\n"))
    return b"".join(out)


def regime_close() -> bytes:
    return ESC + b"endgroup\n"


def catcode_line() -> bytes:
    """Written in the ambient regime, before `regime_open`."""
    cells = b"".join(b"\\the\\catcode%d ," % b for b in range(256))
    return b"\\immediate\\write-1{LPC:" + cells + b"}%\n"


def _name_line(nm: bytes, make) -> bytes | None:
    """make(name_bytes) builds one dump line. A name holding a reserved byte
    (the regime's five control bytes, CR or LF) is written through \\lowercase:
    each reserved byte is replaced by an unused placeholder byte whose \\lccode
    is the reserved byte, every other \\lccode being the identity inside the
    group, so the name reaches \\csname byte for byte. None if impossible."""
    bad = sorted({c for c in nm if c in UNWRITABLE})
    if not bad:
        return make(nm)
    free = [c for c in range(0x0E, 0x20) if c not in nm]
    if len(free) < len(bad):
        return None
    ph = dict(zip(bad, free))
    alias = bytes(ph.get(c, c) for c in nm)
    lcs = [ESC + b"lccode%d=%d" % (c, c) + SPACER for c in range(1, 256)
           if c not in ph.values()]
    lcs += [ESC + b"lccode%d=%d" % (p, c) + SPACER for c, p in ph.items()]
    return _w(ESC, b"begingroup", b"".join(lcs), ESC, b"lowercase", BGROUP,
              ESC, b"endgroup", make(alias).rstrip(b"\n"), EGROUP, b"\n")


def dump_block(cs_names: list, *, actives: bool, u8_sweep: bool,
               tests: list | None = None) -> tuple:
    """Bytes to insert at the dump point, and the list of unwritable names.

    cs_names[i] is dumped as LPM:i:<meaning> or LPU:i; tests[i] as LPS:i:0|1."""
    out = [catcode_line(), regime_open()]
    unwritable = []
    for i, nm in enumerate(cs_names):
        idx = str(i).encode()
        line = _name_line(nm, lambda n, idx=idx: _w(
            ESC, b"ifcsname", SPACER, n, ESC, b"endcsname",
            ESC, b"immediate", ESC, b"write-1", BGROUP, b"LPM:", idx, b":",
            ESC, b"expandafter", ESC, b"meaning", ESC, b"csname", SPACER, n,
            ESC, b"endcsname", END, EGROUP, ESC, b"else",
            ESC, b"immediate", ESC, b"write-1", BGROUP, b"LPU:", idx, EGROUP,
            ESC, b"fi\n"))
        if line is None:
            unwritable.append(nm)
        else:
            out.append(line)
    if actives:
        out.append(_w(ESC, b"begingroup", ESC, b"catcode0=13", SPACER, ESC,
                      b"immediate", ESC, b"write-1", BGROUP, b"lpa:0:", ESC, b"meaning",
                      b"\x00", END, EGROUP, ESC, b"endgroup\n"))
        for b in range(1, 256):
            out.append(_w(ESC, b"begingroup", ESC, b"lccode5=%d" % b, SPACER,
                          ESC, b"lowercase", BGROUP, ESC, b"endgroup", ESC, b"immediate",
                          ESC, b"write-1", BGROUP, b"lpa:%d:" % b, ESC, b"meaning",
                          ACTIVE, END, EGROUP, EGROUP, b"\n"))
    if u8_sweep:
        for cp in range(0x80, 0x10000):
            if 0xD800 <= cp <= 0xDFFF:
                continue
            out.append(_w(ESC, b"ifcsname", SPACER, b"u8:", chr(cp).encode("utf-8"),
                          ESC, b"endcsname", ESC, b"immediate", ESC, b"write-1",
                          BGROUP, b"LPX:%x" % cp, EGROUP, ESC, b"fi\n"))
    for i, nm in enumerate(tests or []):
        idx = str(i).encode()
        line = _name_line(nm, lambda n, idx=idx: _w(
            ESC, b"ifcsname", SPACER, n, ESC, b"endcsname",
            ESC, b"immediate", ESC, b"write-1", BGROUP, b"LPS:", idx, b":1",
            EGROUP, ESC, b"else", ESC, b"immediate", ESC, b"write-1", BGROUP,
            b"LPS:", idx, b":0", EGROUP, ESC, b"fi\n"))
        if line is None:
            unwritable.append(nm)
        else:
            out.append(line)
    out.append(regime_close())
    return b"".join(out), unwritable


# ---------------------------------------------------------------------------
# Configurations
# ---------------------------------------------------------------------------

def normalize_config(cfg: dict) -> dict:
    items = []
    for it in cfg.get("preamble", []):
        if "package" in it:
            items.append({"package": str(it["package"]),
                          "options": [str(o) for o in it.get("options", [])]})
        elif "definer" in it:
            items.append({"definer": str(it["definer"])})
        else:
            raise SystemExit("gen_contract: preamble item must be package or definer: %r" % it)
    return {"class": str(cfg["class"]),
            "class_options": [str(o) for o in cfg.get("class_options", [])],
            "preamble": items}


def _opts(opts: list) -> str:
    return "[%s]" % ",".join(opts) if opts else ""


def segment_labels(cfg: dict) -> list:
    labels = ["class:" + cfg["class"]]
    for i, it in enumerate(cfg["preamble"]):
        labels.append(("package:" + it["package"]) if "package" in it
                      else "definer:%d" % i)
    labels.append("begin_document")
    return labels


def preamble_tex(cfg: dict, *, markers: bool = False) -> bytes:
    """The configuration as TeX source, one item per line. With markers, an
    \\immediate\\write-1{LPSEG:k} precedes segment k (class = 0, item i = i+1,
    \\begin{document} = n+1); \\immediate\\write assigns nothing."""
    lines = []

    def mark(k):
        if markers:
            lines.append("\\immediate\\write-1{LPSEG:%d}" % k)
    mark(0)
    lines.append("\\documentclass%s{%s}" % (_opts(cfg["class_options"]), cfg["class"]))
    for i, it in enumerate(cfg["preamble"]):
        mark(i + 1)
        if "package" in it:
            lines.append("\\usepackage%s{%s}" % (_opts(it["options"]), it["package"]))
        else:
            lines.append(it["definer"])
    mark(len(cfg["preamble"]) + 1)
    return ("\n".join(lines) + "\n").encode("utf-8")


# ---------------------------------------------------------------------------
# The TeX runner: one long-lived container per invocation, jobs via docker exec
# ---------------------------------------------------------------------------

def read_image(repo: Path) -> str:
    text = (repo / WORKFLOW).read_text(encoding="utf-8")
    m = re.search(r"^\s*TEX_IMAGE:\s*(\S+)\s*$", text, re.M)
    if not m or "@sha256:" not in m.group(1):
        raise SystemExit("gen_contract: no digest-pinned TEX_IMAGE in %s" % WORKFLOW)
    return m.group(1)


class Tex:
    def __init__(self, image: str, work: Path):
        self.image = image
        home = Path.home().resolve()
        work = work.resolve()
        if home not in work.parents and work != home:
            raise SystemExit("gen_contract: work dir %s is not under $HOME; colima "
                             "mounts only $HOME by default" % work)
        self.host = work / ("run-" + uuid.uuid4().hex[:12])
        self.host.mkdir(parents=True)
        self.name = "lp-contract-" + self.host.name
        env = []
        for k, v in TEX_ENV.items():
            env += ["-e", "%s=%s" % (k, v)]
        r = subprocess.run(["docker", "run", "-d", "--rm", "--name", self.name,
                            "-v", "%s:%s" % (self.host, CONTAINER_WORK)] + env +
                           [image, "sleep", "infinity"], capture_output=True, text=True)
        if r.returncode != 0:
            shutil.rmtree(self.host, ignore_errors=True)
            raise SystemExit("gen_contract: cannot start the pinned image: %s" % r.stderr)
        # The mount must be live: a file written on the host must be visible.
        (self.host / "mount_probe").write_text("ok")
        r = self.sh("cat %s/mount_probe" % CONTAINER_WORK)
        if r.stdout.strip() != "ok":
            self.close()
            raise SystemExit("gen_contract: work dir is not visible in the container")

    def sh(self, cmd: str, timeout: int = 120):
        return subprocess.run(["docker", "exec", self.name, "bash", "-c", cmd],
                               capture_output=True, text=True, timeout=timeout)

    def job(self, name: str) -> Path:
        d = self.host / name
        if d.exists():
            shutil.rmtree(d)
        d.mkdir(parents=True)
        return d

    def run(self, jobdir: Path, argv: list, timeout: int) -> tuple:
        """Run argv in the container in jobdir under coreutils `timeout`.
        Returns (rc, seconds). rc 124 = timed out."""
        rel = jobdir.relative_to(self.host).as_posix()
        t0 = time.monotonic()
        r = subprocess.run(["docker", "exec", "-w", "%s/%s" % (CONTAINER_WORK, rel),
                            self.name, "timeout", str(timeout)] + argv,
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                           timeout=timeout + 60)
        return r.returncode, time.monotonic() - t0

    def pdflatex(self, jobdir: Path, tex: bytes, *, halt: bool = True,
                 recorder: bool = False, timeout: int = LONG_TIMEOUT) -> dict:
        (jobdir / "job.tex").write_bytes(tex)
        argv = ["pdflatex", "-interaction=nonstopmode"]
        if halt:
            argv.append("-halt-on-error")
        if recorder:
            argv.append("-recorder")
        argv.append("job.tex")
        rc, secs = self.run(jobdir, argv, timeout)
        log = (jobdir / "job.log").read_bytes() if (jobdir / "job.log").exists() else b""
        fls = (jobdir / "job.fls").read_bytes() if (jobdir / "job.fls").exists() else b""
        return {"rc": rc, "secs": secs, "log": log, "fls": fls,
                "pdf": (jobdir / "job.pdf").exists(), "tex_sha256": sha256_bytes(tex)}

    def close(self):
        subprocess.run(["docker", "rm", "-f", self.name], capture_output=True)
        if os.environ.get("LP_CONTRACT_KEEP_WORK") != "1":
            shutil.rmtree(self.host, ignore_errors=True)

    def __enter__(self):
        return self

    def __exit__(self, *a):
        self.close()


# ---------------------------------------------------------------------------
# Pin and kernel
# ---------------------------------------------------------------------------

def get_pin(tex: Tex, image: str) -> dict:
    r = tex.sh("set -e; pdflatex --version | head -1; uname -m; "
               "f=$(kpsewhich -engine=pdftex pdflatex.fmt); echo \"$f\"; "
               "sha256sum \"$f\" | cut -d' ' -f1; "
               "root=$(kpsewhich -var-value TEXMFROOT); echo \"$root\"; "
               "sha256sum \"$root/tlpkg/texlive.tlpdb\" | cut -d' ' -f1")
    lines = r.stdout.strip().split("\n")
    if r.returncode != 0 or len(lines) != 6:
        raise SystemExit("gen_contract: cannot read the pin: %s %s" % (r.stdout, r.stderr))
    banner, arch, fmt_path, fmt_sha, root, tlpdb = lines
    return {"image": image, "arch": arch, "engine_banner": banner,
            "fmt_path": fmt_path, "fmt_sha256": fmt_sha, "texmf_root": root,
            "tlpdb_sha256": tlpdb}


def format_banners(log: bytes) -> dict:
    """First `LaTeX2e <...>` and `L3 programming layer <...>` lines (a normal
    run prints both from the every-job hook; INITEX prints only the first)."""
    out = {}
    for m in re.finditer(rb"^(LaTeX2e <[^>]*>|L3 programming layer <[^>]*>)\r?$",
                         log, re.M):
        line = m.group(1).decode("utf-8", "replace")
        out.setdefault("latex" if line.startswith("LaTeX2e") else "l3", line)
    return out


FMT_STOP = b"\\csname @@end\\endcsname\n"


def fmt_state_dump(tex: Tex, jobname: str, names: list, *, actives=False,
                   u8_sweep=False, recorder=False) -> tuple:
    block, unw = dump_block(names, actives=actives, u8_sweep=u8_sweep)
    res = tex.pdflatex(tex.job(jobname), block + FMT_STOP, recorder=recorder)
    d = parse_dump(res["log"])
    if res["rc"] != 0 or d["error"] is not None:
        raise SystemExit("gen_contract: format-state dump %s failed: rc=%d %s" %
                         (jobname, res["rc"], d["error"]))
    return d, unw, res


def build_kernel(tex: Tex, pin: dict, report: dict) -> dict:
    """INITEX trace of pdflatex.ini, then format-state meaning dumps until the
    set of names referenced from dumped meanings stops growing."""
    t0 = time.monotonic()
    jd = tex.job("kernel_initex")
    rc, secs = tex.run(jd, ["pdftex", "-ini", "-etex", "-interaction=nonstopmode",
                            "-jobname=lpkernel", "-progname=pdflatex",
                            "-translate-file=cp227.tcx",
                            "\\tracingassigns=1 \\tracingrestores=1 \\tracingonline=0 "
                            "\\input pdflatex.ini"], LONG_TIMEOUT)
    log = (jd / "lpkernel.log").read_bytes()
    tr = parse_trace(log)
    if rc != 0 or tr["first_error"] is not None:
        raise SystemExit("gen_contract: INITEX of pdflatex.ini failed: rc=%d %s" %
                         (rc, tr["first_error"]))
    banners = format_banners(log)
    report["kernel_initex_secs"] = round(secs, 1)
    report["kernel_trace_records"] = tr["records"]
    shutil.rmtree(jd)
    cs = sorted(nm for (kind, nm) in tr["names"] if kind == "cs")
    meanings: dict = {}
    unwritable: set = set()
    todo = cs
    rounds = 0
    base = None
    while todo and rounds < 6:
        rounds += 1
        d, unw, res = fmt_state_dump(tex, "kernel_dump%d" % rounds, todo,
                                     actives=(rounds == 1), recorder=(rounds == 1))
        if rounds == 1:
            base = (d, res)
        unwritable.update(unw)
        for i, nm in enumerate(todo):
            if nm in unw:
                continue
            meanings[nm] = d["meanings"].get(i)
        new = set()
        for m in d["meanings"].values():
            if m is not None:
                new |= referenced_names(m)
        todo = sorted(n for n in new if n not in meanings and n not in unwritable)
    d1, res1 = base
    _, fls_inputs = parse_fls(res1["fls"])
    defined = {nm: m for nm, m in meanings.items() if m is not None}
    report["kernel_dump_rounds"] = rounds
    report["kernel_secs"] = round(time.monotonic() - t0, 1)
    return {
        "fmt_sha256": pin["fmt_sha256"],
        "banners": banners,
        "initex_names": len(cs),
        "names": {name_str(k): name_str(v) for k, v in defined.items()},
        "actives": {str(b): name_str(m) for b, m in d1["actives"].items()},
        "catcodes": d1["catcodes"],
        "baseline_inputs": [p for p in fls_inputs if p.startswith("/")],
        "unwritable": sorted(name_str(x) for x in unwritable),
        "dump_rounds": rounds,
        "trace_unparsed": tr["unparsed"],
    }


def load_kernel(tex: Tex, pin: dict, cache: Path, fresh: bool, report: dict) -> dict:
    cache.mkdir(parents=True, exist_ok=True)
    path = cache / ("kernel-%s.json" % pin["fmt_sha256"])
    if path.exists() and not fresh:
        k = json.loads(path.read_text(encoding="utf-8"))
        if k.get("generator_version") == GENERATOR_VERSION:
            report["kernel_cache"] = "hit"
            return k
    report["kernel_cache"] = "miss"
    k = build_kernel(tex, pin, report)
    k["generator_version"] = GENERATOR_VERSION
    tmp = path.with_suffix(".tmp")
    tmp.write_text(json.dumps(k, ensure_ascii=False, sort_keys=True), encoding="utf-8")
    tmp.replace(path)
    return k


def kernel_public(kernel: dict, pin: dict) -> dict:
    """The committed kernel file: names and their meaning kinds (no bodies)."""
    names = {}
    for n, m in kernel["names"].items():
        nb = name_bytes(n)
        names[n] = short_kind(classify_meaning(nb, name_bytes(m)))
    digest = sha256_bytes("\n".join("%s\t%s" % (n, kernel["names"][n])
                                    for n in sorted(kernel["names"])).encode("utf-8"))
    return {"schema": KERNEL_SCHEMA, "generator_version": GENERATOR_VERSION,
            "pin": {k: pin[k] for k in ("image", "arch", "engine_banner", "fmt_sha256")},
            "banners": kernel["banners"],
            "method": "INITEX pdftex -ini -etex pdflatex.ini under \\tracingassigns=1 "
                      "\\tracingrestores=1; every traced name, and every name "
                      "referenced from a dumped meaning, dumped with \\meaning in "
                      "format state until no new name appears; the defined ones",
            "initex_traced_names": kernel["initex_names"],
            "dump_rounds": kernel["dump_rounds"],
            "unwritable_names": kernel["unwritable"],
            "meanings_sha256": digest,
            "count": len(names),
            "names": names}


# ---------------------------------------------------------------------------
# Contract generation
# ---------------------------------------------------------------------------

def texmf_rel(path: str, root: str) -> str:
    root = root.rstrip("/") + "/"
    return path[len(root):] if path.startswith(root) else path


def hash_files(tex: Tex, paths: list) -> dict:
    if not paths:
        return {}
    listing = tex.host / "hash_list.txt"
    listing.write_text("\n".join(paths) + "\n", encoding="utf-8")
    r = tex.sh("xargs -d '\\n' -a %s/hash_list.txt sha256sum" % CONTAINER_WORK)
    out = {}
    for line in r.stdout.splitlines():
        h, _, p = line.partition("  ")
        out[p] = h
    missing = [p for p in paths if p not in out]
    if missing:
        raise SystemExit("gen_contract: could not hash %s" % missing[:5])
    return out


def generate(cfg: dict, tex: Tex, pin: dict, kernel: dict, use_names: list,
             report: dict) -> dict:
    cfg = normalize_config(cfg)
    labels = segment_labels(cfg)
    reasons = []
    t0 = time.monotonic()
    pre = preamble_tex(cfg)
    provenance = {}

    # R1: the load outcome, pristine configuration. This compile IS the attestation.
    r1 = tex.pdflatex(tex.job("r1_load"), pre + b"\\begin{document}\n\\end{document}\n",
                      recorder=True)
    report["r1_secs"] = round(r1["secs"], 2)
    provenance["load_tex_sha256"] = r1["tex_sha256"]
    err1 = first_error(r1["log"])

    # R2: pass 1, the trace, with load-boundary markers.
    trace_tex = (b"\\tracingassigns=1 \\tracingrestores=1 \\tracingonline=0\n" +
                 preamble_tex(cfg, markers=True) +
                 b"\\begin{document}\n\\immediate\\write-1{LPSEG:%d}\n"
                 b"\\tracingassigns=0 \\tracingrestores=0\n\\end{document}\n"
                 % (len(labels)))
    r2 = tex.pdflatex(tex.job("r2_trace"), trace_tex)
    report["r2_secs"] = round(r2["secs"], 2)
    provenance["trace_tex_sha256"] = r2["tex_sha256"]
    tr = parse_trace(r2["log"])
    report["trace_records"] = tr["records"]

    def seg_label(k):
        if k < 0:
            return "before_class"
        return labels[k] if k < len(labels) else "body"

    if r1["rc"] != 0 or err1 is not None:
        seg = tr["first_error"][0] if tr["first_error"] else None
        if tr["first_error"] is None or tr["first_error"][1] != err1:
            reasons.append("load and trace runs disagree on the fatal error")
        load = {"status": "fatal", "rc": r1["rc"], "message": err1,
                "error_class": classify_error(err1 or ""),
                "load_index": seg, "segment": seg_label(seg) if seg is not None else None}
    else:
        load = {"status": "ok"}
        if r2["rc"] != 0 or tr["first_error"] is not None:
            reasons.append("trace run failed where the load run succeeded")

    # files_read: R1 .fls minus the empty-job baseline minus job-local files.
    _, inputs = parse_fls(r1["fls"])
    base = set(kernel["baseline_inputs"])
    reads = sorted(p for p in inputs if p.startswith("/") and p not in base
                   and not p.startswith(CONTAINER_WORK + "/"))
    hashes = hash_files(tex, reads)
    files_read = [{"path": texmf_rel(p, pin["texmf_root"]), "sha256": hashes[p]}
                  for p in reads]
    files_read.sort(key=lambda d: d["path"])

    key_material = canonical_json({"configuration": cfg, "fmt_sha256": pin["fmt_sha256"],
                                   "files": files_read})
    config_key = sha256_bytes(key_material.encode("utf-8"))

    contract = {
        "schema": SCHEMA,
        "generator": {"tool": "scripts/tools/gen_contract.py",
                      "version": GENERATOR_VERSION},
        "configuration": cfg,
        "config_key": config_key,
        "pin": {k: pin[k] for k in ("image", "arch", "engine_banner", "fmt_sha256",
                                     "tlpdb_sha256")},
        "banners": format_banners(r1["log"]),
        "load_outcome": load,
        "files_read": files_read,
    }
    if contract["banners"].get("latex") != kernel["banners"].get("latex"):
        reasons.append("the INITEX kernel's LaTeX banner differs from the format's")

    if load["status"] != "ok":
        reasons.insert(0, "load_fatal: the configuration does not load, so no name "
                          "set was generated")
        contract.update({"complete": False, "incomplete_reasons": reasons,
                         "provenance": provenance})
        report["total_secs"] = round(time.monotonic() - t0, 1)
        return contract

    # Tracing must have stayed on from our first line to our last.
    own = [t for t in tr["tracing_toggles"]]
    # Ours: the first line (segment -1) switches both on; the line after the
    # last marker switches \tracingassigns off (printed as its "changing").
    foreign = [t for t in own if not (
        t[0] == -1 or (t[1] == "changing" and t[2] == "tracingassigns"
                       and t[0] == len(labels)))]
    if foreign:
        reasons.append("tracing was toggled by the configuration: %r" % foreign[:3])
    if tr["unparsed"]:
        reasons.append("%d trace records could not be parsed" % tr["unparsed"])

    traced = {}
    for (kind, nm), seg in tr["names"].items():
        if kind == "cs":
            traced[nm] = seg
    traced_active = {nm[0]: seg for (kind, nm), seg in tr["names"].items()
                     if kind == "active"}
    kernel_names = {name_bytes(n): name_bytes(m) for n, m in kernel["names"].items()}
    universe = sorted(set(kernel_names) | set(traced))

    # R4: format-state meanings of traced names the kernel does not have.
    extra = sorted(n for n in traced if n not in kernel_names)
    fmt_meaning = dict(kernel_names)
    if extra:
        d4, _, r4 = fmt_state_dump(tex, "r4_fmt_extra", extra)
        provenance["fmt_extra_tex_sha256"] = r4["tex_sha256"]
        kernel_gaps = []
        for i, nm in enumerate(extra):
            m = d4["meanings"].get(i)
            if m is not None:
                fmt_meaning[nm] = m
                kernel_gaps.append(name_str(nm))
        if kernel_gaps:
            contract["kernel_gaps"] = sorted(kernel_gaps)

    # R3: pass 2, the body-start meaning dump (after the begin-document hooks).
    block, unw = dump_block(universe, actives=True, u8_sweep=True)
    r3 = tex.pdflatex(tex.job("r3_dump"), pre + b"\\begin{document}\n" + block +
                      b"\\end{document}\n")
    report["r3_secs"] = round(r3["secs"], 2)
    provenance["dump_tex_sha256"] = r3["tex_sha256"]
    d3 = parse_dump(r3["log"])
    if r3["rc"] != 0 or d3["error"] is not None:
        reasons.append("body-start dump failed: rc=%d %s" % (r3["rc"], d3["error"]))
    bad_prims = sorted(p for p, m in d3["prims"].items() if m != "\\" + p)
    if bad_prims or len(d3["prims"]) != len(DUMP_PRIMITIVES):
        reasons.append("dump primitives redefined or missing: %s" % bad_prims)
    if unw:
        contract["unwritable_names"] = sorted(name_str(n) for n in unw)
    body = {}
    for i, nm in enumerate(universe):
        if nm in unw:
            continue
        if i not in d3["meanings"]:
            reasons.append("dump lost name %s" % name_str(nm))
            continue
        body[nm] = d3["meanings"][i]

    defined, reverted, untraced = {}, [], []
    for nm, bm in body.items():
        km = fmt_meaning.get(nm)
        if bm == km:
            if nm in traced:
                reverted.append(name_str(nm))
            continue
        if nm not in traced:
            untraced.append(name_str(nm))
        d = classify_meaning(nm, bm)
        d["meaning_sha256"] = sha256_bytes(bm or b"undefined")[:16]
        d["set_in"] = seg_label(traced[nm]) if nm in traced else "untraced"
        defined[name_str(nm)] = d
    if untraced:
        reasons.append("%d names changed meaning without a traced assignment: %s"
                       % (len(untraced), sorted(untraced)[:5]))
    members = {nm for nm, bm in body.items() if bm is not None}

    # Active characters and catcodes, against format state.
    kact = {int(b): name_bytes(m) for b, m in kernel["actives"].items()}
    active_diff = {}
    for b, m in sorted(d3["actives"].items()):
        if kact.get(b) != m:
            d = classify_meaning(bytes([b]), m)
            d["meaning_sha256"] = sha256_bytes(m)[:16]
            active_diff["%d" % b] = d
    untraced_act = [b for b in active_diff if int(b) not in traced_active]
    if untraced_act:
        reasons.append("active characters changed without a traced assignment: %s"
                       % untraced_act)
    cat_diff = {}
    if d3["catcodes"] is None or len(d3["catcodes"]) != 256:
        reasons.append("catcode dump missing")
    else:
        for b in range(256):
            if d3["catcodes"][b] != kernel["catcodes"][b]:
                cat_diff["%d" % b] = {"format": kernel["catcodes"][b],
                                      "body_start": d3["catcodes"][b]}

    # Unicode: sweep vs closed-world u8: names in the BMP.
    swept = d3["u8"]
    named = set()
    for nm in members:
        if nm.startswith(b"u8:"):
            try:
                s = nm[3:].decode("utf-8")
            except UnicodeDecodeError:
                continue
            if len(s) == 1:
                named.add(ord(s))
    named_bmp = {c for c in named if c <= 0xFFFF}
    if swept != named_bmp:
        reasons.append("u8 sweep and closed-world names disagree on %d code points"
                       % len(swept ^ named_bmp))
    unicode = {"defined": ["U+%04X" % c for c in sorted(swept | named)],
               "sweep_range": "U+0080..U+FFFF minus surrogates",
               "sweep_count": len(swept),
               "beyond_bmp_from_names": ["U+%04X" % c for c in sorted(named - named_bmp)]}

    # Counters and key families, from the body-start closed world.
    counters = {}
    for nm in sorted(members):
        if not nm.startswith(b"c@"):
            continue
        c = classify_meaning(nm, body[nm])
        if c["kind"] != "Register" or c["register"] != "count":
            continue
        x = nm[2:]
        resets = []
        cl = body.get(b"cl@" + x)
        if cl:
            resets = sorted({name_str(r) for r in re.findall(rb"\\@elt \{([^{}]*)\}", cl)})
        counters[name_str(x)] = {"the": (b"the" + x) in members, "resets": resets,
                                 "kernel": nm in kernel_names}
    families: dict = {}
    options = []
    for nm in sorted(members):
        if nm.startswith(b"KV@"):
            fam, _, key = nm[3:].partition(b"@")
            if not key or not fam:
                continue
            f = families.setdefault(name_str(fam), {})
            if key.endswith(b"@default"):
                f.setdefault(name_str(key[:-8]), {})["has_default"] = True
            else:
                f.setdefault(name_str(key), {}).setdefault("has_default", False)
        elif nm.startswith(b"ds@") and len(nm) > 3:
            options.append(name_str(nm[3:]))

    # R5: the closure self-check, an independent run.
    rng = random.Random(int(config_key[:16], 16))
    member_list = sorted(members)
    k = max(1, math.ceil(0.01 * len(member_list)))
    sample = sorted(rng.sample(member_list, k))
    refs = set()
    for nm, bm in body.items():
        if bm is not None:
            refs |= referenced_names(bm)
    ref_list = sorted(refs)
    given = sorted({name_bytes(u) for u in use_names})
    tests = sample + ref_list + given
    block5, unw5 = dump_block([], actives=False, u8_sweep=False, tests=tests)
    r5 = tex.pdflatex(tex.job("r5_selfcheck"), pre + b"\\begin{document}\n" + block5 +
                      b"\\end{document}\n")
    report["r5_secs"] = round(r5["secs"], 2)
    provenance["selfcheck_tex_sha256"] = r5["tex_sha256"]
    d5 = parse_dump(r5["log"])
    if r5["rc"] != 0 or d5["error"] is not None:
        reasons.append("self-check run failed: rc=%d %s" % (r5["rc"], d5["error"]))
    unw5 = set(unw5)
    mismatches = []
    for i, nm in enumerate(tests):
        if nm in unw5:
            continue
        got = d5["tests"].get(i)
        want = nm in members
        if got is None or got != want:
            mismatches.append({"name": name_str(nm), "ifcsname": got, "member": want})
    mismatches.sort(key=lambda d: d["name"])
    self_check = {
        "sample_fraction": 0.01, "sample_seed": config_key[:16],
        "sampled_members": len(sample),
        "referenced_names": len(ref_list),
        "referenced_non_members": sum(1 for n in ref_list if n not in members),
        "use_names": len(given), "use_names_list": [name_str(n) for n in given],
        "unwritable": len(unw5),
        "mismatches": mismatches[:50], "mismatch_count": len(mismatches),
        "pass": not mismatches and not (r5["rc"] != 0),
    }
    if not self_check["pass"]:
        reasons.append("closure self-check failed (%d mismatches)" % len(mismatches))

    contract.update({
        "closed_world": {"kernel_names": len(kernel_names), "members": len(members),
                         "traced_names": len(traced), "universe": len(universe)},
        "defined_names": defined,
        "reverted_names": sorted(reverted),
        "active_chars": active_diff,
        "catcodes": cat_diff,
        "unicode": unicode,
        "counters": counters,
        "key_families": families,
        "declared_options": sorted(options),
        "self_check": self_check,
        "complete": not reasons,
        "incomplete_reasons": reasons,
        "provenance": provenance,
    })
    report["total_secs"] = round(time.monotonic() - t0, 1)
    return contract


# ---------------------------------------------------------------------------
# Probe harness (M1 slice 1: harness only; the typed lattice is slice 2)
# ---------------------------------------------------------------------------

def probe_doc(cfg: dict, snippet: str) -> bytes:
    return (preamble_tex(normalize_config(cfg)) + b"\\begin{document}\n" +
            snippet.encode("utf-8") + b"\n\\end{document}\n")


def probe_family(name: str, d: dict) -> list:
    """Probe snippets for one command from its meaning. The arity is only the
    static hint (design B.2: a shape read is never attestation)."""
    n = d.get("arity_hint", 0)
    if "ltcmd_spec" in d:
        n = d["ltcmd_spec"].count("m")
    args = "{a}" * n
    margs = "{1}" * n
    fam = [("text", "x \\%s%s y" % (name, args)),
           ("math", "$\\%s%s$" % (name, margs))]
    if n >= 1:
        fam.append(("par_in_arg", "x \\%s{a\\par b}%s y" % (name, "{a}" * (n - 1))))
        fam.append(("missing_arg", "x {\\%s} y" % name))
    return fam


def run_probes(tex: Tex, contract: dict, names: list, workers: int, report: dict,
               texmf_root: str, kernel: dict):
    cfg = contract["configuration"]
    base_fls = None
    r = tex.pdflatex(tex.job("probe_base"), probe_doc(cfg, ""), recorder=True)
    _, base_inputs = parse_fls(r["fls"])
    base_fls = set(base_inputs)
    probes = []
    for nm in names:
        def meaning_of(n):
            if n in contract["defined_names"]:
                return contract["defined_names"][n]
            if n in kernel["names"]:
                return classify_meaning(name_bytes(n), name_bytes(kernel["names"][n]))
            return {"kind": "Undefined"}
        d = meaning_of(nm)
        if d.get("robust_inner"):
            d = meaning_of(d["robust_inner"])
        for fam, snip in probe_family(nm, d):
            probes.append({"id": "%s/%s" % (nm, fam), "name": nm, "family": fam,
                           "snippet": snip})
    probes.sort(key=lambda p: p["id"])

    def solo(i_p):
        i, p = i_p
        jd = tex.job("probe_%04d" % i)
        res = tex.pdflatex(jd, probe_doc(cfg, p["snippet"]), recorder=True,
                           timeout=PROBE_TIMEOUT)
        out = classify_outcome(res["rc"], res["log"], res["pdf"])
        _, ins = parse_fls(res["fls"])
        lazy = sorted(texmf_rel(x, texmf_root) for x in ins
                      if x.startswith("/") and x not in base_fls
                      and not x.startswith(CONTAINER_WORK + "/"))
        shutil.rmtree(jd, ignore_errors=True)
        return i, out, lazy, res["secs"]

    t0 = time.monotonic()
    with ThreadPoolExecutor(max_workers=workers) as ex:
        results = list(ex.map(solo, list(enumerate(probes))))
    report["solo_secs"] = round(time.monotonic() - t0, 1)
    report["solo_probe_mean_secs"] = round(sum(r[3] for r in results) / max(1, len(results)), 3)
    for i, out, lazy, _ in results:
        probes[i]["solo"] = out
        if lazy:
            probes[i]["lazy_files"] = lazy

    # Batched triage: all probes of one command in one nonstop run, markers
    # between them, errors attributed to the segment they appear in.
    by_name: dict = {}
    for i, p in enumerate(probes):
        by_name.setdefault(p["name"], []).append(i)
    t0 = time.monotonic()

    def batch(item):
        nm, idxs = item
        lines = []
        for i in idxs:
            lines.append("\\immediate\\write-1{LPPROBE:%d}" % i)
            lines.append("\\begingroup %s\\par\\endgroup" % probes[i]["snippet"])
        lines.append("\\immediate\\write-1{LPPROBE:end}")
        jd = tex.job("batch_" + hashlib.sha256(nm.encode()).hexdigest()[:10])
        res = tex.pdflatex(jd, probe_doc(cfg, "\n".join(lines)), halt=False,
                           timeout=PROBE_TIMEOUT * 4)
        seen = {}
        cur = None
        for raw in res["log"].split(b"\n"):
            m = re.match(rb"^LPPROBE:(\d+|end)$", raw.rstrip(b"\r"))
            if m:
                cur = None if m.group(1) == b"end" else int(m.group(1))
                if cur is not None:
                    seen.setdefault(cur, [])
                continue
            if cur is not None and raw.startswith(b"! "):
                seen[cur].append(raw[2:].decode("utf-8", "replace").strip())
        shutil.rmtree(jd, ignore_errors=True)
        return {i: ("timeout" if res["rc"] == TIMEOUT_RC else
                    ("unreached" if i not in seen else
                     ("fatal" if seen[i] else "ok"))) for i in idxs}

    with ThreadPoolExecutor(max_workers=workers) as ex:
        for part in ex.map(batch, sorted(by_name.items())):
            for i, pol in part.items():
                probes[i]["batch"] = pol
    report["batch_secs"] = round(time.monotonic() - t0, 1)

    agree = disagree = inconclusive = 0
    dis = []
    for p in probes:
        s = "ok" if p["solo"]["outcome"] == "ok" else "fatal"
        if p["solo"]["outcome"] == "timeout" or p["batch"] in ("timeout", "unreached"):
            inconclusive += 1
        elif s == p["batch"]:
            agree += 1
        else:
            disagree += 1
            dis.append(p["id"])
    classes: dict = {}
    for p in probes:
        c = p["solo"].get("error_class", "ok")
        classes[c] = classes.get(c, 0) + 1
    return {
        "schema": PROBE_SCHEMA,
        "generator": {"tool": "scripts/tools/gen_contract.py", "version": GENERATOR_VERSION},
        "config_key": contract["config_key"],
        "configuration": contract["configuration"],
        "pin": contract["pin"],
        "protocol": {"solo": "pdflatex -interaction=nonstopmode -halt-on-error -recorder, "
                             "fresh directory, coreutils timeout %ds; ok = rc 0 and a PDF; "
                             "otherwise the error class of the first `!` line" % PROBE_TIMEOUT,
                     "batch": "every probe of one command in one -interaction=nonstopmode "
                              "run (no -halt-on-error), each in \\begingroup...\\par\\endgroup "
                              "after a marker; polarity = any `!` line in its segment",
                     "lazy_files": "solo .fls INPUT files minus those of the same "
                                   "configuration with an empty body"},
        "commands": sorted(set(p["name"] for p in probes)),
        "probes": probes,
        "summary": {"probes": len(probes), "error_classes": classes,
                    "batch_vs_solo": {"agree": agree, "disagree": disagree,
                                      "inconclusive": inconclusive,
                                      "disagreements": dis}},
    }


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _pkg(spec: str) -> dict:
    m = re.fullmatch(r"([^\[\]]+)(?:\[(.*)\])?", spec)
    if not m:
        raise argparse.ArgumentTypeError("bad package spec %r" % spec)
    opts = [o for o in (m.group(2) or "").split(",") if o]
    return {"package": m.group(1), "options": opts}


def config_from_args(a) -> dict:
    if a.config:
        return json.loads(Path(a.config).read_text(encoding="utf-8"))
    if not a.cls:
        raise SystemExit("gen_contract: give --config or --class")
    return {"class": a.cls,
            "class_options": [o for o in (a.class_options or "").split(",") if o],
            "preamble": a.items or []}


def kernel_rel(pin: dict) -> Path:
    return CONTRACT_DIR / "kernel" / ("%s-%s.json" % (pin["arch"], pin["fmt_sha256"][:16]))


def attach_kernel_ref(contract: dict, kernel: dict, pin: dict) -> None:
    contract["kernel"] = {"file": kernel_rel(pin).as_posix(),
                          "meanings_sha256": kernel_public(kernel, pin)["meanings_sha256"],
                          "count": len(kernel["names"])}


def write_kernel_file(repo: Path, kernel: dict, pin: dict) -> Path:
    kp = repo / kernel_rel(pin)
    kp.parent.mkdir(parents=True, exist_ok=True)
    kp.write_text(canonical_json(kernel_public(kernel, pin)), encoding="utf-8")
    return kp


def cmd_generate(a) -> int:
    repo = Path(a.repo).resolve()
    image = read_image(repo)
    cfg = normalize_config(config_from_args(a))
    use_names = []
    if a.use_names:
        use_names = [ln for ln in Path(a.use_names).read_text(encoding="utf-8").splitlines()
                     if ln.strip()]
    report = {}
    with Tex(image, Path(a.work).expanduser()) as tex:
        pin = get_pin(tex, image)
        kernel = load_kernel(tex, pin, Path(a.cache).expanduser(), a.fresh_kernel, report)
        contract = generate(cfg, tex, pin, kernel, use_names, report)
        attach_kernel_ref(contract, kernel, pin)
    out = Path(a.out) if a.out else repo / CONTRACT_DIR / (a.name + ".json")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(canonical_json(contract), encoding="utf-8")
    if not a.no_kernel_file:
        kp = write_kernel_file(repo, kernel, pin)
        report["kernel_file"] = str(kp)
    report["contract"] = str(out)
    report["contract_bytes"] = out.stat().st_size
    report["complete"] = contract["complete"]
    report["incomplete_reasons"] = contract["incomplete_reasons"]
    print(json.dumps(report, indent=1, sort_keys=True), file=sys.stderr)
    return 0


def cmd_probes(a) -> int:
    repo = Path(a.repo).resolve()
    image = read_image(repo)
    contract = json.loads(Path(a.contract).read_text(encoding="utf-8"))
    public = sorted(n for n, d in contract.get("defined_names", {}).items()
                    if re.fullmatch(r"[A-Za-z]+", n) and d["kind"] == "Macro"
                    and not d.get("delimited"))
    seed = int(contract["config_key"][:16], 16)
    names = sorted(random.Random(seed).sample(public, min(a.sample, len(public))))
    for n in (a.names or "").split(","):
        if n and n not in names:
            names.append(n)
    report = {}
    with Tex(image, Path(a.work).expanduser()) as tex:
        pin = get_pin(tex, image)
        if pin["fmt_sha256"] != contract["pin"]["fmt_sha256"]:
            raise SystemExit("gen_contract: the image's format differs from the contract's")
        kernel = load_kernel(tex, pin, Path(a.cache).expanduser(), False, report)
        out = run_probes(tex, contract, sorted(names), a.workers, report,
                         pin["texmf_root"], kernel)
    out["selection"] = {"sample": a.sample, "seed": contract["config_key"][:16],
                        "from": "public (letters-only), undelimited Macro names in "
                                "defined_names", "extra_names": [n for n in (a.names or "").split(",") if n]}
    Path(a.out).write_text(canonical_json(out), encoding="utf-8")
    report["summary"] = out["summary"]
    print(json.dumps(report, indent=1, sort_keys=True), file=sys.stderr)
    return 0


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--repo", default=str(REPO))
    ap.add_argument("--work", default="~/.cache/lp-oracle/contracts/work")
    ap.add_argument("--cache", default="~/.cache/lp-oracle/contracts/cache")
    sub = ap.add_subparsers(dest="cmd", required=True)
    g = sub.add_parser("generate")
    g.add_argument("--config")
    g.add_argument("--class", dest="cls")
    g.add_argument("--class-options")
    g.add_argument("--package", dest="items", action="append", type=_pkg)
    g.add_argument("--definer", dest="items", action="append",
                   type=lambda s: {"definer": s})
    g.add_argument("--name", required=True)
    g.add_argument("--out")
    g.add_argument("--use-names")
    g.add_argument("--fresh-kernel", action="store_true",
                   help="rebuild the kernel from INITEX even if cached")
    g.add_argument("--no-kernel-file", action="store_true")
    p = sub.add_parser("probes")
    p.add_argument("--contract", required=True)
    p.add_argument("--sample", type=int, default=30)
    p.add_argument("--names", help="comma-separated extra names to probe")
    p.add_argument("--workers", type=int, default=4)
    p.add_argument("--out", required=True)
    a = ap.parse_args(argv)
    return cmd_generate(a) if a.cmd == "generate" else cmd_probes(a)


if __name__ == "__main__":
    sys.exit(main())
