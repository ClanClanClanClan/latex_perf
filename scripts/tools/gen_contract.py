#!/usr/bin/env python3
"""Generate a configuration contract under the pinned TeX Live image (ADR-012, M1 slice 1).

A configuration is a document class with its options, followed by an ordered list
of package loads (each with options) and, optionally, preamble definer lines
interleaved with them. The contract records what that exact configuration does
under the oracle, which ADR-012 decision 7 freezes as CI's digest-pinned image
(`TEX_IMAGE` in .github/workflows/tex-oracle.yml, read from there, never
restated here). Every TeX job runs inside that image through the ONE oracle
entry point, scripts/tools/_oracle.py (`run_engine`, `image_command`); this
file starts no engine and no container of its own (check_oracle_pin.py). The
laptop TeX Live is never used.

Nothing in a contract is hand-listed. Every field comes from a TeX run:

  pin             engine banner, pdflatex.fmt sha256, texlive.tlpdb sha256,
                  image reference and architecture, LaTeX and L3 banners.
  kernel          every name defined in format state (a job after \\everyjob).
                  Candidates: every string of the shipped format's string pool,
                  the engine's primitives (virgin INITEX, counted against TeX's
                  own cs_count), every name the INITEX run of pdflatex.ini and
                  its \\everyjob replay assigns, all one-character names and the
                  null name; dumped with \\meaning in format state, closed over
                  referenced names. COMPLETE because TeX's own count of its hash
                  table finds 0 entries outside the candidates (hash_coverage).
                  Cached by fmt hash and generator source hash.
  load_outcome    the configuration plus \\begin{document}\\end{document}
                  under the GRADING environment and the oracle's pass protocol
                  (run_to_fixpoint: to the first rc 0 in at most 3 runs, then a
                  confirming run), -halt-on-error: ok, or the first `!` error
                  of the last run, the pass count and the load segment. The
                  same run under the forced date must agree.
  files_read      the .fls (-recorder) of the forced run's first pass, minus the
                  files an empty format-state job reads, minus job-local files;
                  with sha256.
  defined_names   pass 1 traces every assignment from before \\documentclass
                  until after the begin-document hooks, with a marker between
                  loads. The body-start state is then taken on EVERY pass the
                  oracle's protocol can run (protocol_histories: after the
                  histories '', F, S, FF, FS, FFS of completed (S) and failed
                  (F) passes, i.e. passes 1 to MAX_PASSES+1; a pass after
                  history h runs on the files the passes of h wrote), in
                  three environments: forced date / job name `job` (the
                  reference), the graders' real clock / `job`, and the real
                  clock / a second job name. On each pass of each: a trace
                  (every name it assigns joins the UNIVERSE, with every name
                  token of the files read, of the definers and of the files
                  the jobs wrote, and the kernel's candidates), a guarded
                  \\meaning dump of the whole universe at body start, and
                  hash_coverage, TeX's own count of its hash table, seeded
                  with the same files and labelled with the pass it
                  describes (coverage_passes). The contract's state is pass
                  1 of the reference. Membership must be the same on every
                  pass and in every environment, and no count may find a name
                  outside the universe, or the contract is incomplete
                  (pass_dependent_state / date_dependent_state /
                  jobname_dependent_state). A name is in defined_names iff
                  its body-start meaning differs from its format-state
                  meaning (class Undefined = the configuration removed a
                  kernel name). Meanings that differ between passes are
                  pass_dependent_meanings; between job names,
                  jobname_dependent_meanings (compare meanings under `job`).
                  Traced names whose meaning is back to the kernel's are
                  listed in reverted_names; primitive parameters the
                  configuration assigned are listed in parameters_assigned
                  (values are not recorded).
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
                  whole universe (members and non-members), on every name
                  referenced from a body-start meaning, and on any --use-names,
                  must agree with membership. Any mismatch sets complete=false.
  complete_scope  what complete=true attests: the configuration's name set,
                  never a document's own names (M2's per-document check).

Signature probes (the typed lattice) are M1 slice 2. This slice ships only the
probe HARNESS (`probes` subcommand): solo -halt-on-error probe documents under
the oracle's pass protocol with a timeout, classified by error class (never by
rc), and a batched run whose polarity is compared with the solo one.

Determinism: every job runs in a fresh directory under the oracle's work root.
The TeX environment is the graders' own (`_oracle.oracle_tex_vars`, one
definition) plus explicit overrides (see LOG_WIDTH): name-set runs add
FORCE_SOURCE_DATE=1; the load outcome is attested without it (the graders'
environment) and must agree. Output JSON is sorted; no timing is written into a contract.
`check_contracts_reproducible.py` regenerates a committed contract and diffs it
byte for byte.

Usage:
  gen_contract.py generate --class article --package amsmath --package hyperref \\
      --name article-amsmath-hyperref [--out corpora/contracts/NAME.json]
  gen_contract.py generate --config CONFIG.json --name NAME
  gen_contract.py probes --contract corpora/contracts/NAME.json --sample 30 \\
      [--names mathbb,frac] --out corpora/contracts/probe_demo_NAME.json

Needs the oracle (_oracle.py: docker with the pinned image pulled, or the
pinned image itself). Work directories lie under the oracle's work root, which
the container sees (colima mounts only $HOME by default).
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import math
import os
import random
import re
import shutil
import struct
import sys
import tarfile
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import _oracle  # noqa: E402  (the ONE oracle entry point, ADR-012 decision 7)

SCHEMA = "lp-configuration-contract/1"
KERNEL_SCHEMA = "lp-kernel-names/1"
PROBE_SCHEMA = "lp-probe-report/1"
# A semantic version, bumped by hand when the generator's OUTPUT changes on
# purpose. Deliberately not a hash of this file: a comment edit must not
# invalidate every committed contract (the C-68 lesson).
GENERATOR_VERSION = "4"

REPO = Path(__file__).resolve().parent.parent.parent
WORKFLOW = Path(".github/workflows/tex-oracle.yml")
CONTRACT_DIR = Path("corpora/contracts")
# THE TeX ENVIRONMENT. Every job runs through the oracle (`_oracle.run_engine`)
# under EXACTLY the variables `tex_vars(env, td)` returns, built on the ONE
# definition of the graders' environment, `_oracle.oracle_tex_vars(td)`
# (openin_any/openout_any=p, SOURCE_DATE_EPOCH=0, a private TEXMFHOME/TEXMFVAR
# below td), which this file never restates. The overrides, each explicit:
#   LOG_WIDTH           every job: no log line wrapping, so a trace record or a
#                       dumped meaning is one line (changes no outcome);
#   FORCE_DATE          "forced" and "second_date": FORCE_SOURCE_DATE=1, which
#                       the graders do NOT set: it pins \\year, \\month, \\day
#                       and \\time to SOURCE_DATE_EPOCH, so name-set runs are
#                       byte-reproducible;
#   SECOND_EPOCH        "second_date" only: another forced date, which finds
#                       the kernel's date-dependent names.
# "grading" is the base plus LOG_WIDTH only: the oracle's own environment (real
# clock), under which the load outcome is attested. Every contract checks that
# the forced date changed nothing (review defect R1.3: `\\ifnum\\year>2000`
# loaded under one and failed under the other). check_gen_contract_parsers.py
# asserts each environment is exactly base + these overrides.
LOG_WIDTH = {"max_print_line": "1000000", "error_line": "254",
             "half_error_line": "238"}
FORCE_DATE = {"FORCE_SOURCE_DATE": "1"}
SECOND_EPOCH = "1790000000"
ENVS = ("forced", "grading", "second_date")
PRIVATE_TEXMF = "<private-texmf>"
# Every job's name. Some meanings hold it (l3's \\c_sys_jobname_str, the file
# currently read, ...), so a contract is exact under this job name only; the
# names whose meaning changes with it are found by a run under the second one
# (review LOW item b) and listed, so a consumer compares meanings under `job`.
JOBNAME = "job"
SECOND_JOBNAME = "lpotherjob"
# diff_real_roots.MAX_PASSES (the oracle's pass protocol, B.4); the parser
# self-test asserts the two agree.
MAX_PASSES = 3
# What `complete` attests (review defect R1.4).
COMPLETE_SCOPE = ("configuration: the name set at body start of this configuration "
                  "is exact (every name TeX's hash table holds there was asked); "
                  "it attests no document's own names, which need a per-document "
                  "self-check (M2)")
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
# Log parsers (unit-tested on recorded fixtures by check_gen_contract_parsers.py)
# ---------------------------------------------------------------------------

_REC_START = re.compile(
    rb"\{(globally )?(changing|into|reassigning|restoring|retaining) ")
# Quantities (not control-sequence meanings) that \tracingassigns also reports.
_QUANTITY = re.compile(
    rb"(?:count|dimen|skip|muskip|toks|box|catcode|lccode|uccode|sfcode|mathcode|"
    rb"delcode|textfont|scriptfont|scriptscriptfont)\d+")
SEG_MARK = re.compile(rb"^LPSEG:(-?\d+)$")
# set_in of a name whose value was restored to one from before the trace.
SEG_BEFORE_TRACE = -2


# What a traced value can start with (`print_cmd_chr` / `show_eqtb`), after the
# escape character where one is printed. A `=` inside a name is legal, so a
# record is split at every `=` whose remainder reads as a value, never only at
# the first one (review defect 3: `\\lpa=b=macro:->x` was read as `lpa`).
_VALUE_WORDS = (b"macro:", b"undefined", b"select font ", b"the letter ",
                b"the character ", b"begin-group character ",
                b"end-group character ", b"math shift character ",
                b"alignment tab character ", b"macro parameter character ",
                b"superscript character ", b"subscript character ", b"blank space ",
                b"end of alignment template", b"outer endtemplate", b"[unknown",
                b"long macro:", b"protected macro:", b"outer macro:",
                b"protected long macro:", b"long outer macro:",
                b"protected long outer macro:", b"protected outer macro:")
_VALUE_NUM = re.compile(rb"^-?[0-9.]")
# Name of the null control sequence as TeX prints it (`print_cs(null_cs)`):
# esc + "csname" + esc + "endcsname"; with no escape character both are bare.
NULL_CS = b""


def _value_like(rest: bytes, esc: int) -> bool:
    """Could `rest` be the printed value of a trace record? Under a negative
    escape character a primitive meaning prints bare (`relax`), so every
    remainder could be one."""
    if not 0 <= esc <= 255:
        return True
    if rest == b"" or _VALUE_NUM.match(rest) or rest[:1] == bytes([esc]):
        return True
    return rest.startswith(_VALUE_WORDS)


def _printed_names(dec: bytes, esc: int) -> list:
    """(kind, name) readings of one printed name (already ^^-decoded)."""
    out = []
    if 0 <= esc <= 255:
        e = bytes([esc])
        if dec == e + b"csname" + e + b"endcsname":
            out.append(("cs", NULL_CS))
        if dec.startswith(e) and len(dec) > 1:
            out.append(("cs", dec[1:]))
        elif len(dec) == 1:
            out.append(("active", dec))
        else:
            # printed with a different escape than we track: keep the
            # whole string as a candidate name (the dump settles it).
            out.append(("cs", dec))
    else:
        if dec == b"csnameendcsname":
            out.append(("cs", NULL_CS))
        out.append(("cs", dec))
        if len(dec) == 1:
            out.append(("active", dec))
    return out


def _same_value(a: bytes, b: bytes) -> bool:
    """Two printed trace values (backslashes removed) that can be the same
    value: equal, or equal up to where TeX truncated one with `ETC.` (the
    truncation point moves with the escape character, so a value printed
    under \\escapechar=-1 is truncated later than the same value under 92)."""
    if a == b:
        return True
    ta, tb = a.endswith(b"ETC."), b.endswith(b"ETC.")
    if ta:
        a = a[:-4]
    if tb:
        b = b[:-4]
    if ta and tb:
        return a.startswith(b) or b.startswith(a)
    if ta:
        return b.startswith(a)
    if tb:
        return a.startswith(b)
    return False


def parse_trace(log: bytes):
    """Parse a \\tracingassigns/\\tracingrestores log.

    Returns a dict:
      names      {(kind, name_bytes): segment}, kind is "cs" or "active"; the
                 segment is the index of the last LPSEG marker before the
                 assignment whose value the name holds at the end of the trace:
                 `into`/`reassigning` set it; `changing` (the old value) and
                 `retaining` (a global value kept at a group end) never do; a
                 `restoring` record gives back the segment of the assignment
                 whose value it restores, or SEG_BEFORE_TRACE when that value
                 predates the trace (review defect 4: a local \\def inside a
                 group used to win). The restored value is looked up first in
                 a per-name stack of the values local `into`s replaced, top
                 down, then in the name's history (matched on the printed
                 value). The trace shows no group levels, so two local
                 assignments at ONE level of which the first re-sets the value
                 the level started with are still attributed to that first
                 one: same meaning, only the label can be off.
      ambiguous  set of tuples of cs names: one record whose printed name has
                 several readings (a `=` inside the name, or the null control
                 sequence, which prints like the name `csname\\endcsname`).
                 Every reading is in `names`; the dump settles which exists.
      sure       set of cs names read from a record with exactly one reading
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
    history: dict = {}
    saves: dict = {}
    before: dict = {}
    current: dict = {}
    pending: dict = {}
    skipped: dict = {}
    ambiguous = set()
    sure = set()
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
        # A control symbol named `=` prints as `\\==value`: skip its own `=`.
        start = 2 if body[1:2] == b"=" and 0 <= esc <= 255 and body[:1] == bytes([esc]) else 0
        eqs = [i for i in range(start, len(body)) if body[i:i + 1] == b"="]
        if not eqs:
            unparsed += 1
            continue
        # The first `=` is always a reading (a token-list parameter's value
        # can start with anything); every later `=` whose remainder reads as a
        # value is another.
        splits = eqs[:1] + [i for i in eqs[1:] if _value_like(body[i + 1:], esc)]
        first_printed = decode_carets(body[:splits[0]])
        value = body[splits[0] + 1:]

        # escapechar bookkeeping: the "into" record is printed with the NEW
        # escape character, so match the bare name with any one-byte prefix.
        def is_param(x, dec=first_printed):
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
        if first_printed == b"current font":
            continue
        cands = []
        for i in splits:
            for kn in _printed_names(decode_carets(body[:i]), esc):
                if kn[0] == "cs" and _QUANTITY.fullmatch(kn[1]):
                    continue
                if kn not in [c[0] for c in cands]:
                    cands.append((kn, body[i + 1:]))
        cs_names = tuple(dict.fromkeys(nm for (k, nm), _ in cands if k == "cs"))
        if len(cs_names) > 1:
            ambiguous.add(cs_names)
        elif len(cs_names) == 1:
            sure.add(cs_names[0])
        # Values are compared without backslashes: a value printed while
        # \\escapechar=-1 is the same value printed bare.
        cands = [(key, val.replace(b"\\", b"")) for key, val in cands]
        keys = tuple(key for key, _ in cands)
        skip = set()
        if len(cands) > 1:
            # An ambiguous record (a one-byte name under \\escapechar=-1 is
            # the active character or the control symbol): a reading whose
            # known value is not the `changing` record's old value is not the
            # one being assigned, so the `into` that follows skips it.
            if verb == b"changing":
                excl = {k for k, v in cands if k in current and not _same_value(current[k], v)}
                pending[keys] = excl if len(excl) < len(cands) else set()
            elif verb in (b"into", b"reassigning"):
                skip = pending.pop(keys, set())
                skipped[keys] = skip
            elif verb == b"restoring":
                # ... and neither is the group end that undoes that `into`.
                skip = skipped.pop(keys, set())
        glob = m.group(1) is not None
        for key, val in cands:
            if key in skip:
                continue
            if verb in (b"into", b"reassigning"):
                prior = before.pop(key, None)
                if verb == b"into" and not glob:
                    # A local assignment: TeX may save the value it replaces
                    # for the group end to restore. `reassigning` saves
                    # nothing (e-TeX returns before eq_save), nor does a
                    # global one.
                    saves.setdefault(key, []).append(
                        prior or (current.get(key), names.get(key, SEG_BEFORE_TRACE)))
                names[key] = seg
                current[key] = val
                history.setdefault(key, []).append((val, seg))
            elif verb == b"restoring":
                # The value restored is one a local assignment replaced: the
                # innermost saved entry holding it (review LOW item a: the
                # last history entry with that printed value could be the
                # in-group assignment itself, when it re-set the same value).
                stack = saves.get(key) or []
                hit = None
                while stack:
                    v, sg = stack.pop()
                    if v is not None and _same_value(v, val):
                        hit = sg
                        break
                back = [sg for v, sg in history.get(key, []) if _same_value(v, val)]
                if hit is not None:
                    names[key] = hit
                    current[key] = val
                elif back:
                    names[key] = back[-1]
                    current[key] = val
                elif len(cands) == 1:
                    names[key] = SEG_BEFORE_TRACE
                    current[key] = val
                else:
                    # An ambiguous record restoring a value this reading
                    # never had: this reading's value is now unknown.
                    names.setdefault(key, SEG_BEFORE_TRACE)
                    current.pop(key, None)
            else:  # changing, retaining: not the assignment of the kept value
                if verb == b"changing":
                    # the value (and its segment) the `into` that follows
                    # replaces
                    before[key] = (val, names[key] if key in names else SEG_BEFORE_TRACE)
                elif saves.get(key):
                    # a group end keeping a global value drops its save entry
                    saves[key].pop()
                names.setdefault(key, seg)
                current.setdefault(key, val)
    return {"names": names, "ambiguous": ambiguous, "sure": sure,
            "records": records, "tracing_toggles": toggles,
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
        return {"kind": "Primitive", "primitive": name_str(_unmark(r.group(1)))}
    return {"kind": "Other", "meaning": name_str(m)}


def _unmark(prim: bytes) -> bytes:
    """e-TeX prints the mark primitives with a trailing colon (`\\topmark:`,
    the class-0 form of `\\topmarks`); the primitive's name has none."""
    return prim[:-1] if prim.endswith(b":") and len(prim) > 1 else prim


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
        # `\\topmark:` names the primitive `topmark` (review defect 1a).
        out.add(decode_carets(m.group(1)))
        out.add(decode_carets(_unmark(m.group(1))))
    # A font identifier's meaning names its font (`select font nullfont`);
    # for \\nullfont that name is the identifier itself (review defect 1b).
    m = _FONT.match(meaning)
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
# The TeX runner: a client of the one oracle (_oracle.py), never its own engine
# ---------------------------------------------------------------------------

def read_image(repo: Path) -> str:
    text = (repo / WORKFLOW).read_text(encoding="utf-8")
    m = re.search(r"^\s*TEX_IMAGE:\s*(\S+)\s*$", text, re.M)
    if not m or "@sha256:" not in m.group(1):
        raise SystemExit("gen_contract: no digest-pinned TEX_IMAGE in %s" % WORKFLOW)
    return m.group(1)


def tex_vars(env: str, td) -> dict:
    """The exact TeX variables of one of the three environments (see
    LOG_WIDTH): the oracle's shared base for work directory `td`, plus the
    documented overrides."""
    out = dict(_oracle.oracle_tex_vars(td), **LOG_WIDTH)
    if env == "grading":
        return out
    if env == "forced":
        return dict(out, **FORCE_DATE)
    if env == "second_date":
        return dict(out, **FORCE_DATE, SOURCE_DATE_EPOCH=SECOND_EPOCH)
    raise ValueError(env)


class Tex:
    """The generator's TeX runner: a CLIENT of the one oracle (ADR-012
    decision 7, OPEN-118). Every TeX job -- the pdflatex runs, the INITEX
    (`pdftex -ini`) kernel jobs, the \\meaning dumps, the probes and the
    hash-coverage jobs -- goes through `_oracle.run_engine`, so it runs in the
    oracle's container (or natively inside the pinned image) with the
    oracle's guarantees: a verified tree fingerprint, the rc read inside the
    container, positive proof pdfTeX ran, the free-space floor, pdfTeX's own
    write failures refused. The image's own files (the shipped format, the
    files a configuration read) are read through `_oracle.image_command`.

    Work directories lie under the oracle's work root, which the container
    sees at the same absolute path (colima mounts only $HOME). One invocation
    gets one run directory: `jobs/` holds a fresh directory per job and
    `texmf/` the private TEXMFHOME/TEXMFVAR every job of the invocation
    shares (`_oracle.private_texmf_vars`)."""

    def __init__(self, image: str, work: Path | None = None, oracle=None):
        try:
            self.oracle = oracle or _oracle.get_oracle()
        except _oracle.OracleError as e:
            raise SystemExit("gen_contract: the oracle is unavailable: %s" % e)
        if image != _oracle.IMAGE:
            raise SystemExit("gen_contract: asked for %s but the oracle is %s"
                             % (image, _oracle.IMAGE))
        self.image = image
        if work is None:
            self.base = self.oracle.mkdtemp(prefix="contract-run-")
        else:
            work = Path(work).expanduser().resolve()
            work.mkdir(parents=True, exist_ok=True)
            inside = getattr(self.oracle, "_inside", None)
            if inside is not None and not inside(work):
                raise SystemExit("gen_contract: work dir %s is outside the oracle work "
                                 "root %s, which the container cannot see (set "
                                 "LP_ORACLE_WORKROOT or omit --work)"
                                 % (work, self.oracle.workroot))
            self.base = Path(tempfile.mkdtemp(prefix="contract-run-", dir=work))
        self.host = self.base / "jobs"
        self.texmf = self.base / "texmf"
        self.host.mkdir()
        self.texmf.mkdir()
        # Jobs are numbered under a lock: the pass-history trees run in threads.
        self._lock = threading.Lock()
        self._jobs = 0

    def image_command(self, argv: list, timeout: int = 300) -> tuple:
        """(rc, stdout text, stderr text) of a non-TeX command in the image."""
        try:
            rc, out, err = self.oracle.image_command(argv, timeout=timeout)
        except _oracle.OracleError as e:
            raise SystemExit("gen_contract: INFRASTRUCTURE - %s" % e)
        return rc, out.decode("utf-8", "surrogateescape"), err.decode("utf-8", "replace")

    def is_job_path(self, path: str) -> bool:
        """A file of this invocation's own jobs (job.tex, .aux, ...)."""
        return path.startswith(str(self.host) + "/")

    def stable_path(self, path: str) -> str:
        """`path` with this invocation's private TEXMFHOME/TEXMFVAR directory
        replaced by the fixed token PRIVATE_TEXMF, so that a file read from
        there (a font mktexpk made) is named the same in every invocation and
        the kernel's cached baseline still subtracts it. (Before the generator
        became an oracle client these trees were the fixed container paths
        /tmp/lp-texmfhome and /tmp/lp-texmfvar; no committed contract reads a
        file from either.)"""
        root = str(self.texmf) + "/"
        return PRIVATE_TEXMF + "/" + path[len(root):] if path.startswith(root) else path

    def job(self, name: str) -> Path:
        """A fresh job directory. Never a reused name: a directory deleted and
        re-created under the same name on the host can reach the container
        stale through the VM mount, and pdflatex then fails to write its log
        (measured: an intermittent rc=1 with no log, in a loop that reused
        one name)."""
        with self._lock:
            self._jobs += 1
            d = self.host / ("%s-%d" % (name, self._jobs))
        d.mkdir(parents=True)
        return d

    def run(self, jobdir: Path, engine: str, args: list, timeout: int,
            env: str = "forced") -> tuple:
        """One `engine` run with `args` in jobdir through the oracle, under
        the TeX variables of `env` (tex_vars). Returns (rc, seconds); rc
        TIMEOUT_RC = timed out. An oracle failure is never a TeX outcome: it
        stops the generator."""
        t0 = time.monotonic()
        try:
            rc, _, timed_out = self.oracle.run_engine(
                jobdir, engine, args, tex_vars(env, self.texmf), timeout)
        except _oracle.OracleError as e:
            raise SystemExit("gen_contract: INFRASTRUCTURE - %s (job %s)"
                             % (e, jobdir.name))
        return (TIMEOUT_RC if timed_out else rc), time.monotonic() - t0

    def pdflatex(self, jobdir: Path, tex: bytes, *, halt: bool = True,
                 recorder: bool = False, timeout: int = LONG_TIMEOUT,
                 env: str = "forced", jobname: str = JOBNAME) -> dict:
        """One pdflatex run of `tex` (written as job.tex) in jobdir. The job
        name is `job` unless `jobname` says otherwise (the jobname-dependence
        check); every output file is named after it."""
        (jobdir / "job.tex").write_bytes(tex)
        args = ["-interaction=nonstopmode"]
        if halt:
            args.append("-halt-on-error")
        if recorder:
            args.append("-recorder")
        if jobname != JOBNAME:
            args.append("-jobname=" + jobname)
        args.append("job.tex")
        rc, secs = self.run(jobdir, _oracle.ENGINE_PDFLATEX, args, timeout, env)
        logp, flsp = jobdir / (jobname + ".log"), jobdir / (jobname + ".fls")
        if not logp.exists() and rc != TIMEOUT_RC:
            # pdflatex always writes a log; no log means docker or the
            # container failed, which must never read as a TeX outcome.
            raise SystemExit("gen_contract: INFRASTRUCTURE - pdflatex wrote no log "
                             "in %s (rc=%d)" % (jobdir.name, rc))
        log = logp.read_bytes() if logp.exists() else b""
        fls = flsp.read_bytes() if flsp.exists() else b""
        return {"rc": rc, "secs": secs, "log": log, "fls": fls,
                "pdf": (jobdir / (jobname + ".pdf")).exists(),
                "tex_sha256": sha256_bytes(tex)}

    def fixpoint(self, jobdir: Path, tex: bytes, *, env: str = "grading",
                 recorder: bool = True, timeout: int = LONG_TIMEOUT) -> dict:
        """The oracle's pass protocol, `diff_real_roots.run_to_fixpoint`, in
        the container: run until the first rc 0 (at most MAX_PASSES runs),
        then ONE confirming run in the same directory; the result is the last
        run's. A document that succeeds and then breaks itself through a file
        its own first pass wrote is caught by the confirming run (review
        defect R1.2: the load run used to be a single pass). The first
        pass's .fls and log are kept alongside."""
        first = res = None
        passes = 0
        for _ in range(MAX_PASSES):
            res = self.pdflatex(jobdir, tex, recorder=recorder, timeout=timeout, env=env)
            passes += 1
            first = first or res
            if res["rc"] in (0, TIMEOUT_RC):
                break
        if res["rc"] == 0:
            res = self.pdflatex(jobdir, tex, recorder=recorder, timeout=timeout, env=env)
            passes += 1
        out = dict(res)
        out.update({"passes": passes, "first_fls": first["fls"],
                    "first_log": first["log"], "first_rc": first["rc"]})
        return out

    def close(self):
        # The oracle's container is long-lived and shared: only this
        # invocation's run directory is removed.
        if os.environ.get("LP_CONTRACT_KEEP_WORK") != "1":
            shutil.rmtree(self.base, ignore_errors=True)

    def __enter__(self):
        return self

    def __exit__(self, *a):
        self.close()


# ---------------------------------------------------------------------------
# The engine's own name lists: format string pools, primitives, TeX's hash count
# ---------------------------------------------------------------------------

def fmt_pool_strings(data: bytes) -> list:
    """Every string of a web2c TeX format's string pool, in pool order.

    A format dumps (web2c tex.ch, `Dump constants for consistency check` and
    `Dump the string pool`, big-endian): the magic "W2TX", the engine name,
    engine-specific constants, then pool_ptr, str_ptr, str_start[0..str_ptr]
    and the pool bytes. Every multiletter control-sequence name in the
    format's hash table IS one of these strings (`id_lookup` makes the name a
    pool string), so the pool is a superset of the format's names by
    construction. The offset of pool_ptr depends on the engine's constants,
    so it is searched for, and accepted only where the whole structure
    checks: str_start[0] = 0, non-decreasing, str_start[str_ptr] = pool_ptr,
    and strings 0..255 are TeX's printable forms of the 256 characters."""
    if data[:2] == b"\x1f\x8b":
        data = gzip.decompress(data)
    if data[:4] != b"W2TX":
        raise ValueError("not a web2c format (no W2TX magic)")
    for off in range(8, min(len(data) - 8, 16384), 4):
        pool_ptr, str_ptr = struct.unpack_from(">ii", data, off)
        if not (256 < str_ptr < 10 ** 7 and 0 < pool_ptr < 10 ** 9):
            continue
        base = off + 8
        pool_at = base + 4 * (str_ptr + 1)
        if pool_at + pool_ptr > len(data):
            continue
        if struct.unpack_from(">i", data, base)[0] != 0:
            continue
        if struct.unpack_from(">i", data, base + 4 * str_ptr)[0] != pool_ptr:
            continue
        ss = struct.unpack_from(">%di" % (str_ptr + 1), data, base)
        if any(ss[i] > ss[i + 1] for i in range(str_ptr)):
            continue
        pool = data[pool_at:pool_at + pool_ptr]
        strs = [pool[ss[i]:ss[i + 1]] for i in range(str_ptr)]
        if all(decode_carets(strs[k]) == bytes([k]) for k in range(256)):
            return strs
    raise ValueError("no string pool found in the format")


_CS_COUNT = re.compile(rb"(\d+) multiletter control sequences")


def cs_count(log: bytes):
    """TeX's `cs_count` as printed in the log's statistics (at the end of a
    job run with \\tracingstats>0, and by \\dump): the number of multiletter
    control sequences in the hash table."""
    m = _CS_COUNT.findall(log)
    return int(m[-1]) if m else None


# Candidate names harvested from a TeX source file. A name token is `\\`
# followed by letters, and which bytes are letters is the catcode table at
# that point, which a file can change (`@`, expl3's `_` and `:`, pdfescape's
# `!`, ...). So after every `\\`, take the run R of bytes that are not
# white space, `\\`, a brace or `%` (at most 80), and every R[:j] where j is
# the position of a byte that is not an ASCII letter (the name ends at the
# first non-letter, whichever that is) or the end of R. An over-approximation
# on purpose: a candidate that is not a name costs one `\\ifcsname`, and
# hash_coverage says whether anything was still missed (measured: letters,
# `@`, `_` and `:` alone missed `\\Gin@rule@*` and `\\!!stringa` in the
# five-package configuration).
_TOK_RUN = re.compile(rb"\\([^\s\\{}%]{1,80})")


def source_names(data: bytes) -> set:
    out = set()
    for m in _TOK_RUN.finditer(data):
        run = m.group(1)
        for j, c in enumerate(run):
            if not (65 <= c <= 90 or 97 <= c <= 122):
                if j >= 2:
                    out.add(run[:j])
        if len(run) >= 2:
            out.add(run)
    return out


# `\csname <text>\endcsname` as a job writes it into its own files (an .aux
# line such as `\expandafter\gdef\csname lpq7\endcsname{}`): the text is a
# name that is no `\`-token.
_CSNAME_LIT = re.compile(rb"\\csname *([^\\{}%\r\n]{1,200})\\endcsname")
# Files a job leaves that are not written by the document: the source, the
# log, the recorder file and the PDF.
_NOT_JOB_WRITTEN = {".tex", ".log", ".fls", ".pdf"}


def job_written_names(jobdir: Path) -> set:
    """Candidate names from the files the job itself wrote (.aux, .out, ...):
    their name tokens and `\\csname` literals. A name that a later pass
    creates by reading one of them (`\\newlabel{LastPage}` builds
    `\\r@LastPage`) is often neither; the later-pass trace and the last
    pass's hash count are what see those (review defect 1)."""
    out = set()
    for f in sorted(jobdir.iterdir()):
        if not f.is_file() or f.suffix in _NOT_JOB_WRITTEN or f.name == "mount_probe":
            continue
        data = f.read_bytes()
        out |= source_names(data)
        out |= set(_CSNAME_LIT.findall(data))
    return out


def engine_primitives(tex: Tex) -> dict:
    """The engine's primitives, derived from the engine alone.

    A virgin INITEX run (`pdftex -ini -etex -translate-file=cp227.tcx`, the
    fmtutil flags of pdflatex, and nothing read) dumps a format whose hash
    table holds exactly the primitives. Its string pool (the engine's
    compiled-in pool plus nothing) gives the candidates; a second virgin
    INITEX run tests each with `\\ifcsname` and dumps its `\\meaning`, plus
    all 256 one-character names and the null name. COMPLETE BECAUSE: the
    number of multiletter candidates found defined must equal the virgin
    dump's own count of multiletter control sequences (TeX's cs_count), and
    the one-character names are enumerated exhaustively."""
    jd = tex.job("virgin")
    initex = _oracle.ENGINE_PDFTEX
    ini = ["-ini", "-etex", "-interaction=nonstopmode", "-translate-file=cp227.tcx"]
    rc, _ = tex.run(jd, initex, ini + ["-jobname=lpvirgin", "\\dump"], LONG_TIMEOUT)
    log = (jd / "lpvirgin.log").read_bytes() if (jd / "lpvirgin.log").exists() else b""
    if rc != 0 or not (jd / "lpvirgin.fmt").exists():
        raise SystemExit("gen_contract: virgin INITEX dump failed: rc=%d" % rc)
    count = cs_count(log)
    pool = fmt_pool_strings((jd / "lpvirgin.fmt").read_bytes())
    cands = sorted({x for x in pool if len(x) >= 2}) + [bytes([b]) for b in range(256)] \
        + [NULL_CS]
    block, unw = dump_block(cands, actives=False, u8_sweep=False)
    # Virgin INITEX has no brace characters; the catcode line needs them.
    (jd / "prim.tex").write_bytes(b"\\catcode123=1 \\catcode125=2 \\relax\n" + block +
                                  b"\\end\n")
    rc2, _ = tex.run(jd, initex, ini + ["-jobname=lpprim", "prim.tex"], LONG_TIMEOUT)
    d = parse_dump((jd / "lpprim.log").read_bytes())
    shutil.rmtree(jd, ignore_errors=True)
    if rc2 != 0 or d["error"] is not None or unw:
        raise SystemExit("gen_contract: virgin INITEX primitive dump failed: rc=%d %s %s"
                         % (rc2, d["error"], unw[:3]))
    prims = {}
    for i, nm in enumerate(cands):
        m = d["meanings"].get(i)
        if m is not None:
            prims[nm] = m
    multi = sorted(n for n in prims if len(n) >= 2)
    single = sorted(n for n in prims if len(n) < 2)
    not_self = sorted(name_str(n) for n, m in prims.items()
                      if classify_meaning(n, m)["kind"] not in ("Primitive", "Relax", "Font"))
    reasons = []
    if count is None or len(multi) != count:
        reasons.append("virgin INITEX: %d multiletter primitives found, TeX counts %s"
                       % (len(multi), count))
    if not_self:
        reasons.append("virgin INITEX names that are not primitives: %s" % not_self[:5])
    return {"names": multi + single, "multiletter": len(multi),
            "single": [name_str(n) for n in single], "tex_cs_count": count,
            "pool_strings": len(pool), "complete": not reasons, "reasons": reasons}


def hash_coverage(tex: Tex, jobname: str, prefix: bytes, universe, *,
                  env: str = "forced", seed_dir: Path | None = None,
                  tex_jobname: str = JOBNAME) -> dict:
    """Does `universe` hold every multiletter name in TeX's hash table at the
    point `prefix` leaves a job in? Answered by TeX's own counter, so the
    answer does not depend on how `universe` was built.

    Job A is prefix + the dump regime + stop. Job B is the same with a
    `\\csname` of every name of universe in between (inside groups, so
    nothing survives): `\\csname` enters a name the table does not hold yet
    and leaves one it holds alone. Both end with \\tracingstats=1, whose
    statistics print cs_count. So count(B) - count(A) is the number of
    universe names NOT in the table, universe minus that is the number of
    table entries universe covers, and count(A) minus the covered number is
    the number of table entries universe MISSES. 0 means complete; anything
    else is incompleteness nobody listed, which is exactly what a check
    built from the generator's own lists cannot see.

    `seed_dir`: a job directory whose job-written files (.aux, .out, ...)
    are copied into both jobs first, so the count is taken on the pass that
    reads them (review defect 1: a name created from the .aux on pass 2 was
    outside a pass-1 count). The count therefore describes the pass AFTER
    the one that wrote seed_dir's files; `tex_jobname` must be the job name
    they were written under."""
    ml = sorted({n for n in universe if len(n) >= 2})
    head = prefix + b"\\tracingstats=1\\relax\n" + regime_open()

    def body(names):
        out = [head]
        unw = []
        for i, nm in enumerate(names):
            if i % 500 == 0:
                out.append(ESC + b"begingroup\n")
            line = _name_line(nm, lambda n: _w(
                ESC, b"expandafter", ESC, b"ifx", ESC, b"csname", SPACER, n,
                ESC, b"endcsname", ESC, b"relax", ESC, b"fi\n"))
            if line is None:
                unw.append(nm)
            else:
                out.append(line)
            if i % 500 == 499:
                out.append(ESC + b"endgroup\n")
        if len(names) % 500:
            out.append(ESC + b"endgroup\n")
        out.append(regime_close() + FMT_STOP)
        return b"".join(out), unw

    def seeded(name):
        jd = tex.job(name)
        _copy_job_files(seed_dir, jd)
        return jd

    ta, _ = body([])
    tb, unw = body(ml)
    ra = tex.pdflatex(seeded(jobname + "_a"), ta, env=env, jobname=tex_jobname)
    rb = tex.pdflatex(seeded(jobname + "_b"), tb, env=env, jobname=tex_jobname)
    ka, kb = cs_count(ra["log"]), cs_count(rb["log"])
    ea, eb = first_error(ra["log"]), first_error(rb["log"])
    out = {"universe_multiletter": len(ml), "unwritable": len(unw)}
    if ra["rc"] != 0 or rb["rc"] != 0 or ea or eb or ka is None or kb is None:
        out["error"] = "coverage jobs failed: rc=%d/%d %s %s" % (ra["rc"], rb["rc"], ea, eb)
        return out
    covered = len(ml) - len(unw) - (kb - ka)
    out.update({"hash_entries": ka, "covered": covered, "uncovered": ka - covered})
    return out


# ---------------------------------------------------------------------------
# Pin and kernel
# ---------------------------------------------------------------------------

def get_pin(tex: Tex, image: str) -> dict:
    """The pin, from the oracle's own VERIFIED tree fingerprint (banner, arch,
    format and tlpdb hashes, TEXMFROOT; `_oracle.tree_fingerprint`) plus the
    format's path, which the kernel job copies."""
    try:
        fp = tex.oracle.fingerprint()
    except _oracle.OracleError as e:
        raise SystemExit("gen_contract: cannot read the pin: %s" % e)
    rc, out, err = tex.image_command(["kpsewhich", "-engine=pdftex", "pdflatex.fmt"])
    fmt_path = out.strip()
    if rc != 0 or not fmt_path or not fp.get("fmt_sha256"):
        raise SystemExit("gen_contract: cannot read the pin: %s %s" % (out, err))
    return {"image": image, "arch": fp["arch"], "engine_banner": fp["banner"],
            "fmt_path": fmt_path, "fmt_sha256": fp["fmt_sha256"],
            "texmf_root": fp["texmfroot"], "tlpdb_sha256": fp["tlpdb_sha256"]}


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
                   u8_sweep=False, recorder=False, env="forced",
                   tex_jobname: str = JOBNAME) -> tuple:
    block, unw = dump_block(names, actives=actives, u8_sweep=u8_sweep)
    res = tex.pdflatex(tex.job(jobname), block + FMT_STOP, recorder=recorder, env=env,
                       jobname=tex_jobname)
    d = parse_dump(res["log"])
    if res["rc"] != 0 or d["error"] is not None:
        raise SystemExit("gen_contract: format-state dump %s failed: rc=%d %s" %
                         (jobname, res["rc"], d["error"]))
    return d, unw, res


# The INITEX run intercepts latex.ltx's final \dump to replay \everyjob under
# the same tracing first: \everyjob runs at the start of every job, before a
# job's first line, so names it assigns (l3's c_sys_* constants, the
# sys_if_shell conditionals it builds with \csname) are assigned in no trace a
# job can take. The replay is a candidate source only; membership still comes
# from the shipped format.
# (Virgin INITEX has no brace characters, so the prefix makes them braces for
# its \\def and gives them back: latex.ltx refuses to start if `{` is a brace.)
INITEX_PREFIX = ("\\catcode123=1 \\catcode125=2 "
                 "\\tracingassigns=1 \\tracingrestores=1 \\tracingonline=0 "
                 "\\let\\lprealdump\\dump \\def\\dump{\\nonstopmode"
                 "\\immediate\\write-1{LPSEG:1}\\the\\everyjob\\lprealdump}"
                 "\\catcode123=12 \\catcode125=12 ")


def build_kernel(tex: Tex, pin: dict, report: dict, *, drop=()) -> dict:
    """The kernel closed world: every name defined in format state (a job's
    state after \\everyjob), with its meaning.

    Candidates, from four independent sources: every string of the shipped
    pdflatex.fmt's string pool (a superset of its hash table, see
    fmt_pool_strings); the engine's primitives (engine_primitives); every
    name the INITEX run of pdflatex.ini and its \\everyjob replay assigns;
    all 256 one-character names and the null name. Each is dumped with
    \\meaning in format state, then every name referenced from a dumped
    meaning, until no new name appears. The defined ones are the kernel.

    COMPLETE BECAUSE hash_coverage, TeX's own count of the hash table in
    format state, must find 0 entries outside the candidates. `drop` removes
    names from the candidates (the kill-test of that check)."""
    t0 = time.monotonic()
    reasons = []
    prim = engine_primitives(tex)
    if not prim["complete"]:
        reasons += prim["reasons"]
    report["engine_primitives"] = prim["multiletter"] + len(prim["single"])

    jd = tex.job("kernel_initex")
    rc, secs = tex.run(jd, _oracle.ENGINE_PDFTEX,
                       ["-ini", "-etex", "-interaction=nonstopmode",
                        "-jobname=lpkernel", "-progname=pdflatex",
                        "-translate-file=cp227.tcx",
                        INITEX_PREFIX + "\\input pdflatex.ini"], LONG_TIMEOUT)
    log = (jd / "lpkernel.log").read_bytes()
    tr = parse_trace(log)
    if rc != 0 or tr["first_error"] is not None:
        raise SystemExit("gen_contract: INITEX of pdflatex.ini failed: rc=%d %s" %
                         (rc, tr["first_error"]))
    banners = format_banners(log)
    report["kernel_initex_secs"] = round(secs, 1)
    report["kernel_trace_records"] = tr["records"]
    shutil.rmtree(jd)
    initex = {nm for (kind, nm) in tr["names"] if kind == "cs"}
    everyjob = {nm for (kind, nm), seg in tr["names"].items() if kind == "cs" and seg == 1}

    jd = tex.job("kernel_fmt")
    rc, _, err = tex.image_command(["cp", pin["fmt_path"], str(jd / "shipped.fmt")])
    if rc != 0:
        raise SystemExit("gen_contract: cannot copy the format: %s" % err)
    fmt_bytes = (jd / "shipped.fmt").read_bytes()
    if sha256_bytes(fmt_bytes) != pin["fmt_sha256"]:
        raise SystemExit("gen_contract: the copied format is not the pinned one")
    pool = set(fmt_pool_strings(fmt_bytes))
    shutil.rmtree(jd)

    singles = {bytes([b]) for b in range(256)} | {NULL_CS}
    universe = (pool | initex | set(prim["names"]) | singles) - set(drop)
    report["kernel_universe"] = len(universe)
    meanings: dict = {}
    unwritable: set = set()
    todo = sorted(universe)
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
        todo = sorted(n for n in new - set(drop) if n not in meanings and n not in unwritable)
    if todo:
        reasons.append("referenced-name closure did not converge in 6 rounds")
    if unwritable:
        reasons.append("%d kernel candidates could not be written into the dump"
                       % len(unwritable))
    d1, res1 = base
    _, fls_inputs = parse_fls(res1["fls"])
    universe = sorted(meanings)

    cov = hash_coverage(tex, "kernel_cov", b"", universe)
    if cov.get("error"):
        reasons.append("kernel " + cov["error"])
    elif cov["uncovered"] != 0:
        reasons.append("TeX's hash table in format state holds %d names outside the "
                       "kernel's candidates" % cov["uncovered"])

    # Names whose format-state meaning depends on the date (\everyjob's
    # c_sys_* constants): dumped again under a second forced date.
    d2, _, _ = fmt_state_dump(tex, "kernel_date2", universe, env="second_date")
    date_dep = sorted(nm for i, nm in enumerate(universe)
                      if d2["meanings"].get(i) != meanings.get(nm))
    # ... and whose format-state meaning holds the job name (review LOW item
    # b): dumped again under a second job name.
    dj, _, _ = fmt_state_dump(tex, "kernel_jobname2", universe,
                              tex_jobname=SECOND_JOBNAME)
    job_dep = sorted(nm for i, nm in enumerate(universe)
                     if dj["meanings"].get(i) != meanings.get(nm))

    defined = {nm: m for nm, m in meanings.items() if m is not None}
    prim_names = set(prim["names"])
    report["kernel_dump_rounds"] = rounds
    report["kernel_secs"] = round(time.monotonic() - t0, 1)
    return {
        "fmt_sha256": pin["fmt_sha256"],
        "banners": banners,
        "initex_names": len(initex),
        "names": {name_str(k): name_str(v) for k, v in defined.items()},
        "universe": [name_str(x) for x in universe],
        "actives": {str(b): name_str(m) for b, m in d1["actives"].items()},
        "catcodes": d1["catcodes"],
        "baseline_inputs": [tex.stable_path(p) for p in fls_inputs if p.startswith("/")],
        "unwritable": sorted(name_str(x) for x in unwritable),
        "dump_rounds": rounds,
        "trace_unparsed": tr["unparsed"],
        "sources": {"fmt_pool_strings": len(pool), "initex_traced": len(initex),
                    "everyjob_replay": len(everyjob),
                    "engine_primitives": len(prim_names),
                    "one_character_and_null": len(singles),
                    "universe": len(universe)},
        "everyjob_names": sorted(name_str(x) for x in everyjob if x in defined),
        "primitives": {"names": sorted(name_str(x) for x in prim_names),
                       "multiletter": prim["multiletter"],
                       "tex_cs_count": prim["tex_cs_count"],
                       "virgin_pool_strings": prim["pool_strings"],
                       "complete": prim["complete"],
                       "undefined_in_format": sorted(name_str(x) for x in prim_names
                                                     if x not in defined)},
        "coverage": cov,
        "date_dependent_names": [name_str(x) for x in date_dep],
        "jobname": JOBNAME,
        "jobname_dependent_names": [name_str(x) for x in job_dep],
        "complete": not reasons,
        "incomplete_reasons": reasons,
    }


def generator_sha256() -> str:
    """sha256 of this file. Keys the LOCAL kernel cache only (a behaviour
    change cannot reuse a stale kernel, review defect R1.5); it is never
    written into a committed file, where it would make a comment edit
    invalidate every contract (the C-68 lesson)."""
    return sha256_bytes(Path(__file__).read_bytes())


def load_kernel(tex: Tex, pin: dict, cache: Path, fresh: bool, report: dict) -> dict:
    cache.mkdir(parents=True, exist_ok=True)
    gsha = generator_sha256()
    path = cache / ("kernel-%s-%s.json" % (pin["fmt_sha256"], gsha[:16]))
    if path.exists() and not fresh:
        k = json.loads(path.read_text(encoding="utf-8"))
        if k.get("generator_sha256") == gsha:
            report["kernel_cache"] = "hit"
            return k
    report["kernel_cache"] = "miss"
    k = build_kernel(tex, pin, report)
    k["generator_version"] = GENERATOR_VERSION
    k["generator_sha256"] = gsha
    tmp = path.with_suffix(".tmp")
    tmp.write_text(json.dumps(k, ensure_ascii=False, sort_keys=True), encoding="utf-8")
    tmp.replace(path)
    return k


def kernel_public(kernel: dict, pin: dict) -> dict:
    """The committed kernel file: names and their meaning kinds (no bodies),
    and the evidence that the name set is complete."""
    names = {}
    for n, m in kernel["names"].items():
        nb = name_bytes(n)
        names[n] = short_kind(classify_meaning(nb, name_bytes(m)))
    digest = sha256_bytes("\n".join("%s\t%s" % (n, kernel["names"][n])
                                    for n in sorted(kernel["names"])).encode("utf-8"))
    return {"schema": KERNEL_SCHEMA, "generator_version": GENERATOR_VERSION,
            "pin": {k: pin[k] for k in ("image", "arch", "engine_banner", "fmt_sha256")},
            "banners": kernel["banners"],
            "method": "candidates = every string of the shipped pdflatex.fmt's string "
                      "pool, every engine primitive (virgin INITEX), every name the "
                      "INITEX run of pdflatex.ini and its \\everyjob replay assigns, "
                      "every one-character name and the null name; each dumped with "
                      "\\meaning in format state (a job after \\everyjob), then every "
                      "name referenced from a dumped meaning until no new name "
                      "appears; the defined ones. Completeness: TeX's own count of "
                      "its hash table in format state finds 0 names outside the "
                      "candidates (coverage.uncovered)",
            "initex_traced_names": kernel["initex_names"],
            "dump_rounds": kernel["dump_rounds"],
            "unwritable_names": kernel["unwritable"],
            "candidate_sources": kernel["sources"],
            "coverage": kernel["coverage"],
            "primitives": kernel["primitives"],
            "everyjob_names": kernel["everyjob_names"],
            "date_dependent_names": kernel["date_dependent_names"],
            "jobname": kernel["jobname"],
            "jobname_dependent_names": kernel["jobname_dependent_names"],
            "complete": kernel["complete"],
            "incomplete_reasons": kernel["incomplete_reasons"],
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
    listing = tex.base / "hash_list.txt"
    listing.write_text("\n".join(paths) + "\n", encoding="utf-8")
    _, stdout, _ = tex.image_command(["xargs", "-d", "\\n", "-a", str(listing),
                                      "sha256sum"])
    out = {}
    for line in stdout.splitlines():
        h, _, p = line.partition("  ")
        out[p] = h
    missing = [p for p in paths if p not in out]
    if missing:
        raise SystemExit("gen_contract: could not hash %s" % missing[:5])
    return out


def read_files(tex: Tex, paths: list) -> dict:
    """{path: bytes} of files inside the image (through a tar in the work dir)."""
    if not paths:
        return {}
    (tex.base / "read_list.txt").write_text("\n".join(paths) + "\n", encoding="utf-8")
    rc, _, err = tex.image_command(["tar", "-cf", str(tex.base / "read.tar"), "-P", "-T",
                                    str(tex.base / "read_list.txt")], timeout=300)
    if rc != 0:
        raise SystemExit("gen_contract: cannot read files: %s" % err)
    out = {}
    with tarfile.open(tex.base / "read.tar") as t:
        for m in t.getmembers():
            if m.isfile():
                out[m.name] = t.extractfile(m).read()
    (tex.base / "read.tar").unlink()
    return out


def _dump_state(d: dict, names: list) -> dict:
    """The comparable part of a body-start dump."""
    return {"meanings": {nm: d["meanings"].get(i) for i, nm in enumerate(names)},
            "actives": d["actives"], "catcodes": d["catcodes"], "u8": d["u8"]}


def _state_diff(a: dict, b: dict, ignore=frozenset()) -> tuple:
    """(membership, meaning_only) differences between two body-start dumps:
    names defined in one and not the other (plus any active-character,
    catcode or u8 difference), and names defined in both with different
    meanings."""
    member, meaning = [], []
    for n, m in a["meanings"].items():
        if n in ignore:
            continue
        o = b["meanings"].get(n)
        if (m is None) != (o is None):
            member.append(name_str(n))
        elif m != o:
            meaning.append(name_str(n))
    member.sort()
    meaning.sort()
    if a["actives"] != b["actives"]:
        member.append("<active characters>")
    if a["catcodes"] != b["catcodes"]:
        member.append("<catcodes>")
    if a["u8"] != b["u8"]:
        member.append("<u8 sweep>")
    return member, meaning


# The line a FAILING pass of a pass history ends its body with (see
# protocol_histories): after everything the pass is run for, so the pass
# still writes what the configuration writes at \begin{document}, and not
# what it writes at \end{document}.
FAIL_MSG = "lp forced failing pass"
FAIL_LINE = b"\\errmessage{" + FAIL_MSG.encode() + b"}\n"
END_DOC = b"\\end{document}\n"


def protocol_histories(max_passes: int = MAX_PASSES) -> list:
    """Every history of earlier passes that the oracle's pass protocol
    (`Tex.fixpoint`, diff_real_roots.run_to_fixpoint) can run a pass after,
    as a string of S (a pass that completed) and F (a pass that failed),
    shortest first. A pass's state at body start depends only on the files
    earlier passes wrote, so these are all the states the protocol can
    GRADE (review re-review 2, defect 1: the checks covered passes 1 and 2
    only, and pass 3 after F S is graded).

    The protocol runs up to max_passes passes until the first one that
    completes, then one confirming pass: F^j S S for j < max_passes, or
    F^max_passes. The histories are the proper prefixes of those runs:
    for 3, '', F, S, FF, FS, FFS, i.e. passes 1 to max_passes+1."""
    out = set()
    for j in range(max_passes):
        run = "F" * j + "SS"
        out |= {run[:i] for i in range(len(run))}
    run = "F" * max_passes
    out |= {run[:i] for i in range(len(run))}
    return sorted(out, key=lambda h: (len(h), h))


def failing_variant(doc: bytes) -> bytes:
    """`doc` (ending with \\end{document}) failing just before its end."""
    if not doc.endswith(END_DOC):
        raise SystemExit("gen_contract: a pass-history document must end with "
                         "\\end{document}")
    return doc[:-len(END_DOC)] + FAIL_LINE + END_DOC


def _copy_job_files(src: Path | None, dst: Path) -> None:
    """Copy the files a job wrote (.aux, .out, ...) into another job dir."""
    if src is None:
        return
    for f in sorted(src.iterdir()):
        if f.is_file() and f.suffix not in _NOT_JOB_WRITTEN:
            shutil.copyfile(f, dst / f.name)


def hist_label(h: str) -> str:
    return h or "none"


def run_history_tree(tex: Tex, label: str, doc: bytes, histories: list, *,
                     env: str = "forced", jobname: str = JOBNAME,
                     count_prefix: bytes | None = None, universe=None) -> dict:
    """Run `doc` on every pass of the protocol's pass histories, as a tree:
    the pass after history h runs in a fresh directory holding the files the
    passes of h wrote. At each history `doc` itself is run (the S run; its
    log is that pass's log) and, when a longer history needs it, its failing
    variant (the F run). With count_prefix, TeX's hash count (hash_coverage)
    is taken on that pass too, seeded with the same files, so the count is
    labelled with the pass it describes (review re-review 2, defect 2).

    Returns {h: {"pass": len(h)+1, "S": run, "F": run or None, "S_dir",
    "F_dir", "coverage": dict or None}}."""
    hs = set(histories)
    seed: dict = {"": None}
    out: dict = {}
    fail_doc = failing_variant(doc)
    for h in histories:
        if h not in seed:
            raise SystemExit("gen_contract: pass history %r has no parent" % h)
        node = {"pass": len(h) + 1, "F": None, "F_dir": None, "coverage": None}
        for x, d in (("S", doc), ("F", fail_doc)):
            if x == "F" and h + "F" not in hs:
                continue
            jd = tex.job("%s_%s_%s" % (label, hist_label(h), x))
            _copy_job_files(seed[h], jd)
            node[x] = tex.pdflatex(jd, d, env=env, jobname=jobname)
            node[x + "_dir"] = jd
            if h + x in hs:
                seed[h + x] = jd
        if count_prefix is not None:
            node["coverage"] = hash_coverage(
                tex, "%s_cov_%s" % (label, hist_label(h)), count_prefix, universe,
                env=env, seed_dir=seed[h], tex_jobname=jobname)
        out[h] = node
    return out


def generate(cfg: dict, tex: Tex, pin: dict, kernel: dict, use_names: list,
             report: dict, *, universe_filter=None) -> dict:
    """One configuration's contract. `universe_filter`, if given, drops names
    from the dumped universe: the kill-test of the hash-coverage check."""
    cfg = normalize_config(cfg)
    labels = segment_labels(cfg)
    reasons = []
    t0 = time.monotonic()
    pre = preamble_tex(cfg)
    provenance = {"generator_version": GENERATOR_VERSION}
    if not kernel.get("complete"):
        reasons.append("the kernel is incomplete: %s"
                       % "; ".join(kernel.get("incomplete_reasons") or ["unknown"]))

    # R1: the load outcome, attested under the GRADING environment with the
    # oracle's pass protocol. This compile IS the attestation.
    load_doc = pre + b"\\begin{document}\n\\end{document}\n"
    r1 = tex.fixpoint(tex.job("r1_load"), load_doc, env="grading")
    report["r1_secs"] = round(r1["secs"], 2)
    provenance["load_tex_sha256"] = r1["tex_sha256"]
    err1 = first_error(r1["log"])
    # R1f: the same under the forced date; it must agree, and its first pass
    # supplies files_read (deterministic).
    r1f = tex.fixpoint(tex.job("r1f_load"), load_doc, env="forced")
    errf = first_error(r1f["log"])
    ok1 = r1["rc"] == 0 and err1 is None
    if (ok1, err1, r1["passes"]) != (r1f["rc"] == 0 and errf is None, errf, r1f["passes"]):
        reasons.append("date_dependent_load: the grading environment (real clock) gives "
                       "rc=%d %r in %d passes, the forced date rc=%d %r in %d passes"
                       % (r1["rc"], err1, r1["passes"], r1f["rc"], errf, r1f["passes"]))

    # R2: pass 1, the trace, with load-boundary markers.
    trace_tex = (b"\\tracingassigns=1 \\tracingrestores=1 \\tracingonline=0\n" +
                 preamble_tex(cfg, markers=True) +
                 b"\\begin{document}\n\\immediate\\write-1{LPSEG:%d}\n"
                 b"\\tracingassigns=0 \\tracingrestores=0\n\\end{document}\n"
                 % (len(labels)))
    # The trace runs on every pass of the protocol's pass histories (review
    # defect 1, and re-review 2 defect 1: pass 3 after a failing pass 1 is
    # graded), in each of the three environments the body-start state is
    # checked in (R3 below): a name that exists only under the real clock or
    # only under another job name (l3's \csname lookups of
    # `__file_seen_<jobname>.aux:`) must be in the universe too. The
    # contract's pass 1 is the S run of the empty history, forced, `job`.
    histories = protocol_histories()
    envs = [("forced", JOBNAME), ("grading", JOBNAME), ("grading", SECOND_JOBNAME)]
    with ThreadPoolExecutor(max_workers=len(envs)) as ex:
        futs = [ex.submit(run_history_tree, tex, "r2_trace_%s_%s" % (e, j), trace_tex,
                          histories, env=e, jobname=j) for e, j in envs]
        trace_trees = [f.result() for f in futs]
    r2 = trace_trees[0][""]["S"]
    report["r2_secs"] = round(r2["secs"], 2)
    provenance["trace_tex_sha256"] = r2["tex_sha256"]
    provenance["trace_log_sha256"] = sha256_bytes(r2["log"])
    tr = parse_trace(r2["log"])
    report["trace_records"] = tr["records"]

    def seg_label(k):
        if k == SEG_BEFORE_TRACE:
            return "before_trace"
        if k < 0:
            return "before_class"
        return labels[k] if k < len(labels) else "body"

    if not ok1:
        seg = tr["first_error"][0] if tr["first_error"] else None
        if tr["first_error"] is None or tr["first_error"][1] != err1:
            reasons.append("load and trace runs disagree on the fatal error (the "
                           "trace is one pass; the load needed %d)" % r1["passes"])
        load = {"status": "fatal", "rc": r1["rc"], "passes": r1["passes"],
                "first_pass_rc": r1["first_rc"], "message": err1,
                "error_class": ("timeout" if r1["rc"] == TIMEOUT_RC
                                else classify_error(err1 or "")),
                "load_index": seg, "segment": seg_label(seg) if seg is not None else None}
    else:
        load = {"status": "ok", "passes": r1["passes"]}
        if r2["rc"] != 0 or tr["first_error"] is not None:
            reasons.append("trace run failed where the load run succeeded")

    # files_read: the forced run's first-pass .fls minus the empty-job
    # baseline minus job-local files.
    _, inputs = parse_fls(r1f["first_fls"])
    base = set(kernel["baseline_inputs"])
    reads = sorted(p for p in inputs if p.startswith("/") and tex.stable_path(p) not in base
                   and not tex.is_job_path(p))
    hashes = hash_files(tex, reads)
    files_read = [{"path": texmf_rel(tex.stable_path(p), pin["texmf_root"]),
                   "sha256": hashes[p]} for p in reads]
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
        "banners": format_banners(r1f["log"]),
        "load_outcome": load,
        "files_read": files_read,
        "complete_scope": COMPLETE_SCOPE,
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
    # Ours: the first line (segment -1) switches both on; the line after the
    # last marker switches \tracingassigns off (printed as its "changing").
    foreign = [t for t in tr["tracing_toggles"] if not (
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

    # The later passes (review defect 1). The oracle grades the last pass of
    # its protocol, and a later pass reads what earlier ones wrote: a name
    # built from the .aux (\newlabel{LastPage} makes \r@LastPage) exists
    # there and nowhere in pass 1, and is often no token of any file. So
    # every name any pass of any history assigns, and every name token and
    # \csname literal of the files any pass wrote, joins the universe. Only
    # pass 1's trace supplies set_in; TeX's hash count on every pass below is
    # the check that does not depend on any of this.
    written = set()
    later_traced = set()
    for (env, jobname), trace_tree in zip(envs, trace_trees):
        where = "" if (env, jobname) == envs[0] else " (%s, job name %s)" % (env, jobname)
        for h, node in trace_tree.items():
            for x in ("S", "F"):
                rk = node[x]
                if rk is None:
                    continue
                written |= job_written_names(node[x + "_dir"])
                if rk is r2:
                    continue
                trk = parse_trace(rk["log"])
                err = trk["first_error"][1] if trk["first_error"] else None
                at = "trace pass %d after history %s%s" % (node["pass"], hist_label(h), where)
                if x == "S" and (rk["rc"] != 0 or err is not None):
                    reasons.append("%s failed (rc=%d): %s" % (at, rk["rc"], err))
                if x == "F" and (err is None or FAIL_MSG not in err):
                    reasons.append("%s did not fail at the forced failure: %s" % (at, err))
                later_traced |= {nm for (kind, nm) in trk["names"] if kind == "cs"}
    later_traced -= set(traced)
    traced_active = {nm[0]: seg for (kind, nm), seg in tr["names"].items()
                     if kind == "active"}
    kernel_names = {name_bytes(n): name_bytes(m) for n, m in kernel["names"].items()}
    kernel_universe = {name_bytes(n) for n in kernel["universe"]}

    # The universe dumped at body start: the kernel's candidates, every traced
    # name (every reading of an ambiguous record), every name token of the
    # files the configuration read and of its definers, and every
    # one-character name and the null name. hash_coverage below checks it
    # against TeX's own count.
    sources = read_files(tex, reads)
    file_names = set()
    for data in sources.values():
        file_names |= source_names(data)
    for it in cfg["preamble"]:
        if "definer" in it:
            file_names |= source_names(it["definer"].encode("utf-8"))
    singles = {bytes([b]) for b in range(256)} | {NULL_CS}
    universe = sorted(kernel_universe | set(traced) | later_traced | file_names |
                      written | singles)
    if universe_filter is not None:
        universe = [n for n in universe if universe_filter(n)]

    # R4: format-state meanings of universe names outside the kernel's
    # candidates. The kernel is complete, so every one must be undefined.
    extra = sorted(n for n in universe if n not in kernel_universe)
    fmt_meaning = dict(kernel_names)
    if extra:
        d4, unw4, r4 = fmt_state_dump(tex, "r4_fmt_extra", extra)
        provenance["fmt_extra_tex_sha256"] = r4["tex_sha256"]
        kernel_gaps = []
        for i, nm in enumerate(extra):
            m = d4["meanings"].get(i)
            if m is not None:
                fmt_meaning[nm] = m
                kernel_gaps.append(name_str(nm))
        if kernel_gaps:
            contract["kernel_gaps"] = sorted(kernel_gaps)
            reasons.append("%d names defined in format state are missing from the "
                           "kernel: %s" % (len(kernel_gaps), sorted(kernel_gaps)[:5]))

    # R3: the body-start meaning dump (after the begin-document hooks), with
    # TeX's own hash count, on EVERY pass of the protocol's pass histories
    # (passes 1 to MAX_PASSES+1), in three environments (review re-review 2,
    # defects 1 to 3: membership and the count covered passes 1 and 2 only,
    # the count on pass 3 was labelled pass 2, and the date and job-name
    # checks covered pass 1 only):
    #   forced/job     the reference: the contract's state is pass 1 of it;
    #   grading/job    the graders' environment (real clock), compared with
    #                  forced/job pass by pass: any difference outside the
    #                  kernel's date-dependent names is date_dependent_state;
    #   grading/<2nd>  the graders' environment under a second job name,
    #                  compared with grading/job pass by pass: a membership
    #                  difference is jobname_dependent_state, a meaning
    #                  difference is listed in jobname_dependent_meanings.
    # On every pass TeX's hash count must find no name outside the universe.
    block, unw = dump_block(universe, actives=True, u8_sweep=True)
    dump_doc = pre + b"\\begin{document}\n" + block + END_DOC
    count_prefix = pre + b"\\begin{document}\n"
    with ThreadPoolExecutor(max_workers=len(envs)) as ex:
        futs = [ex.submit(run_history_tree, tex, "r3_%s_%s" % (e, j), dump_doc, histories,
                          env=e, jobname=j, count_prefix=count_prefix, universe=universe)
                for e, j in envs]
        trees = [f.result() for f in futs]
    r3 = trees[0][""]["S"]
    report["r3_secs"] = round(r3["secs"], 2)
    provenance["dump_tex_sha256"] = r3["tex_sha256"]
    provenance["dump_log_sha256"] = sha256_bytes(r3["log"])
    d3 = parse_dump(r3["log"])
    date_dep = {name_bytes(n) for n in kernel.get("date_dependent_names", [])}
    job_dep_k = {name_bytes(n) for n in kernel.get("jobname_dependent_names", [])}
    states = []
    coverage_passes = []
    for (env, jobname), tree in zip(envs, trees):
        where = "" if (env, jobname) == envs[0] else " (%s, job name %s)" % (env, jobname)
        st = {}
        for h, node in tree.items():
            at = "pass %d after history %s%s" % (node["pass"], hist_label(h), where)
            rs = node["S"]
            ds = d3 if rs is r3 else parse_dump(rs["log"])
            if rs["rc"] != 0 or ds["error"] is not None:
                reasons.append("body-start dump failed on %s: rc=%d %s"
                               % (at, rs["rc"], ds["error"]))
            st[h] = _dump_state(ds, universe)
            rf = node["F"]
            if rf is not None:
                ef = first_error(rf["log"])
                if rf["rc"] == 0 or ef is None or FAIL_MSG not in ef:
                    reasons.append("the failing run of %s did not fail at the forced "
                                   "failure (rc=%d): %s" % (at, rf["rc"], ef))
                member, meaning = _state_diff(st[h], _dump_state(parse_dump(rf["log"]),
                                                                 universe), date_dep)
                if member or meaning:
                    reasons.append("nondeterministic_state: two runs of %s differ: %s"
                                   % (at, (member + meaning)[:5]))
            cv = node["coverage"]
            if cv.get("error"):
                reasons.append("body-start %s on %s" % (cv["error"], at))
            elif cv["uncovered"] != 0:
                reasons.append("TeX's hash table at body start on %s holds %d names "
                               "outside the dumped universe" % (at, cv["uncovered"]))
            rec = {"env": env, "jobname": jobname, "history": hist_label(h),
                   "pass": node["pass"]}
            if (env, jobname) == envs[0]:
                rec.update(cv)
            else:
                rec.update({k: cv[k] for k in ("uncovered", "error") if k in cv})
            coverage_passes.append(rec)
        states.append(st)
    forced, grading, second = states
    cov = dict(trees[0][""]["coverage"])
    # A name whose MEANING differs between passes while it stays defined (an
    # .aux checksum such as rerunfilecheck's \\ReFiCh@1) is recorded as
    # pass-dependent; a MEMBERSHIP difference makes the contract incomplete.
    pass_dep = set()
    job_dep = set()
    for h in histories:
        n = len(h) + 1
        if h:
            member, meaning = _state_diff(forced[""], forced[h])
            pass_dep.update(meaning)
            if member:
                reasons.append("pass_dependent_state: the body-start name set on pass %d "
                               "after history %s differs from pass 1: %s"
                               % (n, hist_label(h), member[:5]))
        member, meaning = _state_diff(forced[h], grading[h], date_dep)
        if member or meaning:
            reasons.append("date_dependent_state: the body-start state on pass %d after "
                           "history %s under the real clock differs from the forced "
                           "date: %s" % (n, hist_label(h), (member + meaning)[:5]))
        member, meaning = _state_diff(grading[h], second[h], date_dep | job_dep_k)
        job_dep.update(meaning)
        if member:
            reasons.append("jobname_dependent_state: the body-start name set on pass %d "
                           "after history %s under job name %s differs: %s"
                           % (n, hist_label(h), SECOND_JOBNAME, member[:5]))

    bad_prims = sorted(p for p, m in d3["prims"].items() if m != "\\" + p)
    if bad_prims or len(d3["prims"]) != len(DUMP_PRIMITIVES):
        reasons.append("dump primitives redefined or missing: %s" % bad_prims)
    if unw:
        contract["unwritable_names"] = sorted(name_str(n) for n in unw)
        reasons.append("%d universe names could not be written into the dump, so their "
                       "membership is unknown" % len(unw))
    body = {}
    for i, nm in enumerate(universe):
        if nm in unw:
            continue
        if i not in d3["meanings"]:
            reasons.append("dump lost name %s" % name_str(nm))
            continue
        body[nm] = d3["meanings"][i]

    # Readings of an ambiguous trace record that name nothing: when one
    # reading exists (in format state or at body start) the others are
    # phantoms; when none does, the first reading is kept.
    def exists(n):
        return body.get(n) is not None or fmt_meaning.get(n) is not None
    phantoms = set()
    for grp in tr["ambiguous"]:
        real = [n for n in grp if exists(n)]
        keep = set(real) if real else {grp[0]}
        phantoms |= {n for n in grp if n not in keep and n not in tr["sure"]}

    defined, reverted, params, untraced = {}, [], [], []
    for nm, bm in body.items():
        km = fmt_meaning.get(nm)
        if bm == km:
            if nm in traced and nm not in phantoms:
                c = classify_meaning(nm, bm) if bm is not None else {"kind": "Undefined"}
                if c["kind"] == "Primitive" and name_bytes(c["primitive"]) == nm:
                    params.append(name_str(nm))
                else:
                    reverted.append(name_str(nm))
            continue
        if nm not in traced:
            untraced.append(name_str(nm))
        d = classify_meaning(nm, bm)
        d["meaning_sha256"] = sha256_bytes(bm or b"undefined")[:16]
        d["set_in"] = seg_label(traced[nm]) if nm in traced else "untraced"
        if name_str(nm) in pass_dep:
            d["pass_dependent"] = True
        if name_str(nm) in job_dep or nm in job_dep_k:
            d["jobname_dependent"] = True
        defined[name_str(nm)] = d
    if untraced:
        reasons.append("%d names changed meaning without a traced assignment: %s"
                       % (len(untraced), sorted(untraced)[:5]))
    lost = sorted(n for n, d in defined.items() if d["set_in"] == "before_trace")
    if lost:
        reasons.append("%d names whose surviving assignment the trace does not show: %s"
                       % (len(lost), lost[:5]))
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

    # R5: the closure self-check, an independent run. The sample is drawn
    # from the whole dumped UNIVERSE, members and non-members alike, so the
    # non-member direction is tested too (review defect 5); hash_coverage
    # above is the check that does not depend on the universe at all.
    rng = random.Random(int(config_key[:16], 16))
    k = max(1, math.ceil(0.01 * len(universe)))
    sample = sorted(rng.sample(universe, k))
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
    provenance["selfcheck_log_sha256"] = sha256_bytes(r5["log"])
    d5 = parse_dump(r5["log"])
    if r5["rc"] != 0 or d5["error"] is not None:
        reasons.append("self-check run failed: rc=%d %s" % (r5["rc"], d5["error"]))
    unw5 = set(unw5)
    if unw5:
        reasons.append("%d self-check names could not be written" % len(unw5))
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
        "sample_from": "universe",
        "sampled": len(sample),
        "sampled_members": sum(1 for n in sample if n in members),
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
                         "traced_names": len(traced), "universe": len(universe),
                         "later_pass_traced_names": len(later_traced),
                         "job_written_names": len(written),
                         "passes": MAX_PASSES + 1,
                         "pass_histories": [hist_label(h) for h in histories],
                         "file_token_names": len(file_names),
                         "ambiguous_trace_records": len(tr["ambiguous"]),
                         "phantom_readings": len(phantoms)},
        "coverage": cov,
        "coverage_passes": coverage_passes,
        "defined_names": defined,
        "reverted_names": sorted(reverted),
        "parameters_assigned": sorted(params),
        "pass_dependent_meanings": sorted(pass_dep),
        "jobname": JOBNAME,
        "jobname_dependent_meanings": sorted(set(job_dep) | {
            name_str(n) for n in job_dep_k if body.get(n) is not None}),
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


def batch_polarity(log: bytes, idxs: list, rc: int) -> dict:
    """Polarity of each probe of a batched run: an error in a probe's segment
    (between its LPPROBE marker and the next) makes it fatal. An error is a
    `! ` line followed by TeX's location context, the SAME test as the solo
    classifier's first_error (review defect R1.8: the batch counted any line
    starting `! `, so a printed meaning holding `! LaTeX Error` read as a
    fatal here and as nothing in the solo run)."""
    lines = log.split(b"\n")
    seen: dict = {}
    cur = None
    for n, raw in enumerate(lines):
        m = re.match(rb"^LPPROBE:(\d+|end)$", raw.rstrip(b"\r"))
        if m:
            cur = None if m.group(1) == b"end" else int(m.group(1))
            if cur is not None:
                seen.setdefault(cur, [])
            continue
        if cur is not None and raw.startswith(b"! ") and _has_context(lines, n + 1):
            seen[cur].append(raw[2:].decode("utf-8", "replace").strip())
    return {i: ("timeout" if rc == TIMEOUT_RC else
                ("unreached" if i not in seen else
                 ("fatal" if seen[i] else "ok"))) for i in idxs}


def run_probes(tex: Tex, contract: dict, names: list, workers: int, report: dict,
               texmf_root: str, kernel: dict):
    cfg = contract["configuration"]
    base_fls = None
    r = tex.pdflatex(tex.job("probe_base"), probe_doc(cfg, ""), recorder=True,
                     env="grading")
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
        # The oracle's predicate (B.4): grading environment, the pass
        # protocol of run_to_fixpoint, ok = rc 0 AND a PDF on the last pass.
        i, p = i_p
        jd = tex.job("probe_%04d" % i)
        res = tex.fixpoint(jd, probe_doc(cfg, p["snippet"]), env="grading",
                           timeout=PROBE_TIMEOUT)
        out = classify_outcome(res["rc"], res["log"], res["pdf"])
        out["passes"] = res["passes"]
        _, ins = parse_fls(res["first_fls"])
        lazy = sorted(texmf_rel(tex.stable_path(x), texmf_root) for x in ins
                      if x.startswith("/") and x not in base_fls
                      and not tex.is_job_path(x))
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
                           timeout=PROBE_TIMEOUT * 4, env="grading")
        shutil.rmtree(jd, ignore_errors=True)
        return batch_polarity(res["log"], idxs, res["rc"])

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
        "protocol": {"solo": "%s -interaction=nonstopmode -halt-on-error -recorder, "
                             "fresh directory, grading environment, the oracle's pass "
                             "protocol (to the first rc 0 in at most %d runs, then one "
                             "confirming run), coreutils timeout %ds per run; ok = rc 0 "
                             "and a PDF on the last run; otherwise the error class of "
                             "its first `!` line" % (_oracle.ENGINE_PDFLATEX, MAX_PASSES,
                                                     PROBE_TIMEOUT),
                     "batch": "every probe of one command in one -interaction=nonstopmode "
                              "run (no -halt-on-error), each in \\begingroup...\\par\\endgroup "
                              "after a marker; polarity = a `!` line with TeX's location "
                              "context in its segment (the solo test)",
                     "lazy_files": "first-run .fls INPUT files minus those of the same "
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
    with Tex(image, Path(a.work).expanduser() if a.work else None) as tex:
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
    with Tex(image, Path(a.work).expanduser() if a.work else None) as tex:
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
    ap.add_argument("--work", default=None,
                    help="a directory under the oracle work root (default: the "
                         "oracle work root itself, _oracle.py workroot)")
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
