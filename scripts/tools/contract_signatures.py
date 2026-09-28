#!/usr/bin/env python3
"""Signature probes of a configuration contract (ADR-012, M1 slice 2).

A contract (gen_contract.py generate) says which names exist at body start. This
module says, for the names a document can TYPE, how each one may be USED: the
arguments it consumes and, per mode and context, whether a well-typed use
compiles (STRICT_TIER_DESIGN.md B.2, fields `signature`, `environments`,
`definer_rules`, `decl_templates`). It is part of the generator and a client
of the one oracle: every TeX job is `gen_contract.Tex.fixpoint`, i.e.
`_oracle.run_engine` in the pinned image, under the graders' environment and the
oracle's pass protocol. It starts no engine of its own (check_oracle_pin.py).

WHAT IS ATTESTED, AND HOW (design B.2: solo probes, one variable each,
classified by error class, never by rc; a shape read from \\meaning is a hint).

  names in scope   every control sequence a body can name under the body-start
                   catcodes: a run of catcode-11 bytes, or one byte that is not
                   one, that is a member of the contract's closed world (the
                   committed kernel file plus the contract's defined_names).
                   A name outside the closed world is E1 and needs no signature.
  cells            (mode, context) pairs a use is probed in: `text` (inside a
                   paragraph), `math` (inline math), `vertical` (between
                   paragraphs), `list` (after \\item in itemize) and `preamble`.
                   Tabular cells are M4.
  the sentinel     `\\outer\\def\\lpstop{}`. A macro that tries to take \\lpstop
                   as an argument stops with `Forbidden control sequence found
                   while scanning use of` (error class forbidden_cs_use,
                   outcome `grab`); a futurelet peek (\\@ifnextchar) does not.
                   So `\\cs A\\lpstop` grabs iff \\cs still wants a mandatory
                   argument after the arguments A, `\\cs A[\\lpstop]` grabs iff
                   \\cs consumes an optional argument there, and so on (below).
  shape            found in the first cell (text, math, vertical, list,
                   preamble) where a use compiles:
                     1. mandatory count r: the first k with `\\cs {a}^k\\lpstop`
                        not grabbing;
                     2. payload types, if the use `\\cs {a}^r` fails with an
                        error that is not a mode error: a greedy search over the
                        payload lattice (LATTICE), then minimised (a slot keeps
                        a non-text payload only if `a` there fails: that
                        failure is recorded as the slot's negative);
                     3. exactness, attested: the canonical use compiles, the
                        canonical use followed by \\lpstop does not grab, the
                        FOLLOW PROBE passes (version 2, below), and with its
                        last mandatory argument dropped it grabs (the
                        missing-argument negative). A multi-stage macro that
                        grabs more once its payloads are well typed goes back
                        to step 1;
                     4. optional arguments at each position j <= r: before
                        mandatory argument j, `\\cs A_<j [a] A_j..A_{r-2}\\lpstop`
                        grabs iff an optional argument was consumed there
                        (without one, `[`, `a`, `]` would fill the remaining
                        mandatory slots); after the last, `\\cs A[\\lpstop]`
                        grabs iff one was consumed. Tri-state: consumed / not
                        consumed (the probe compiled) / unknown (it failed
                        otherwise). Up to MAX_OPT_RUN in a row;
                     5. a star at position 0: `\\cs*A_1..A_{r-1}\\lpstop` grabs
                        iff `*` was taken as a flag (else it is the first
                        mandatory argument); for r = 0 only a grab proves a
                        star (`\\cs*\\lpstop`, `\\cs*[\\lpstop]`), otherwise it
                        is unknown. A starred name gets its own variant,
                        discovered the same way after `*`;
                     6. a brace group taken if present (a peek for `{`, as
                        \\input does): `\\cs A{\\lpstop}` grabs iff it is
                        consumed (kind `gopt`); without this test the group
                        would be modelled as typeset text.
  follow probe     (version 2, review C-82) `\\lpfsave <use>\\lpfollow\\lpnocs`:
                   the \\outer sentinel only trips a macro PARAMETER scan, so a
                   use that takes the next token another way (\\string,
                   \\noexpand, \\meaning, \\aftergroup, \\expandafter, \\index,
                   \\enddocument, \\ifdefined) or changes the catcodes or the
                   group level (\\obeylines, \\obeyspaces, \\makeatletter,
                   \\bgroup) passed version 1 as r = 0. The probe passes only
                   if \\lpfollow is executed next and finds the catcodes of all
                   256 bytes and \\currentgrouplevel as \\lpfsave saved them
                   (`! LPFOLLOW.`); \\lpnocs (undefined) catches a use that
                   reorders or defers it.
  per cell         the canonical use of each variant, solo: `ok` or the fatal
                   error class and message. In an accepting cell,
                   `shape_checked` records that the shape holds there: the
                   follow probe passes, and (outside the base cell) nothing
                   more is grabbed; only checked cells give content kinds.
  argument types   a text-like slot (payload `a` accepted) is typed by what its
                   payload is typeset as, in each checked cell that accepts the
                   use (text, math and the base cell), from three one-variable
                   witnesses classified by ERROR CLASS: `a^b` (missing_dollar =
                   typeset in text), `\\"a` (math_accent = typeset in math,
                   without toggling it as version 1's `$a$` did) and `a&b`
                   (compiles only where nothing is typeset, or in an
                   alignment); `a\\par b` in the base cell gives `long`.
                   TyText / TyMath / TyInherit (text in text cells, math in the
                   math cell) / TyLabel (no cell typesets the payload); None
                   when the cells disagree otherwise. Every type is then
                   CONFIRMED (version 2): the payloads it admits must compile
                   in the consumer document (\\title given; headings, the
                   toc/lof/lot before the use; \\maketitle, a new page and the
                   marks after it), and a TyLabel payload must be processed at
                   the use (`\\lpnocs` there is undefined_cs, not stored or
                   discarded), with each other text-like slot also set to
                   toc/lof/lot, and no TyLabel beside two or more other
                   text-like slots. A refuted type is None, with `refuted`.
                   Non-text slots are typed by the lattice payload that made
                   the use compile: TyNumber `1`, TyDimen `1pt`, TyCounter (a
                   counter of the configuration), TyFile `lpprobe` (lpprobe.tex
                   and lpprobe.sty sit in every probe directory), TyCsName
                   `\\lpprobecs` (undefined), TyNewName `lpq` (an undefined
                   name, for slots that define one), TyEnvName (an environment
                   of the configuration), TyKV `width=1cm`, TyUrl `http://x`.

  A name whose shape cannot be attested in any cell is `unresolved`, with the
  reason and every cell's outcome: its uses are outside the strict tier. That
  is not a failure of the contract (design B.2: signature coverage need not be
  complete; the NAME set must be).

  environments     every X whose \\X and \\endX are members, X letters with an
                   optional trailing `*`: begin-arguments by the same method
                   (head `\\begin{X}`, body `a` then `\\item a`), per cell, and
                   one-variable body probes (`a^b`, `$a$`, `\\item a`,
                   `a\\par b`, `\\caption{a}`, `a&b`) giving the body mode and
                   the contexts the environment pushes.
  definer_rules    a probe table: each admitted definer (\\newcommand,
                   \\renewcommand, \\providecommand, \\newenvironment,
                   \\renewenvironment, \\newcounter, \\setcounter,
                   \\addtocounter, \\newtheorem in four forms, \\theoremstyle,
                   \\DeclareMathOperator) on targets derived from the contract
                   (a fresh name, a macro, a \\relax-meaning name, a primitive,
                   a chardef, an end-prefixed name, a counter, an environment),
                   in the preamble and in the body. The table IS the attestation.
  decl_templates   `decl-templates`: per owner combination (kernel, amsthm,
                   amsthm+thmtools) and \\newtheorem form, the names the
                   declaration defines (a complete contract of the base
                   configuration with the declaration as a definer, diffed
                   against the base's), and a collision matrix.

  Batched probes are TRIAGE only (design B.2): after the solo probes, every
  name's probes run once more in one nonstop document, each in a group after a
  marker, and the batch polarity is compared with the solo one (follow and
  consumer probes are skipped). Nothing in a signature comes from a batch.

  calibration      (version 2) the design's premises re-measured for the
                   configuration (CALIBRATION): the witnesses' classes, the
                   follow probe on \\relax / \\string / \\obeylines, the
                   consumer suite. A configuration where one fails is refused.
  the log          every probe of a record, in order, with the message of a
                   fatal one: check_sidecar RE-DERIVES the whole record from
                   it (replay(): the derivation re-run on the log, no TeX).

The sidecar `corpora/contracts/signatures/<contract>.json` names its contract
by sha256 (a regenerated contract with other bytes makes it stale) and is
byte-reproducible: no timing is written, and the documents run are pinned by
the sha256 of every probe .tex. probe_names() is the on-demand API for M3's
use-based attestation, cached by (contract sha256, name, cell).
"""
from __future__ import annotations

import hashlib
import json
import random
import re
import shutil
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import gen_contract as gc  # noqa: E402  (the generator; its Tex is the oracle client)

SIG_SCHEMA = "lp-contract-signatures/1"
DECL_SCHEMA = "lp-decl-templates/1"
# Bumped by hand when the probe DESIGN changes the output on purpose (as
# gen_contract.GENERATOR_VERSION; never a source hash, the C-68 lesson).
SIGNATURE_VERSION = "2"
SIG_DIR = gc.CONTRACT_DIR / "signatures"
DECL_DIR = gc.CONTRACT_DIR / "decl_templates"
CACHE = "~/.cache/lp-oracle/contracts/signatures"

# Probe-design names. Each must be UNDEFINED in the configuration probed
# (checked against the closed world; a configuration that defines one cannot
# be probed with this design and is refused).
SENT = "lpstop"          # the \outer sentinel
CSPAY = "lpprobecs"      # the TyCsName payload
FRESH = "lpq"            # the definer table's fresh name (and endlpq, c@lpq)
DECL_FRESH = "zzq"       # the decl-template fresh theorem name (design B.2)
# The follow probe (version 2, review C-82): `\lpfsave <use>\lpfollow\lpnocs`.
# \lpfsave records the catcodes of all 256 bytes and the group level;
# \lpfollow (\outer, so a macro cannot take it as an argument) compares them
# and stops with `! LPFOLLOW.` if nothing changed, `! LPSTATE.` if something
# did; \lpnocs is undefined, so a use that consumes, defers or reorders the
# token after it (\string, \noexpand, \aftergroup, \expandafter, \index, ...)
# stops on \lpnocs (or not at all) instead. \lpnocs is also the payload of the
# stored-payload probe (a TyLabel slot's payload must be processed at the
# use, not stored or discarded).
FOLLOW = "lpfollow"
FSAVE = "lpfsave"
NOCS = "lpnocs"
FOLLOW_AUX = ("lpfone", "lpfgob", "lpfcc", "lpfstate", "lpfnow")
RESERVED = (SENT, CSPAY, FRESH, "end" + FRESH, "c@" + FRESH, DECL_FRESH, "c@" + DECL_FRESH,
            FOLLOW, FSAVE, NOCS) + FOLLOW_AUX
FOLLOW_DEF = (r"\long\def\lpfone#1{#1}\long\def\lpfgob#1{}"
              r"\def\lpfcc#1{\ifnum#1<256 \the\catcode#1,\expandafter\lpfone\else"
              r"\expandafter\lpfgob\fi{\expandafter\lpfcc\expandafter{\the\numexpr#1+1}}}"
              r"\def\lpfsave{\edef\lpfstate{\lpfcc{0}/\the\currentgrouplevel}}"
              r"\outer\def\lpfollow{\edef\lpfnow{\lpfcc{0}/\the\currentgrouplevel}"
              r"\ifx\lpfstate\lpfnow\errmessage{LPFOLLOW}\else\errmessage{LPSTATE}\fi}")
FOLLOW_OK = "LPFOLLOW."
FOLLOW_STATE = "LPSTATE."
# Files in every probe directory, so that a file argument can be well typed.
FILE_STEM = "lpprobe"
COMPANIONS = {FILE_STEM + ".tex": b"lpprobefile\n",
              FILE_STEM + ".sty": b"\\ProvidesPackage{lpprobe}\n"}

CELLS = ("text", "math", "vertical", "list", "preamble")
# Where the use sits inside the body of a probe document (preamble: in the
# preamble, with `x` as the body so that a PDF is made).
CELL_DOC = {"text": "x %s y", "math": "x $%s$", "vertical": "%s\\par x",
            "list": "\\begin{itemize}\\item x %s y\\end{itemize}"}
TEXTLIKE_CELLS = ("text", "vertical", "list")
# The consumer document (version 2, review C-82): a slot's payload may be
# typeset LATER by another command (\section[..] and \caption[..] through
# the .toc/.lof, \title/\author/\thanks through \maketitle, \markboth and
# \sectionmark through the running heads), across the pass protocol. A
# consumer cell `consumers:<cell>` is <cell> with a \title given before the
# use (\maketitle without one is an error at the pin) and these around it.
CONS = "consumers:"
CONS_TITLE = "\\title{t}\n"
CONS_PRE = "\\pagestyle{headings}\\tableofcontents\\listoffigures\\listoftables\n"
CONS_POST = "\n\\maketitle\\newpage x\\leftmark\\rightmark"
# The files the consumer suite reads back. A slot's consumption can depend on
# another slot's value (\addtocontents{toc}{..} is typeset, {a}{..} is written
# nowhere): a TyLabel candidate is also confirmed with each other text-like
# slot set to each of these, and is not typed at all when the use has two or
# more other text-like slots (their joint values are not attested).
CONS_KEYS = ("toc", "lof", "lot")
MAX_REQ = 9
MAX_OPT_RUN = 3
MAX_TYPE_PASSES = 2

TEXT = "a"
# Content witnesses, one variable each (version 2). Measured at the pin
# (2026-09-27): `a^b` is fatal typeset in text mode and fine in math and as a
# key; `\"a` is fatal typeset in math mode WITHOUT toggling it (`$a$`, the
# version-1 witness, closed the math and reopened it, so \pmod{$a$} compiled
# and \pmod read as not typesetting its argument; \pmod{\LaTeX} is fatal);
# `a&b` is fatal typeset in either mode outside an alignment and fine as a
# \label/\cite key or in \typeout. calibrate() re-measures all of this for
# the configuration probed and refuses it if any fails.
MATH_CONTENT = "a^b"
TEXT_CONTENT = "\\\"a"
NONE_CONTENT = "a&b"
PAR_CONTENT = "a\\par b"
STORED_CONTENT = "\\" + NOCS
GRAB_CLASS = "forbidden_cs_use"
# Error classes that say the USE is in the wrong place (mode or context), so
# that no payload can fix it in this cell: typing is skipped and the next cell
# is tried.
MODE_CLASSES = frozenset({
    "missing_dollar", "math_only", "text_only", "wrong_mode", "lonely_item",
    "missing_begin_document", "no_line_to_end", "display_math_end",
    "misplaced_tab", "extra_tab", "misplaced_alignment", "preamble_only",
    "no_pdf"})
# Environment body probes (one variable: the body).
ENV_BODIES = (("math_content", MATH_CONTENT), ("text_content", TEXT_CONTENT),
              ("item", "\\item a"), ("par", PAR_CONTENT), ("caption", "\\caption{a}"),
              ("alignment", "a&b"))
ENV_CELLS = ("vertical", "text", "math")


# ---------------------------------------------------------------------------
# Pure helpers (unit-tested by check_gen_contract_parsers.py)
# ---------------------------------------------------------------------------

def refine_class(e: str, m: str | None) -> str:
    """The error class a probe outcome is recorded with: gen_contract's class,
    refined where this module needs more than it says (the follow probe's
    own `! LPSTATE.`, and a missing counter, which steers the payload search
    and so must not depend on the message text)."""
    if m == FOLLOW_STATE:
        return "lp_state_changed"
    if e == "latex_error" and m and m.startswith("LaTeX Error: No counter"):
        return "no_counter"
    if e == "other" and m and m.startswith("Please use \\mathaccent for accents in math mode"):
        return "math_accent"
    return e


def outcome_of(res_or_cls: dict) -> dict:
    """A probe outcome, compact: o in {ok, grab, follow, fatal, timeout}, e
    the error class, m the first error message. `grab` is the sentinel's own
    error; `follow` is the follow probe's `! LPFOLLOW.` (the token after the
    use was the next one executed, and the catcodes and group level are
    unchanged)."""
    c = res_or_cls
    if c["outcome"] == "ok":
        return {"o": "ok"}
    if c["outcome"] == "timeout":
        return {"o": "timeout", "e": "timeout"}
    if c.get("message") == FOLLOW_OK:
        return {"o": "follow"}
    o = {"o": "grab" if c.get("error_class") == GRAB_CLASS else "fatal",
         "e": refine_class(c["error_class"], c.get("message"))}
    if c.get("message"):
        o["m"] = c["message"]
    return o


# Outcomes recorded in the probe log by name; every other one is a fatal
# error class, followed by its message.
NAMED_OUTCOMES = ("ok", "grab", "follow", "timeout")


def cs(name: str) -> str:
    return "\\" + name


def arg_text(kind: str, payload: str) -> str:
    return ("[%s]" if kind == "opt" else "{%s}") % payload


def build_use(head: str, slots: list, *, star: bool = False, stop: bool = False,
              tail: str = "") -> str:
    """`head`, an optional `*`, the arguments, then \\lpstop if `stop`, then
    `tail` (an environment's body and \\end). slots: [(kind, payload)]."""
    s = head + ("*" if star else "") + "".join(arg_text(k, p) for k, p in slots)
    if stop:
        s += cs(SENT)
        # A letter right after the control word would extend its name
        # (`\lpstopa`); the space is skipped by TeX's lexer after a control word.
        if tail[:1].isalpha():
            s += " "
    return s + tail


def follow_use(use: str) -> str:
    """The follow probe of a (complete) use: the state saved before it, then
    \\lpfollow and the undefined \\lpnocs after it."""
    return cs(FSAVE) + " " + use + cs(FOLLOW) + cs(NOCS)


def _mentions(name: str, use: str) -> bool:
    return re.search(r"\\%s(?![A-Za-z])" % name, use) is not None


def cell_doc(pre: bytes, cell: str, use: str) -> bytes:
    """The whole probe document: the configuration, then the use in `cell`.
    The sentinel (and the follow probe's macros) are defined iff the use
    mentions them, just before it. A `consumers:<cell>` cell is <cell> with
    the consumer suite around the use (CONS_*)."""
    cons = cell.startswith(CONS)
    if cons:
        cell = cell[len(CONS):]
    sdef = ("\\outer\\def%s{}" % cs(SENT)) if _mentions(SENT, use) else ""
    if _mentions(FOLLOW, use):
        sdef += FOLLOW_DEF
    top = CONS_TITLE.encode("utf-8") if cons else b""
    bpre, bpost = (CONS_PRE, CONS_POST) if cons else ("", "")
    if cell == "preamble":
        return (pre + top + (sdef + use + "\n").encode("utf-8") +
                ("\\begin{document}\n%sx%s\n\\end{document}\n" % (bpre, bpost)).encode("utf-8"))
    return (pre + top + b"\\begin{document}\n" +
            (bpre + sdef + CELL_DOC[cell] % use + bpost + "\n").encode("utf-8")
            + b"\\end{document}\n")


def letters_of(catcodes: list) -> set:
    return {b for b in range(256) if catcodes[b] == 11}


def user_facing(name: str, letters: set) -> bool:
    """A name a body can type under the body-start catcodes: a run of
    catcode-11 bytes, or a single byte that is not one (a control symbol)."""
    b = gc.name_bytes(name)
    if not b:
        return False
    if len(b) == 1:
        return True
    return all(c in letters for c in b)


def closed_world_members(kernel_names: dict, contract: dict) -> dict:
    """{name: meaning kind} of every member at body start: the kernel's
    names, minus those the configuration made undefined, plus its own."""
    dn = contract["defined_names"]
    out = {n: k for n, k in kernel_names.items()
           if not (n in dn and dn[n]["kind"] == "Undefined")}
    for n, d in dn.items():
        if d["kind"] != "Undefined":
            out[n] = gc.short_kind(d)
    return out


def meaning_hint(name: str, meanings: dict) -> dict:
    """The shape a \\meaning SUGGESTS: never attestation (design B.2; the
    spike measured static arity wrong on 30% of macros). meanings: {name:
    bytes} at body start, including robust inner names."""
    m = meanings.get(name)
    if m is None:
        return {"source": "undefined"}
    d = gc.classify_meaning(gc.name_bytes(name), m)
    via = None
    if d.get("robust") and d.get("robust_inner") in meanings and meanings[d["robust_inner"]]:
        via = d["robust_inner"]
        m = meanings[via]
        d = gc.classify_meaning(gc.name_bytes(via), m)
    if d["kind"] != "Macro":
        return {"source": "kind", "kind": d["kind"]}
    out = {"source": "ltcmd" if "ltcmd_spec" in d else "params", "arity": d["arity_hint"],
           "delimited": d["delimited"]}
    if via:
        out["via"] = via
    if "ltcmd_spec" in d:
        spec = d["ltcmd_spec"]
        out["spec"] = spec
        out["arity"] = sum(1 for c in spec if c in "mrRvb")
        out["star"] = spec.startswith("s")
        out["opt"] = any(c in "oOdD" for c in spec)
        return out
    body = m.split(b"->", 1)[1] if b"->" in m else b""
    out["star"] = body.startswith(b"\\@ifstar ") or body.startswith(b"\\kernel@ifstar ")
    out["opt"] = bool(re.match(rb"^\\(?:@ifnextchar \[|kernel@ifnextchar \[|@testopt |"
                               rb"@protected@testopt |@dblarg )", body))
    return out


# The error classes that are evidence of TYPESETTING in a mode (not of a key
# or string context rejecting the witness, e.g. `\"a` in \label's
# \csname is missing_endcsname): `a^b` typeset in text, `\"a` typeset in
# math. Measured at the pin, 2026-09-27.
TEXT_TYPESET = "missing_dollar"
MATH_TYPESET = "math_accent"


def content_kind(cell: str, m: str, t: str, n: str) -> str:
    """What a text-like slot's payload is, in one cell, from the outcome words
    of the three witnesses: m for `a^b`, t for `\"a`, n for `a&b`.
    `text`/`math`: typeset in that mode (the other mode's witness fails with
    that mode's typesetting error, the own one compiles); `none`: no mode
    shows typesetting, and `a^b` and `a&b` both compile (a key, a message; an
    alignment cell, where `a&b` compiles, typesets `\"a` in math and so is
    `math`); `opaque` and `restricted` describe no type."""
    text_ts, math_ts = m == TEXT_TYPESET, t == MATH_TYPESET
    if text_ts and math_ts:
        return "restricted"
    if text_ts:
        return "text" if t == "ok" else "restricted"
    if math_ts:
        return "math" if m == "ok" else "restricted"
    if m == "ok" and n == "ok":
        return "none"
    if m == "ok" and t == "ok":
        return "opaque"
    return "restricted"


def body_mode_of(m: str, t: str) -> str | None:
    """An environment body's mode from the two mode witnesses' outcome words;
    None unless one mode is shown (version 1 read `either` from `$a$`, which
    toggled math, so `\begin{math}` read as either)."""
    k = content_kind("", m, t, "fatal")
    return k if k in ("math", "text") else None


def argty_of(kinds: dict) -> str | None:
    """The lattice type of a text-like slot from its per-cell content kinds
    ({cell: kind}); None when the cells disagree in a way no type describes.
    TyLabel here is only a CANDIDATE: the consumer and stored-payload probes
    (_confirm_type) must confirm it."""
    if not kinds:
        return None
    vals = set(kinds.values())
    if vals & {"restricted", "opaque"}:
        return None
    if vals == {"none"}:
        return "TyLabel"
    if "none" in vals:
        return None
    tk = {kinds[c] for c in kinds if c in TEXTLIKE_CELLS}
    mk = kinds.get("math")
    if len(tk) > 1:
        return None
    t = next(iter(tk)) if tk else None
    if t == "text" and mk == "math":
        return "TyInherit"
    if t in (None, "text") and mk in (None, "text"):
        return "TyText"
    if t in (None, "math") and mk in (None, "math"):
        return "TyMath"
    return None


def lattice(contract: dict, members: dict) -> list:
    """The payload lattice for non-text slots, [(argty, payload)], in the
    default order. The counter and environment payloads are the first (by
    name) of the configuration's own: a counter with \\theX, and an
    environment whose \\X and \\endX are both macros."""
    counters = sorted(n for n, d in contract.get("counters", {}).items()
                      if d.get("the") and re.fullmatch(r"[A-Za-z]+", n))
    envs = sorted(n for n in members if re.fullmatch(r"[A-Za-z]+", n)
                  and members.get(n, "").startswith("Macro")
                  and members.get("end" + n, "").startswith("Macro"))
    out = [("TyNumber", "1"), ("TyDimen", "1pt")]
    if counters:
        out.append(("TyCounter", counters[0]))
    out += [("TyFile", FILE_STEM), ("TyCsName", cs(CSPAY)), ("TyNewName", FRESH)]
    if envs:
        out.append(("TyEnvName", envs[0]))
    out += [("TyKV", "width=1cm"), ("TyUrl", "http://x")]
    return out


def lattice_order(lat: list, err: dict) -> list:
    """The lattice, the types the error suggests first (a hint for the search
    only; the outcome decides)."""
    e = err.get("e", "")
    first = []
    if e in ("missing_number", "bad_unit"):
        first = ["TyNumber", "TyDimen"] if e == "missing_number" else ["TyDimen"]
    elif e == "no_counter":
        first = ["TyCounter"]
    elif e == "missing_file":
        first = ["TyFile"]
    elif e == "missing_control_sequence":
        first = ["TyCsName"]
    elif e == "already_defined":
        first = ["TyNewName"]
    elif e == "undefined_env":
        first = ["TyEnvName"]
    elif e.startswith("package_error:keyval"):
        first = ["TyKV"]
    return sorted(lat, key=lambda tp: (0 if tp[0] in first else 1,
                                       first.index(tp[0]) if tp[0] in first else 0))


# ---------------------------------------------------------------------------
# The prober: solo probes through the oracle, and a per-name session
# ---------------------------------------------------------------------------

class Prober:
    """Runs solo probes of one configuration: grading environment, the
    oracle's pass protocol (Tex.fixpoint), a fresh directory holding the
    companion files, the probe timeout. Thread-safe."""

    def __init__(self, tex: "gc.Tex", cfg: dict):
        self.tex = tex
        self.cfg = gc.normalize_config(cfg)
        self.pre = gc.preamble_tex(self.cfg)
        self.lock = threading.Lock()
        self.docs: set = set()
        self.solo = 0
        self.runs = 0
        self.secs = 0.0

    def run(self, cell: str, use: str) -> dict:
        doc = cell_doc(self.pre, cell, use)
        jd = self.tex.job("sig")
        for fn, data in COMPANIONS.items():
            (jd / fn).write_bytes(data)
        res = self.tex.fixpoint(jd, doc, env="grading", recorder=False,
                                timeout=gc.PROBE_TIMEOUT)
        shutil.rmtree(jd, ignore_errors=True)
        out = outcome_of(gc.classify_outcome(res["rc"], res["log"], res["pdf"]))
        with self.lock:
            self.docs.add(res["tex_sha256"])
            self.solo += 1
            self.runs += res["passes"]
            self.secs += res["secs"]
        return out

    def batch(self, items: list) -> dict:
        """Triage: every (idx, cell, use) of one name in one nonstop run,
        body cells in the body and preamble cells in the preamble, each in a
        group after a marker. Returns {idx: ok|fatal|timeout|unreached}."""
        pre_lines, body_lines = [], []
        sdef = "\\outer\\def%s{}" % cs(SENT)
        for i, cell, use in items:
            mark = "\\immediate\\write-1{LPPROBE:%d}" % i
            if cell == "preamble":
                pre_lines.append("%s\\begingroup %s\\endgroup" % (mark, use))
            else:
                body_lines.append("%s\\begingroup %s\\par\\endgroup" % (mark, CELL_DOC[cell] % use))
        end = "\\immediate\\write-1{LPPROBE:end}"
        doc = (self.pre + ("\n".join([sdef] + pre_lines + [end]) + "\n").encode("utf-8") +
               b"\\begin{document}\n" +
               ("\n".join([sdef] + body_lines + [end, "x"]) + "\n").encode("utf-8") +
               b"\\end{document}\n")
        jd = self.tex.job("sigbatch")
        for fn, data in COMPANIONS.items():
            (jd / fn).write_bytes(data)
        res = self.tex.pdflatex(jd, doc, halt=False, timeout=gc.PROBE_TIMEOUT * 4, env="grading")
        shutil.rmtree(jd, ignore_errors=True)
        return gc.batch_polarity(res["log"], [i for i, _, _ in items], res["rc"])


class Session:
    """The probes of one name (or environment): memoised by (cell, use), and
    logged in the order run, which is deterministic (each probe depends only
    on the outcomes before it)."""

    def __init__(self, prober: Prober):
        self.prober = prober
        self.memo: dict = {}
        self.log: list = []

    def p(self, cell: str, use: str) -> dict:
        key = (cell, use)
        if key not in self.memo:
            self.memo[key] = self.prober.run(cell, use)
            self.log.append(key)
        return self.memo[key]

    def evidence(self) -> list:
        """[cell, use, outcome] per probe, in the order run; the outcome is
        `ok`, `grab`, `follow`, `timeout` or the error class, and a fatal
        outcome carries its message as a fourth element. The log is complete:
        replay() re-derives the whole record from it."""
        return [evidence_entry(cell, use, self.memo[(cell, use)]) for cell, use in self.log]


def evidence_entry(cell: str, use: str, o: dict) -> list:
    if o["o"] in NAMED_OUTCOMES:
        return [cell, use, o["o"]]
    return [cell, use, o["e"]] + ([o["m"]] if o.get("m") else [])


def outcome_from_entry(entry: list) -> dict:
    """The inverse of evidence_entry."""
    o = entry[2]
    if o in ("ok", "grab", "follow"):
        return {"o": o}
    if o == "timeout":
        return {"o": "timeout", "e": "timeout"}
    out = {"o": "fatal", "e": o}
    if len(entry) > 3:
        out["m"] = entry[3]
    return out


class ReplayMiss(Exception):
    """A replayed derivation asked for a probe its log does not hold."""


class ReplaySession(Session):
    """A Session answered from a record's own probe log, never from TeX: the
    derivation re-run on it must ask for exactly the logged probes, in the
    logged order, and produce exactly the recorded fields (check_sidecar)."""

    def __init__(self, probes: list):
        super().__init__(None)
        self.logged = {}
        for entry in probes:
            self.logged[(entry[0], entry[1])] = outcome_from_entry(entry)

    def p(self, cell: str, use: str) -> dict:
        key = (cell, use)
        if key not in self.memo:
            if key not in self.logged:
                raise ReplayMiss("probe not in the log: %s %r" % key)
            self.memo[key] = self.logged[key]
            self.log.append(key)
        return self.memo[key]


# ---------------------------------------------------------------------------
# Shape discovery
# ---------------------------------------------------------------------------

def _pairs(slots: list) -> list:
    return [(s["kind"], s["payload"]) for s in slots]


def _type_search(S: Session, head: str, tail: str, cell: str, star: bool, slots: list,
                 cur: dict, lat: list, which) -> dict:
    """Greedy coordinate search for payloads that make the use compile: per
    slot (in `which`), the first lattice payload that compiles wins; else
    the first that changes the error class is kept (progress) and the next
    slot is tried. A SEARCH, not attestation: the result is attested by the
    probes the caller runs on it."""
    for _ in range(MAX_TYPE_PASSES):
        for i in which:
            if cur["o"] == "ok":
                return cur
            for ty, p in lattice_order(lat, cur):
                if p == slots[i]["payload"]:
                    continue
                trial = [dict(s) for s in slots]
                trial[i]["payload"] = p
                o = S.p(cell, build_use(head, _pairs(trial), star=star, tail=tail))
                if o["o"] == "ok":
                    slots[i]["payload"], slots[i]["argty"] = p, ty
                    return o
                if o["o"] == "fatal" and o["e"] != cur.get("e"):
                    slots[i]["payload"], slots[i]["argty"] = p, ty
                    cur = o
                    break
    # The greedy pass misses slots that are only right together (\rule's two
    # dimensions: each alone moves the error, neither alone compiles): every
    # searched slot the same lattice payload.
    if cur["o"] != "ok" and len(which) > 1:
        for ty, p in lattice_order(lat, cur):
            trial = [dict(s) for s in slots]
            for i in which:
                trial[i]["payload"] = p
            o = S.p(cell, build_use(head, _pairs(trial), star=star, tail=tail))
            if o["o"] == "ok":
                for i in which:
                    slots[i]["payload"], slots[i]["argty"] = p, ty
                return o
    return cur


EXACT_REASONS = {
    "use": "minimised payloads do not compile",
    "stop": "the canonical use followed by the sentinel fails",
    "follow": "the token after the canonical use is not the next one executed with the "
              "catcodes and group level unchanged (follow probe)",
    "drop": "dropping the last mandatory argument does not leave the name wanting one",
}


def outcome_word(o: dict) -> str:
    """One word for an outcome in a record: the named outcome, or the class."""
    return o["o"] if o["o"] in NAMED_OUTCOMES else o.get("e", o["o"])


def discover(S: Session, head: str, tail: str, cell: str, lat: list, *,
             star: bool = False) -> dict:
    """The shape of `head` (after `*` if star) in `cell`. Returns a variant
    {status: attested, slots, r, ...}, or {status: cell_fatal | unresolved,
    reason, outcome}."""
    def use(slots, stop=False):
        return build_use(head, _pairs(slots), star=star, stop=stop, tail=tail)

    def exact(slots):
        """The four attested facts of a shape: the use compiles, nothing
        more is grabbed after it, the token after it is the next one executed
        with the catcodes and group level unchanged (the follow probe: the
        sentinel only trips a macro PARAMETER scan, so \\string, \\noexpand,
        \\aftergroup, \\index or \\obeylines pass it), and without its last
        mandatory argument the name wants one. Returns None, or the first
        fact that fails and its outcome."""
        if S.p(cell, use(slots))["o"] != "ok":
            return "use", S.p(cell, use(slots))
        o = S.p(cell, use(slots, stop=True))
        if o["o"] != "ok":
            return "stop", o
        o = S.p(cell, follow_use(use(slots)))
        if o["o"] != "follow":
            return "follow", o
        ri = [i for i, s in enumerate(slots) if s["kind"] == "req"]
        if ri:
            short = [s for i, s in enumerate(slots) if i != ri[-1]]
            o = S.p(cell, use(short, stop=True))
            if o["o"] != "grab":
                return "drop", o
        return None

    slots: list = []
    rounds = 0
    while True:
        rounds += 1
        # 1. mandatory count.
        while True:
            o = S.p(cell, build_use(head, _pairs(slots), star=star, stop=True, tail=tail))
            if o["o"] == "grab":
                if len(slots) >= MAX_REQ:
                    return {"status": "unresolved",
                            "reason": "more than %d mandatory arguments" % MAX_REQ}
                slots.append({"kind": "req", "payload": TEXT, "argty": None})
                continue
            if o["o"] == "timeout":
                return {"status": "unresolved", "reason": "timeout", "outcome": o}
            break
        # 2. the use, typed.
        u = S.p(cell, use(slots))
        if u["o"] == "timeout":
            return {"status": "unresolved", "reason": "timeout", "outcome": u}
        if u["o"] != "ok" and slots and u["o"] == "fatal" and u["e"] not in MODE_CLASSES:
            u = _type_search(S, head, tail, cell, star, slots, u, lat, range(len(slots)))
        if u["o"] != "ok":
            return {"status": "cell_fatal", "use": use(slots), "outcome": u}
        # 3. exactness: no further grab.
        o = S.p(cell, use(slots, stop=True))
        if o["o"] == "grab":
            if rounds > MAX_REQ or len(slots) >= MAX_REQ:
                return {"status": "unresolved", "reason": "consumption does not settle"}
            slots.append({"kind": "req", "payload": TEXT, "argty": None})
            continue
        if o["o"] != "ok":
            return {"status": "unresolved", "reason": "the canonical use followed by the "
                    "sentinel fails", "outcome": o}
        break
    # Minimise: a slot keeps a non-text payload only if `a` there fails; that
    # failure is its negative.
    changed = False
    for i, s in enumerate(slots):
        if s["payload"] != TEXT:
            trial = [dict(x) for x in slots]
            trial[i]["payload"] = TEXT
            o = S.p(cell, use(trial))
            if o["o"] == "ok":
                s["payload"], s["argty"] = TEXT, None
                changed = True
            else:
                s["negative"] = o.get("e", o["o"])
    if changed and (S.p(cell, use(slots))["o"] != "ok" or
                    S.p(cell, use(slots, stop=True))["o"] != "ok"):
        return {"status": "unresolved", "reason": "minimised payloads do not compile"}
    r = len(slots)
    fail = exact(slots)
    if fail is not None:
        return {"status": "unresolved", "reason": EXACT_REASONS[fail[0]], "outcome": fail[1]}
    # 4. optional arguments at each position.
    req = slots
    opt_at: dict = {}
    for j in range(r + 1):
        k = 0
        state = None
        while k < MAX_OPT_RUN:
            if j < r:
                trial = req[:j] + [{"kind": "opt", "payload": TEXT}] * (k + 1) + req[j:r - 1]
                o = S.p(cell, use(trial, stop=True))
            else:
                trial = (req + [{"kind": "opt", "payload": TEXT}] * k +
                         [{"kind": "opt", "payload": cs(SENT)}])
                o = S.p(cell, use(trial))
            if o["o"] == "grab":
                k += 1
                continue
            state = False if o["o"] == "ok" else None
            break
        opt_at[j] = {"count": k, "further": state}
    full = []
    for j in range(r + 1):
        full += [{"kind": "opt", "payload": TEXT, "argty": None, "position": j}
                 for _ in range(opt_at[j]["count"])]
        if j < r:
            full.append(req[j])
    # 4b. a brace group taken if present (a peek for `{`, as \input does):
    # `\cs A{\lpstop}` grabs iff the group after the arguments is consumed;
    # without this the group would be modelled as typeset text.
    o = S.p(cell, use(full + [{"kind": "gopt", "payload": cs(SENT)}]))
    group_after = True if o["o"] == "grab" else (False if o["o"] == "ok" else None)
    if group_after:
        full.append({"kind": "gopt", "payload": TEXT, "argty": None})
    canonical = req
    opt_status = "none"
    if any(v["count"] for v in opt_at.values()) or group_after:
        u = S.p(cell, use(full))
        opt_idx = [i for i, s in enumerate(full) if s["kind"] in ("opt", "gopt")]
        if u["o"] == "fatal" and u["e"] not in MODE_CLASSES:
            u = _type_search(S, head, tail, cell, star, full, u, lat, opt_idx)
        opt_status = "untyped"
        if u["o"] == "ok":
            for i in opt_idx:
                s = full[i]
                if s["payload"] != TEXT:
                    trial = [dict(x) for x in full]
                    trial[i]["payload"] = TEXT
                    ot = S.p(cell, use(trial))
                    if ot["o"] == "ok":
                        s["payload"], s["argty"] = TEXT, None
                    else:
                        s["negative"] = ot.get("e", ot["o"])
            if exact(full) is None:
                canonical, opt_status = full, "attested"
            else:
                opt_status = "inexact"
    return {"status": "attested", "cell": cell, "star": star, "r": r,
            "slots": [dict(s) for s in canonical],
            "optional_positions": {str(j): v for j, v in opt_at.items()},
            "group_after": group_after, "optional_status": opt_status}


def star_test(S: Session, head: str, tail: str, cell: str, v: dict):
    """True if `*` after the name is a flag, False if it is taken as the first
    mandatory argument, None if the probes cannot tell."""
    req = [s for s in v["slots"] if s["kind"] == "req"]
    r = len(req)
    if r >= 1:
        o = S.p(cell, build_use(head, _pairs(req[:r - 1]), star=True, stop=True, tail=tail))
        return True if o["o"] == "grab" else (False if o["o"] == "ok" else None)
    o = S.p(cell, build_use(head, [], star=True, stop=True, tail=tail))
    if o["o"] == "grab":
        return True
    o = S.p(cell, build_use(head, [("opt", cs(SENT))], star=True, tail=tail))
    return True if o["o"] == "grab" else None


def _cells_for(S: Session, head: str, tail: str, v: dict, cells) -> dict:
    """Per cell: the canonical use's outcome; the shape checked there (in the
    base cell by discover; elsewhere nothing more is grabbed after the use
    and the follow probe passes); in a checked text-like or math cell, the
    three content witnesses of every text-like slot."""
    slots, star = v["slots"], v["star"]
    canon = build_use(head, _pairs(slots), star=star, tail=tail)
    out = {}
    for cell in cells:
        u = S.p(cell, canon)
        rec = {"allowed": "ok" if u["o"] == "ok" else "fatal"}
        if u["o"] != "ok":
            rec["error_class"] = u.get("e", u["o"])
            if u.get("m"):
                rec["message"] = u["m"]
            out[cell] = rec
            continue
        fo = S.p(cell, follow_use(canon))
        rec["follow"] = outcome_word(fo)
        if cell == v["cell"]:
            rec["shape_checked"] = fo["o"] == "follow"
        else:
            # Outside the base cell: nothing more is consumed after the use,
            # and the token after it is the next one executed.
            o1 = S.p(cell, build_use(head, _pairs(slots), star=star, stop=True, tail=tail))
            rec["shape_checked"] = o1["o"] == "ok" and fo["o"] == "follow"
        if rec["shape_checked"] and (cell in ("text", "math") or
                                     (cell == v["cell"] and cell != "preamble")):
            content = {}
            for i, s in enumerate(slots):
                if s["payload"] != TEXT:
                    continue
                res = []
                for p in (MATH_CONTENT, TEXT_CONTENT, NONE_CONTENT):
                    trial = [dict(x) for x in slots]
                    trial[i]["payload"] = p
                    res.append(outcome_word(S.p(cell, build_use(head, _pairs(trial), star=star,
                                                                tail=tail))))
                content[str(i)] = content_kind(cell, res[0], res[1], res[2])
            if content:
                rec["content"] = content
        out[cell] = rec
    return out


def _witnesses(argty: str, base: str) -> tuple:
    """The content witnesses a slot's type admits, re-run in the consumer
    document of the base cell."""
    if argty == "TyLabel":
        return (NONE_CONTENT,)
    if argty == "TyMath" or (argty == "TyInherit" and base == "math"):
        return (MATH_CONTENT,)
    return (TEXT_CONTENT,)


def _confirm_type(S: Session, head: str, tail: str, v: dict, i: int, argty: str):
    """A text-like slot's type stands only if the payloads it admits are
    also accepted when every consumer of the configuration runs (CONS_*:
    the payload may be typeset later, through the .toc/.lof/.lot, \\maketitle
    or the running heads), and, for TyLabel, if the payload is processed AT
    the use (an undefined control sequence there is fatal) rather than
    stored for later (\\title, a definer's body) or discarded (a branch not
    taken). Returns None, or the refuting probe as [cell, use, outcome]."""
    base = v["cell"]
    ccell = CONS + base

    def use_with(p):
        trial = [dict(x) for x in v["slots"]]
        trial[i]["payload"] = p
        return build_use(head, _pairs(trial), star=v["star"], tail=tail)
    for p in (TEXT,) + _witnesses(argty, base):
        o = S.p(ccell, use_with(p))
        if o["o"] != "ok":
            return [ccell, use_with(p), outcome_word(o)]
    if argty == "TyLabel":
        others = [j for j, s in enumerate(v["slots"]) if j != i and s["payload"] == TEXT]
        if len(others) >= 2:
            return ["-", "%d other text-like slots: their joint values are not attested"
                    % len(others), "joint"]
        for j in others:
            for key in CONS_KEYS:
                def keyed(p):
                    trial = [dict(x) for x in v["slots"]]
                    trial[i]["payload"], trial[j]["payload"] = p, key
                    return build_use(head, _pairs(trial), star=v["star"], tail=tail)
                # Only a legal use can refute: the control must compile.
                if S.p(ccell, keyed(TEXT))["o"] != "ok":
                    continue
                o = S.p(ccell, keyed(NONE_CONTENT))
                if o["o"] != "ok":
                    return [ccell, keyed(NONE_CONTENT), outcome_word(o)]
        o = S.p(base, use_with(STORED_CONTENT))
        if not (o["o"] == "fatal" and o.get("e") == "undefined_cs"):
            return [base, use_with(STORED_CONTENT), outcome_word(o)]
    return None


def _finish_slots(S: Session, head: str, tail: str, v: dict, cells: dict) -> list:
    """argty and long for every slot of a variant."""
    base = v["cell"]
    args = []
    for i, s in enumerate(v["slots"]):
        a = {"kind": s["kind"], "payload": s["payload"]}
        if s["payload"] == TEXT:
            kinds = {c: rec["content"][str(i)] for c, rec in cells.items()
                     if rec.get("content") and str(i) in rec["content"]}
            ty = argty_of(kinds)
            if ty is not None:
                refuted = _confirm_type(S, head, tail, v, i, ty)
                if refuted is not None:
                    a["refuted"] = {"argty": ty, "by": refuted}
                    ty = None
            a["argty"] = ty
            a["content"] = kinds
            if base != "preamble":
                trial = [dict(x) for x in v["slots"]]
                trial[i]["payload"] = PAR_CONTENT
                o = S.p(base, build_use(head, _pairs(trial), star=v["star"], tail=tail))
                a["long"] = (True if o["o"] == "ok" else
                             (False if o.get("e") == "par_in_argument" else None))
                if a["long"] is None:
                    a["par_outcome"] = outcome_word(o)
            else:
                a["long"] = None
        else:
            a["argty"] = s.get("argty")
            a["long"] = None
            if s.get("negative"):
                a["negative"] = s["negative"]
        args.append(a)
    if v["star"]:
        args.insert(0, {"kind": "star"})
    return args


def signature_for(S: Session, head: str, tail: str, lat: list, *, base_order=CELLS,
                  cells=CELLS) -> dict:
    """The whole signature of one head: variants (plain, and starred if `*` is
    a flag), each with its per-cell outcomes and typed arguments."""
    attempts = {}
    v = None
    for cell in base_order:
        d = discover(S, head, tail, cell, lat)
        if d["status"] == "attested":
            v = d
            break
        attempts[cell] = {k: d[k] for k in ("status", "reason") if k in d}
        if d.get("outcome"):
            attempts[cell]["outcome"] = outcome_word(d["outcome"])
        if d["status"] == "unresolved" and (d.get("reason") == "timeout" or
                                            d.get("reason", "").startswith("more than")):
            # Another cell would repeat the same probes to the same end.
            break
    if v is None:
        # Outcomes of the bare use in every cell: facts, but no signature.
        bare = {}
        for cell in cells:
            o = S.p(cell, head + tail)
            bare[cell] = {"allowed": "ok" if o["o"] == "ok" else "fatal"}
            if o["o"] != "ok":
                bare[cell]["error_class"] = outcome_word(o)
                if o.get("m"):
                    bare[cell]["message"] = o["m"]
        return {"status": "unresolved", "attempts": attempts, "bare_use": bare}
    star = star_test(S, head, tail, v["cell"], v)
    variants = []
    plain_cells = _cells_for(S, head, tail, v, cells)
    variants.append({"star": False, "base_cell": v["cell"], "r": v["r"],
                     "optional_positions": v["optional_positions"],
                     "optional_status": v["optional_status"],
                     "args": _finish_slots(S, head, tail, v, plain_cells),
                     "use": build_use(head, _pairs(v["slots"]), tail=tail),
                     "cells": plain_cells})
    out = {"status": "attested", "star": star, "variants": variants}
    if attempts:
        out["attempts"] = attempts
    if star:
        sv = discover(S, head, tail, v["cell"], lat, star=True)
        if sv["status"] == "attested":
            sc = _cells_for(S, head, tail, sv, cells)
            variants.append({"star": True, "base_cell": sv["cell"], "r": sv["r"],
                             "optional_positions": sv["optional_positions"],
                             "optional_status": sv["optional_status"],
                             "args": _finish_slots(S, head, tail, sv, sc),
                             "use": build_use(head, _pairs(sv["slots"]), star=True, tail=tail),
                             "cells": sc})
        else:
            out["star_variant"] = {k: sv[k] for k in ("status", "reason") if k in sv}
    return out


def environment_for(S: Session, env: str, lat: list) -> dict:
    """An environment's begin-arguments, cells and body probes."""
    head = "\\begin{%s}" % env
    rec = None
    tried = {}
    for body in ("a", "\\item a"):
        tail = "%s\\end{%s}" % (body, env)
        sig = signature_for(S, head, tail, lat, base_order=ENV_CELLS, cells=ENV_CELLS)
        if sig["status"] == "attested":
            rec = sig
            rec["body"] = body
            break
        tried[body] = sig
    if rec is None:
        return {"status": "unresolved", "tried": tried}
    v = rec["variants"][0]
    base = v["base_cell"]
    args = v["use"][len(head):len(v["use"]) - len("%s\\end{%s}" % (rec["body"], env))]
    body_probes = {}
    for key, body in ENV_BODIES:
        o = S.p(base, "%s%s%s\\end{%s}" % (head, args, body, env))
        body_probes[key] = outcome_word(o)
    rec["body_mode"] = body_mode_of(body_probes["math_content"], body_probes["text_content"])
    rec["pushes"] = sorted(k for k in ("item", "caption", "alignment") if body_probes[k] == "ok")
    rec["body_probes"] = body_probes
    return rec


# ---------------------------------------------------------------------------
# Definer rules and decl templates
# ---------------------------------------------------------------------------

def definer_targets(members: dict, contract: dict) -> dict:
    """Targets of the definer table, derived from the closed world: the first
    (by name) letters-only member of each kind, and the fresh name."""
    def first(pred):
        c = sorted(n for n, k in members.items() if re.fullmatch(r"[A-Za-z]+", n) and pred(k))
        return c[0] if c else None
    lat = dict(lattice(contract, members))
    return {"fresh": FRESH, "end_prefixed": "end" + FRESH,
            "macro": first(lambda k: k == "Macro"),
            "relax": first(lambda k: k == "Relax"),
            "primitive": first(lambda k: k == "Primitive"),
            "chardef": first(lambda k: k == "Char"),
            "counter": lat.get("TyCounter"), "environment": lat.get("TyEnvName")}


def definer_rows(t: dict) -> list:
    """The probe table: (id, context, preamble lines, body). A `body` context
    row puts its statement at the start of the body; its use (if any) after."""
    rows = []

    def add(rid, stmt, use="", prior=""):
        for ctx in ("preamble", "body"):
            if ctx == "preamble":
                rows.append({"id": rid, "context": ctx, "preamble": prior + stmt,
                             "body": (use + " x").strip()})
            else:
                rows.append({"id": rid, "context": ctx, "preamble": prior,
                             "body": (stmt + use + " x").strip()})
    for d in ("newcommand", "renewcommand", "providecommand"):
        for tk in ("fresh", "macro", "relax", "primitive", "chardef", "end_prefixed"):
            if t.get(tk):
                add("%s/%s" % (d, tk), "\\%s{\\%s}{x}" % (d, t[tk]))
    f = t["fresh"]
    add("newcommand/arity1-use", "\\newcommand{\\%s}[1]{#1}" % f, "\\%s{a}" % f)
    add("newcommand/arity1-par", "\\newcommand{\\%s}[1]{#1}" % f, "\\%s{a\\par b}" % f)
    add("newcommand*/arity1-par", "\\newcommand*{\\%s}[1]{#1}" % f, "\\%s{a\\par b}" % f)
    add("newcommand/opt-default", "\\newcommand{\\%s}[2][d]{#1#2}" % f, "\\%s{a}" % f)
    add("newcommand/opt-given", "\\newcommand{\\%s}[2][d]{#1#2}" % f, "\\%s[b]{a}" % f)
    add("newcommand/ten-params", "\\newcommand{\\%s}[10]{x}" % f)
    add("newcommand/twice", "\\newcommand{\\%s}{x}" % f, prior="\\newcommand{\\%s}{y}" % f)
    for tk in ("fresh", "environment", "macro", "relax"):
        if t.get(tk):
            add("newenvironment/%s" % tk, "\\newenvironment{%s}{[}{]}" % t[tk],
                "\\begin{%s}a\\end{%s}" % (t[tk], t[tk]) if tk == "fresh" else "")
    # \newcommand refuses an end-prefixed name, so \endlpq is made with \def.
    add("newenvironment/end-defined", "\\newenvironment{%s}{[}{]}" % f,
        prior="\\expandafter\\def\\csname end%s\\endcsname{}" % f)
    for tk in ("fresh", "environment"):
        if t.get(tk):
            add("renewenvironment/%s" % tk, "\\renewenvironment{%s}{[}{]}" % t[tk])
    add("newcounter/fresh", "\\newcounter{%s}" % f, "\\stepcounter{%s}\\the%s" % (f, f))
    if t.get("counter"):
        add("newcounter/counter", "\\newcounter{%s}" % t["counter"])
        add("newcounter/within-counter", "\\newcounter{%s}[%s]" % (f, t["counter"]))
    add("newcounter/within-unknown", "\\newcounter{%s}[%s]" % (f, "x" + f))
    add("newcounter/macro-named", "\\newcounter{%s}" % f, prior="\\newcommand{\\%s}{x}" % f)
    for d in ("setcounter", "addtocounter"):
        for tk, name in (("counter", t.get("counter")), ("unknown", "x" + f)):
            if name:
                for val in ("1", "a"):
                    add("%s/%s/%s" % (d, tk, val), "\\%s{%s}{%s}" % (d, name, val))
    # \newtheorem: four forms.
    def thm(name, form):
        c = t.get("counter") or "page"
        return {"plain": "\\newtheorem{%s}{T}" % name,
                "shared": "\\newtheorem{%s}[%s]{T}" % (name, c),
                "shared-unknown": "\\newtheorem{%s}[%s]{T}" % (name, "x" + f),
                "within": "\\newtheorem{%s}{T}[%s]" % (name, c),
                "within-unknown": "\\newtheorem{%s}{T}[%s]" % (name, "x" + f),
                "star": "\\newtheorem*{%s}{T}" % name}[form]
    for form in ("plain", "shared", "shared-unknown", "within", "within-unknown", "star"):
        add("newtheorem/%s/fresh" % form, thm(f, form), "\\begin{%s}a\\end{%s}" % (f, f))
    for form in ("plain", "star"):
        if t.get("environment"):
            add("newtheorem/%s/environment" % form, thm(t["environment"], form))
        add("newtheorem/%s/counter-first" % form, thm(f, form), "\\begin{%s}a\\end{%s}" % (f, f),
            prior="\\newcounter{%s}" % f)
        add("newtheorem/%s/macro-first" % form, thm(f, form), prior="\\newcommand{\\%s}{x}" % f)
        add("newtheorem/%s/theorem-first" % form, thm(f, form), prior=thm(f, "plain"))
    add("theoremstyle/plain", "\\theoremstyle{plain}")
    add("DeclareMathOperator/fresh", "\\DeclareMathOperator{\\%s}{x}" % f, "$\\%s$" % f)
    if t.get("macro"):
        add("DeclareMathOperator/macro", "\\DeclareMathOperator{\\%s}{x}" % t["macro"])
    return rows


def definer_doc(pre: bytes, row: dict) -> bytes:
    return (pre + (row["preamble"] + "\n").encode("utf-8") + b"\\begin{document}\n" +
            (row["body"] + "\n").encode("utf-8") + b"\\end{document}\n")


def run_definer_rows(prober: Prober, rows: list, workers: int) -> list:
    def one(row):
        jd = prober.tex.job("definer")
        doc = definer_doc(prober.pre, row)
        res = prober.tex.fixpoint(jd, doc, env="grading", recorder=False,
                                  timeout=gc.PROBE_TIMEOUT)
        shutil.rmtree(jd, ignore_errors=True)
        o = outcome_of(gc.classify_outcome(res["rc"], res["log"], res["pdf"]))
        with prober.lock:
            prober.docs.add(res["tex_sha256"])
            prober.solo += 1
            prober.runs += res["passes"]
            prober.secs += res["secs"]
        out = dict(row)
        out["outcome"] = o["o"] if o["o"] != "grab" else "fatal"
        if o["o"] != "ok":
            out["error_class"] = o.get("e", o["o"])
            if o.get("m"):
                out["message"] = o["m"]
        return out
    with ThreadPoolExecutor(max_workers=workers) as ex:
        return list(ex.map(one, rows))


# ---------------------------------------------------------------------------
# The whole sidecar
# ---------------------------------------------------------------------------

def contract_sha256(path: Path) -> str:
    return gc.sha256_bytes(path.read_bytes())


def load_kernel_file(repo: Path, contract: dict) -> dict:
    k = json.loads((repo / contract["kernel"]["file"]).read_text(encoding="utf-8"))
    if k["pin"]["fmt_sha256"] != contract["pin"]["fmt_sha256"]:
        raise SystemExit("contract_signatures: the kernel file's format is not the contract's")
    return k


def body_start_dump(tex: "gc.Tex", cfg: dict, names: list) -> tuple:
    """Body-start meanings of `names` (and, in a second round, of the robust
    inner names they point to), and the body-start catcodes, in the grading
    environment: the hints' source and the scope's letters."""
    pre = gc.preamble_tex(gc.normalize_config(cfg))
    meanings: dict = {}
    todo = [gc.name_bytes(n) for n in names]
    catcodes = None
    for _ in range(2):
        block, unw = gc.dump_block(todo, actives=False, u8_sweep=False)
        res = tex.pdflatex(tex.job("sig_dump"), pre + b"\\begin{document}\n" + block +
                           b"\\end{document}\n", env="grading")
        d = gc.parse_dump(res["log"])
        if res["rc"] != 0 or d["error"] is not None or unw:
            raise SystemExit("contract_signatures: body-start dump failed: rc=%d %s %s"
                             % (res["rc"], d["error"], unw[:3]))
        if catcodes is None:
            catcodes = d["catcodes"]
        nxt = []
        for i, nm in enumerate(todo):
            m = d["meanings"].get(i)
            meanings[gc.name_str(nm)] = m
            if m is not None:
                c = gc.classify_meaning(nm, m)
                inner = c.get("robust_inner")
                if inner and inner not in meanings:
                    nxt.append(gc.name_bytes(inner))
        todo = sorted(set(nxt))
        if not todo:
            break
    return meanings, catcodes


def scope_names(members: dict, letters: set) -> list:
    return sorted(n for n in members if user_facing(n, letters))


def environment_names(members: dict) -> list:
    return sorted(n for n in members if re.fullmatch(r"[A-Za-z]+\*?", n)
                  and ("end" + n) in members)


def check_reserved(members: dict) -> None:
    taken = [n for n in RESERVED if n in members]
    if taken:
        raise SystemExit("contract_signatures: the configuration defines the probe "
                         "design's reserved names %s; it cannot be probed with "
                         "signature version %s" % (taken, SIGNATURE_VERSION))


def _record(sig: dict, S: Session, hint: dict | None) -> dict:
    out = dict(sig)
    if hint is not None:
        out["hint"] = hint
    out["probes"] = S.evidence()
    return out


# The probe design's own premises, re-measured for every configuration probed
# (version 2): (cell, use, expected). `fatal` = any error but the follow
# probe's own; `not_follow` = anything but `follow`.
CALIBRATION = (
    ("text", TEXT_CONTENT, "ok"), ("math", TEXT_CONTENT, MATH_TYPESET),
    ("math", MATH_CONTENT, "ok"), ("text", MATH_CONTENT, TEXT_TYPESET),
    ("text", NONE_CONTENT, "fatal"), ("math", NONE_CONTENT, "fatal"),
    ("text", "\\label{%s}" % NONE_CONTENT, "ok"),
    ("text", STORED_CONTENT, "undefined_cs"),
    ("text", follow_use("\\relax"), "follow"),
    ("math", follow_use("\\relax"), "follow"),
    ("preamble", follow_use("\\relax"), "follow"),
    ("text", follow_use("\\string"), "not_follow"),
    ("text", follow_use("\\noexpand"), "not_follow"),
    ("text", follow_use("\\expandafter"), "not_follow"),
    ("text", follow_use("\\obeylines"), "lp_state_changed"),
    ("text", follow_use("\\bgroup"), "lp_state_changed"),
    (CONS + "text", TEXT, "ok"), (CONS + "vertical", TEXT, "ok"),
    (CONS + "preamble", "\\relax", "ok"),
    (CONS + "vertical", "\\section[%s]{x}" % NONE_CONTENT, "fatal"),
    (CONS + "preamble", "\\title{%s}" % MATH_CONTENT, "fatal"),
    (CONS + "text", "\\markboth{%s}{c}" % NONE_CONTENT, "fatal"),
)


def calibration_meets(outcome: str, expect: str) -> bool:
    """Does a logged outcome word meet a CALIBRATION expectation?"""
    if expect in ("ok", "follow"):
        return outcome == expect
    if expect == "not_follow":
        return outcome != "follow"
    if expect == "fatal":
        return outcome not in ("ok", "follow", "timeout", "grab")
    return outcome == expect


def calibrate(prober) -> list:
    """Run CALIBRATION; returns [cell, use, outcome(, message), expected] per
    row and refuses the configuration if any premise fails."""
    S = Session(prober)
    rows = []
    for cell, use, expect in CALIBRATION:
        S.p(cell, use)
    for (cell, use, expect), ent in zip(CALIBRATION, S.evidence()):
        rows.append(ent + [expect] if len(ent) > 3 else ent + [None, expect])
    bad = [r for r in rows if not calibration_meets(r[2], r[-1])]
    if bad:
        raise SystemExit("contract_signatures: the probe design's premises fail for this "
                         "configuration: %s" % bad)
    return rows


def hint_agreement(rec: dict) -> str | None:
    """Did the \\meaning hint predict the attested mandatory count?"""
    h = rec.get("hint") or {}
    if rec.get("status") != "attested" or "arity" not in h:
        return None
    return "agree" if h["arity"] == rec["variants"][0]["r"] else "disagree"


def probe_one_name(prober: Prober, name: str, lat: list, hint: dict | None,
                   cells=CELLS) -> dict:
    S = Session(prober)
    sig = signature_for(S, cs(name), "", lat, cells=cells)
    return _record(sig, S, hint)


def run_batches(prober: Prober, records: dict, workers: int) -> dict:
    """Triage: each record's solo probes (batchable ones) once more in one
    batch; returns agreement counts and the disagreeing probes."""
    def one(item):
        key, rec = item
        items = [(i, p[0], p[1]) for i, p in enumerate(rec["probes"]) if batchable(p[0], p[1])]
        pol = prober.batch(items) if items else {}
        res = []
        for i, p in enumerate(rec["probes"]):
            cell, use, solo = p[0], p[1], p[2]
            if not batchable(cell, use):
                res.append((key, cell, use, "skipped", None))
                continue
            b = pol.get(i, "unreached")
            s = "ok" if solo == "ok" else ("timeout" if solo == "timeout" else "fatal")
            res.append((key, cell, use, s, b))
        return res
    agree = disagree = inconclusive = skipped = 0
    dis = []
    with ThreadPoolExecutor(max_workers=workers) as ex:
        for part in ex.map(one, sorted(records.items())):
            for key, cell, use, s, b in part:
                if s == "skipped":
                    skipped += 1
                elif s == "timeout" or b in ("timeout", "unreached"):
                    inconclusive += 1
                elif s == b:
                    agree += 1
                else:
                    disagree += 1
                    dis.append([key, cell, use, s, b])
    return {"agree": agree, "disagree": disagree, "inconclusive": inconclusive,
            "skipped": skipped, "disagreements": dis}


def batchable(cell: str, use: str) -> bool:
    """Batch triage covers the plain cells only: a consumer cell's document
    and the follow probe's error are not a segment of a shared run."""
    return not cell.startswith(CONS) and not _mentions(FOLLOW, use)


def summarize(sigs: dict, envs: dict) -> dict:
    st = {"attested": 0, "unresolved": 0}
    base: dict = {}
    argty: dict = {}
    cells: dict = {}
    star = {"true": 0, "false": 0, "unknown": 0}
    hint = {"agree": 0, "disagree": 0}
    refuted: dict = {}
    unchecked = 0
    reasons: dict = {}
    probes = 0
    for rec in sigs.values():
        probes += len(rec["probes"])
        st[rec["status"]] += 1
        if rec["status"] != "attested":
            for att in rec.get("attempts", {}).values():
                r = att.get("reason", att["status"])
                reasons[r] = reasons.get(r, 0) + 1
            continue
        star["true" if rec["star"] else ("false" if rec["star"] is False else "unknown")] += 1
        h = hint_agreement(rec)
        if h:
            hint[h] += 1
        for v in rec["variants"]:
            base[v["base_cell"]] = base.get(v["base_cell"], 0) + (0 if v["star"] else 1)
            for a in v["args"]:
                if a["kind"] == "star":
                    continue
                t = a.get("argty") or "untyped"
                argty[t] = argty.get(t, 0) + 1
                if a.get("refuted"):
                    t = a["refuted"]["argty"]
                    refuted[t] = refuted.get(t, 0) + 1
            if v["star"]:
                continue
            for c, r in v["cells"].items():
                k = "%s:%s" % (c, r["allowed"])
                cells[k] = cells.get(k, 0) + 1
                if r["allowed"] == "ok" and not r.get("shape_checked"):
                    unchecked += 1
    env_st = {"attested": 0, "unresolved": 0}
    for rec in envs.values():
        probes += len(rec["probes"])
        env_st[rec["status"]] += 1
    return {"names": len(sigs), "status": st, "base_cell": dict(sorted(base.items())),
            "argty": dict(sorted(argty.items())), "cells": dict(sorted(cells.items())),
            "star": star, "hint_arity_vs_attested": hint, "environments": len(envs),
            "environment_status": env_st, "solo_probes": probes,
            "types_refuted_by_consumers_or_storage": dict(sorted(refuted.items())),
            "accepting_cells_shape_unchecked": unchecked,
            "unresolved_attempt_reasons": dict(sorted(reasons.items()))}


# Names every sampled reproducibility check regenerates (MEDIUM-2 of the
# 2026-09-27 review: a sample seeded by the configuration alone drew the same
# 60 names forever). The reviewers' adversarial names: each once passed a
# version-1 check it should not have, or is the case a fix is about.
ADVERSARIAL_NAMES = ("string", "noexpand", "meaning", "aftergroup", "expandafter", "do",
                     "index", "glossary", "enddocument", "stop", "ifdefined", "partokenname",
                     "obeylines", "obeyspaces", "verb", "section", "input", "pmod", "title",
                     "thanks", "markboth", "caption", "label", "cite", "IfBlankTF",
                     "addcontentsline", "ensuremath")
ADVERSARIAL_ENVS = ("math", "itemize", "equation", "center")


def signature_sample(names, seed: str, n: int, fixed=ADVERSARIAL_NAMES) -> list:
    """A reproducibility sample: n names drawn with `seed` (the caller
    rotates it, e.g. with the commit), plus every `fixed` name present."""
    pool = sorted(names)
    pick = random.Random(seed).sample(pool, min(n, len(pool)))
    return sorted(set(pick) | (set(fixed) & set(pool)))


def generate_signatures(tex: "gc.Tex", repo: Path, contract_path: Path, *, workers: int,
                        names: list | None = None, batch: bool = True,
                        report: dict | None = None, environments: list | None = None,
                        definer: bool = False) -> dict:
    report = report if report is not None else {}
    contract = json.loads(contract_path.read_text(encoding="utf-8"))
    if not contract.get("complete"):
        raise SystemExit("contract_signatures: %s is incomplete; its name set is not a "
                         "closed world" % contract_path)
    pin = gc.get_pin(tex, tex.image)
    if pin["fmt_sha256"] != contract["pin"]["fmt_sha256"] or pin["arch"] != contract["pin"]["arch"]:
        raise SystemExit("contract_signatures: the image's format or architecture is not the "
                         "contract's")
    kernel = load_kernel_file(repo, contract)
    members = closed_world_members(kernel["names"], contract)
    check_reserved(members)
    cfg = contract["configuration"]
    t0 = time.monotonic()
    # The scope's letters are the body-start catcodes, read from TeX; then the
    # body-start meanings of the scope (the hints' source), which must agree
    # with the contract's membership.
    _, catcodes = body_start_dump(tex, cfg, [])
    letters = letters_of(catcodes)
    scope = scope_names(members, letters)
    meanings, _ = body_start_dump(tex, cfg, sorted(set(scope) | set(environment_names(members))))
    mismatch = sorted(n for n in scope if meanings.get(n) is None)
    reasons = []
    if mismatch:
        reasons.append("%d names of the contract's closed world are undefined at body start in "
                       "the grading environment: %s" % (len(mismatch), mismatch[:5]))
    subset = names is not None
    if subset:
        unknown = [n for n in names if n not in members]
        if unknown:
            raise SystemExit("contract_signatures: not members of the closed world: %s" % unknown)
        todo = sorted(set(names))
    else:
        todo = scope
    report["dump_secs"] = round(time.monotonic() - t0, 1)
    lat = lattice(contract, members)
    prober = Prober(tex, cfg)
    calibration = calibrate(prober)

    t1 = time.monotonic()
    sigs: dict = {}
    with ThreadPoolExecutor(max_workers=workers) as ex:
        futs = {n: ex.submit(probe_one_name, prober, n, lat, meaning_hint(n, meanings))
                for n in todo}
        for n, f in futs.items():
            sigs[n] = f.result()
    report["names_secs"] = round(time.monotonic() - t1, 1)
    t2 = time.monotonic()
    envs: dict = {}
    env_todo = (environment_names(members) if not subset else
                sorted(e for e in (environments or []) if e in environment_names(members)))
    def env_one(e):
        S = Session(prober)
        return _record(environment_for(S, e, lat), S, None)
    with ThreadPoolExecutor(max_workers=workers) as ex:
        for e, rec in zip(env_todo, ex.map(env_one, env_todo)):
            envs[e] = rec
    report["environments_secs"] = round(time.monotonic() - t2, 1)
    t3 = time.monotonic()
    targets = definer_targets(members, contract)
    rows = run_definer_rows(prober, definer_rows(targets), workers) if (definer or not subset) \
        else []
    report["definer_secs"] = round(time.monotonic() - t3, 1)
    solo = {"probes": prober.solo, "runs": prober.runs}
    report["solo_engine_secs_total"] = round(prober.secs, 1)
    triage = None
    if batch:
        t4 = time.monotonic()
        allrec = dict(("name:" + n, r) for n, r in sigs.items())
        allrec.update(("env:" + e, r) for e, r in envs.items())
        triage = run_batches(prober, allrec, workers)
        report["batch_secs"] = round(time.monotonic() - t4, 1)
    doc_digest = gc.sha256_bytes("\n".join(sorted(prober.docs)).encode("utf-8"))
    out = {
        "schema": SIG_SCHEMA,
        "generator": {"tool": "scripts/tools/gen_contract.py signatures",
                      "module": "scripts/tools/contract_signatures.py",
                      "version": gc.GENERATOR_VERSION,
                      "signature_version": SIGNATURE_VERSION},
        "contract": contract_path.relative_to(repo).as_posix(),
        "contract_sha256": contract_sha256(contract_path),
        "config_key": contract["config_key"],
        "configuration": cfg,
        "pin": contract["pin"],
        "scope": ({"names": "subset", "requested": todo, "environments": env_todo,
                   "definer_rules": bool(rows)} if subset else
                  {"names": "every member of the closed world a body can type (%d)" % len(scope),
                   "environments": "every X with \\X and \\endX members, X letters with an "
                                   "optional trailing *",
                   "definer_rules": "the probe table (definer_rows)"}),
        "letters": [b for b in sorted(letters)],
        "cells": {c: (CELL_DOC.get(c) or "in the preamble; body `x`") for c in CELLS},
        "sentinel": "\\outer\\def%s{}" % cs(SENT),
        "follow_probe": {"use": follow_use("<use>"), "definitions": FOLLOW_DEF,
                         "passes_on": "! %s" % FOLLOW_OK},
        "witnesses": {"math": MATH_CONTENT, "text": TEXT_CONTENT, "none": NONE_CONTENT,
                      "stored": STORED_CONTENT, "long": PAR_CONTENT},
        "consumers": {"preamble_before_use": CONS_TITLE.strip(), "body_before": CONS_PRE.strip(),
                      "body_after": CONS_POST.strip(), "other_slot_keys": list(CONS_KEYS)},
        "calibration": calibration,
        "lattice": [{"argty": ty, "payload": p} for ty, p in lat],
        "companion_files": sorted(COMPANIONS),
        "protocol": ("solo: %s -interaction=nonstopmode -halt-on-error, a fresh directory "
                     "holding the companion files, the grading environment, the oracle's "
                     "pass protocol (to the first rc 0 in at most %d runs, then one "
                     "confirming run), coreutils timeout %ds per run; outcome ok = rc 0 and "
                     "a PDF on the last run, grab = the sentinel's `Forbidden control "
                     "sequence found while scanning use of`, follow = the follow probe's "
                     "`! LPFOLLOW.`, else the error class of the first `!` line with TeX's "
                     "location context"
                     % (gc._oracle.ENGINE_PDFLATEX, gc.MAX_PASSES, gc.PROBE_TIMEOUT)),
        "signatures": sigs,
        "environments": envs,
        "definer_targets": targets,
        "definer_rules": rows,
        "solo": solo,
        "batch_triage": triage,
        "summary": summarize(sigs, envs),
        "consistent": not reasons,
        "inconsistent_reasons": reasons,
        "provenance": {"probe_documents": len(prober.docs),
                       "probe_documents_sha256": doc_digest},
    }
    report["total_secs"] = round(time.monotonic() - t0, 1)
    return out


# ---------------------------------------------------------------------------
# Consistency of a committed sidecar (pure; check_gen_contract_parsers.py)
# ---------------------------------------------------------------------------

def check_variant(v: dict, probes: list, head: str, tail: str) -> list:
    """The implications the probe log must support for one attested variant
    (a readable restatement of what replay() re-derives in full). Returns
    the failed ones."""
    out = {(p[0], p[1]): p[2] for p in probes}
    bad = []
    base = v["base_cell"]
    slots = [(a["kind"], a["payload"]) for a in v["args"] if a["kind"] != "star"]
    star = v["star"]
    canon = build_use(head, slots, star=star, tail=tail)
    if canon != v["use"]:
        bad.append("use %r is not the canonical use of its args %r" % (v["use"], canon))
    if out.get((base, canon)) != "ok":
        bad.append("canonical use does not compile in the base cell: %r" % out.get((base, canon)))
    if out.get((base, build_use(head, slots, star=star, stop=True, tail=tail))) != "ok":
        bad.append("canonical use + sentinel is not recorded ok in the base cell")
    if out.get((base, follow_use(canon))) != "follow":
        bad.append("the follow probe of the canonical use is not recorded as passing in the "
                   "base cell")
    req_idx = [i for i, s in enumerate(slots) if s[0] == "req"]
    if req_idx:
        short = [s for i, s in enumerate(slots) if i != req_idx[-1]]
        if out.get((base, build_use(head, short, star=star, stop=True, tail=tail))) != "grab":
            bad.append("dropping the last mandatory argument is not recorded as a grab")
    if len(req_idx) != v["r"]:
        bad.append("r=%d but %d mandatory args" % (v["r"], len(req_idx)))
    for c, rec in v["cells"].items():
        o = out.get((c, canon))
        if o is None or (o == "ok") != (rec["allowed"] == "ok"):
            bad.append("cell %s: allowed=%s but the probe log says %r" % (c, rec["allowed"], o))
        if rec.get("shape_checked") and out.get((c, follow_use(canon))) != "follow":
            bad.append("cell %s: shape_checked without a passing follow probe" % c)
    for a in v["args"]:
        if a.get("argty") and a["payload"] != TEXT and not a.get("negative"):
            bad.append("typed slot %r without its negative" % a)
    return bad


def replay(rec: dict, head: str, lat: list, *, env: str | None = None) -> list:
    """Re-derive a whole record from its own probe log, with no TeX: the
    derivation (signature_for, or environment_for) is run again on a
    ReplaySession. It must ask for exactly the logged probes in the logged
    order, and every field it produces (status, shape, star and the starred
    variant, per-cell outcomes, shape_checked, follow, content kinds, argty
    and its refutation, long, negatives, optional positions, body mode,
    pushes, attempts, bare-use outcomes) must equal the recorded one.
    Returns problems."""
    S = ReplaySession(rec["probes"])
    try:
        if env is not None:
            new = environment_for(S, env, lat)
        else:
            new = signature_for(S, head, "", lat, cells=CELLS)
    except ReplayMiss as e:
        return ["replay: %s" % e]
    bad = []
    logged = [(p[0], p[1]) for p in rec["probes"]]
    if S.log != logged:
        extra = len(logged) - len(S.log)
        bad.append("replay: the derivation asks for %d probes, the log holds %d%s"
                   % (len(S.log), len(logged), " (unused entries)" if extra > 0 else
                      " (a different order)"))
    got = {k: v for k, v in rec.items() if k not in ("probes", "hint")}
    new = json.loads(json.dumps(new))
    if new != got:
        keys = sorted(set(new) | set(got))
        diff = [k for k in keys if new.get(k) != got.get(k)]
        detail = ""
        for k in diff:
            if k == "variants" and isinstance(new.get(k), list) and isinstance(got.get(k), list):
                for i, (a, b) in enumerate(zip(new[k], got[k])):
                    for f in sorted(set(a) | set(b)):
                        if a.get(f) != b.get(f):
                            detail = " (variant %d field %s)" % (i, f)
                            break
                    if detail:
                        break
                if not detail and len(new[k]) != len(got[k]):
                    detail = " (%d variants re-derived, %d recorded)" % (len(new[k]), len(got[k]))
        bad.append("replay: recorded %s differ from the re-derivation%s" % (diff, detail))
    return bad


def check_definer_row(row: dict) -> list:
    """A definer row's outcome is its own solo probe (no log to replay); what
    the row can say about itself is checked: the outcome vocabulary, and a
    fatal row's class is the class of its message."""
    bad = []
    o = row.get("outcome")
    if o not in ("ok", "fatal", "timeout"):
        return ["outcome %r" % o]
    if o == "ok" and ("error_class" in row or "message" in row):
        bad.append("ok with an error class or message")
    if o == "fatal":
        m = row.get("message")
        if not row.get("error_class"):
            bad.append("fatal without an error class")
        elif m is not None and row["error_class"] != refine_class(gc.classify_error(m), m):
            bad.append("error class %r is not the class of its message %r"
                       % (row["error_class"], m))
        elif m is None and row["error_class"] not in ("no_pdf", "no_error_line"):
            bad.append("fatal without a message")
    return bad


def check_sidecar(side: dict, contract_bytes: bytes | None) -> list:
    """Every claim of a sidecar that its own probe log can confirm, and its
    binding to the contract. Returns problems."""
    bad = []
    if side.get("schema") != SIG_SCHEMA:
        return ["schema %r" % side.get("schema")]
    if side["generator"].get("signature_version") != SIGNATURE_VERSION:
        bad.append("signature_version %r is not current %r"
                   % (side["generator"].get("signature_version"), SIGNATURE_VERSION))
    if contract_bytes is None:
        bad.append("its contract %s is missing" % side.get("contract"))
    elif gc.sha256_bytes(contract_bytes) != side["contract_sha256"]:
        bad.append("stale: its contract's sha256 differs from contract_sha256")
    # The probe design's premises, as calibrated for this configuration.
    cal = side.get("calibration") or []
    if [(r[0], r[1], r[-1]) for r in cal] != [tuple(c) for c in CALIBRATION]:
        bad.append("calibration: the recorded rows are not this version's CALIBRATION")
    for r in cal:
        if not calibration_meets(r[2], r[-1]):
            bad.append("calibration: %s %r gave %r, expected %s" % (r[0], r[1], r[2], r[-1]))
    wit = side.get("witnesses", {})
    if (wit.get("math"), wit.get("text"), wit.get("none")) != (MATH_CONTENT, TEXT_CONTENT,
                                                               NONE_CONTENT):
        bad.append("witnesses: recorded %r are not this version's" % wit)
    lat = [(x["argty"], x["payload"]) for x in side.get("lattice", [])]
    for n, rec in side["signatures"].items():
        if rec["status"] == "attested":
            for v in rec["variants"]:
                for p in check_variant(v, rec["probes"], cs(n), ""):
                    bad.append("%s: %s" % (n, p))
        elif rec["status"] != "unresolved":
            bad.append("%s: status %r" % (n, rec["status"]))
        seen = [(p[0], p[1]) for p in rec["probes"]]
        if len(seen) != len(set(seen)):
            bad.append("%s: a probe is logged twice" % n)
        for p in replay(rec, cs(n), lat):
            bad.append("%s: %s" % (n, p))
    for e, rec in side.get("environments", {}).items():
        if rec["status"] == "attested":
            tail = "%s\\end{%s}" % (rec["body"], e)
            for v in rec["variants"]:
                for p in check_variant(v, rec["probes"], "\\begin{%s}" % e, tail):
                    bad.append("env %s: %s" % (e, p))
        for p in replay(rec, "", lat, env=e):
            bad.append("env %s: %s" % (e, p))
    rows = side.get("definer_rules", [])
    if rows != [dict(r, **{k: x[k] for k in x if k not in r})
                for r, x in zip(definer_rows(side["definer_targets"]), rows)] or \
            len(rows) != len(definer_rows(side["definer_targets"])):
        bad.append("definer_rules: the rows are not the probe table of its targets")
    for r in rows:
        for p in check_definer_row(r):
            bad.append("definer %s/%s: %s" % (r.get("id"), r.get("context"), p))
    s = summarize(side["signatures"], side.get("environments", {}))
    if s != side["summary"]:
        bad.append("summary does not match the entries")
    if side.get("consistent") != (not side.get("inconsistent_reasons")):
        bad.append("consistent flag disagrees with its reasons")
    return bad


# ---------------------------------------------------------------------------
# On-demand API (M3's use-based attestation)
# ---------------------------------------------------------------------------

def _cache_path(cache: Path, csha: str, name: str) -> Path:
    return (cache / csha[:16] / ("v" + SIGNATURE_VERSION) /
            (hashlib.sha256(name.encode("utf-8")).hexdigest()[:24] + ".json"))


def probe_names(contract_path: Path, names: list, *, cells=CELLS, cache: Path | None = None,
                workers: int = 6, work: Path | None = None, repo: Path = gc.REPO,
                report: dict | None = None) -> dict:
    """Signatures of `names` in `cells` for the contract at contract_path.
    Cached per (contract sha256, name, cell) under `cache`: a cached name
    whose record lacks a requested cell runs only that cell's probes (its
    shape, from the cache, is reused). Returns {name: record}; a record's
    `cells` holds exactly the requested cells. A name outside the closed
    world is returned as {status: undefined} (E1), with no probe."""
    report = report if report is not None else {}
    cache = Path(cache or CACHE).expanduser()
    contract_path = Path(contract_path)
    contract = json.loads(contract_path.read_text(encoding="utf-8"))
    if not contract.get("complete"):
        raise SystemExit("contract_signatures: the contract is incomplete")
    csha = contract_sha256(contract_path)
    kernel = load_kernel_file(repo, contract)
    members = closed_world_members(kernel["names"], contract)
    check_reserved(members)
    out: dict = {}
    todo = []
    for n in names:
        if n not in members:
            out[n] = {"status": "undefined"}
            continue
        p = _cache_path(cache, csha, n)
        rec = json.loads(p.read_text(encoding="utf-8")) if p.exists() else None
        if rec is not None and rec.get("name") == n:
            have = set(rec.get("cells_done", []))
            if set(cells) <= have:
                out[n] = _select_cells(rec, cells)
                report[n] = "cache"
                continue
        todo.append((n, rec))
    if not todo:
        return out
    lat = lattice(contract, members)
    with gc.Tex(gc.read_image(repo), work) as tex:
        pin = gc.get_pin(tex, tex.image)
        if pin["fmt_sha256"] != contract["pin"]["fmt_sha256"]:
            raise SystemExit("contract_signatures: the image's format is not the contract's")
        meanings, _ = body_start_dump(tex, contract["configuration"], [n for n, _ in todo])
        prober = Prober(tex, contract["configuration"])
        calibrate(prober)

        def one(item):
            n, old = item
            want = sorted(set(cells) | set((old or {}).get("cells_done", [])),
                          key=CELLS.index)
            S = Session(prober)
            if old is not None:
                # Replay the cached probe log into the memo: the search is
                # deterministic, so already-run probes are not run again.
                for entry in old["probes"]:
                    S.memo[(entry[0], entry[1])] = outcome_from_entry(entry)
                    S.log.append((entry[0], entry[1]))
            sig = signature_for(S, cs(n), "", lat, cells=tuple(want))
            rec = _record(sig, S, meaning_hint(n, meanings))
            rec["name"] = n
            rec["contract_sha256"] = csha
            rec["cells_done"] = want
            p = _cache_path(cache, csha, n)
            p.parent.mkdir(parents=True, exist_ok=True)
            tmp = p.with_suffix(".tmp")
            tmp.write_text(json.dumps(rec, sort_keys=True, ensure_ascii=False), encoding="utf-8")
            tmp.replace(p)
            return n, rec
        with ThreadPoolExecutor(max_workers=workers) as ex:
            for n, rec in ex.map(one, todo):
                out[n] = _select_cells(rec, cells)
                report[n] = "probed"
        report["solo_probes_run"] = prober.solo
    return out


def _select_cells(rec: dict, cells) -> dict:
    r = {k: v for k, v in rec.items() if k != "cells_done"}
    if r.get("status") == "attested":
        r["variants"] = [dict(v, cells={c: v["cells"][c] for c in cells if c in v["cells"]})
                         for v in r["variants"]]
    elif r.get("status") == "unresolved":
        r["bare_use"] = {c: r["bare_use"][c] for c in cells if c in r.get("bare_use", {})}
    return r


# ---------------------------------------------------------------------------
# decl_templates: \newtheorem per owner combination
# ---------------------------------------------------------------------------

DECL_OWNERS = (("kernel", []), ("amsthm", ["amsthm"]), ("amsthm+thmtools", ["amsthm", "thmtools"]))


def decl_forms(counter: str) -> list:
    z = DECL_FRESH
    return [("plain", "\\newtheorem{%s}{Zzq}" % z),
            ("shared", "\\newtheorem{%s}[%s]{Zzq}" % (z, counter)),
            ("within", "\\newtheorem{%s}{Zzq}[%s]" % (z, counter)),
            ("star", "\\newtheorem*{%s}{Zzq}" % z)]


def decl_collisions(counter: str) -> list:
    """(id, prior definition, declaration, body): what the declaration does
    when the name is already taken, per kind of prior definition, and the
    requirements of its counter arguments."""
    z = DECL_FRESH
    decl = "\\newtheorem{%s}{Zzq}" % z
    use = "\\begin{%s}a\\end{%s}" % (z, z)
    return [
        ("none", "", decl, use),
        ("prior-counter", "\\newcounter{%s}" % z, decl, use),
        ("prior-macro", "\\newcommand{\\%s}{x}" % z, decl, use),
        ("prior-environment", "\\newenvironment{%s}{}{}" % z, decl, use),
        ("prior-theorem", "\\newtheorem{%s}{Z}" % z, decl, use),
        ("prior-counter-lemma", "\\newcounter{lemma}", "\\newtheorem{lemma}{Lemma}",
         "\\begin{lemma}a\\end{lemma}"),
        ("shared-unknown-counter", "", "\\newtheorem{%s}[x%s]{Zzq}" % (z, z), use),
        ("within-unknown-counter", "", "\\newtheorem{%s}{Zzq}[x%s]" % (z, z), use),
        ("star-unused", "", "\\newtheorem*{%s}{Zzq}" % z, ""),
    ]


def _names_diff(base: dict, with_decl: dict) -> dict:
    b, w = base["defined_names"], with_decl["defined_names"]
    added = sorted(n for n in w if n not in b and w[n]["kind"] != "Undefined")
    removed = sorted(n for n in b if n not in w)
    changed = sorted(n for n in w if n in b and w[n]["meaning_sha256"] != b[n]["meaning_sha256"])
    undefined = sorted(n for n in w if n not in b and w[n]["kind"] == "Undefined")
    # `defines` is the declaration's template: the names that carry the
    # declared name. Every other name it first defines is `incidental`:
    # scratch (\@let@token, \thmt@tmp, \reserved@d) or a side effect on
    # something that exists already (\cl@enumi, the reset list of the
    # `within` counter). Version 1 listed both as `defines` (review, LOW).
    return {"defines": {n: gc.short_kind(w[n]) for n in added if DECL_FRESH in n},
            "incidental_defines": {n: gc.short_kind(w[n]) for n in added if DECL_FRESH not in n},
            "changes": changed, "reverts_to_kernel": removed, "undefines_kernel_names": undefined}


def generate_decl_templates(tex: "gc.Tex", kernel: dict, pin: dict, *, workers: int,
                            report: dict) -> dict:
    """For each owner combination: the base configuration's contract, then one
    contract per \\newtheorem form with the form as a preamble definer; the
    template is the difference of the two closed worlds (both must be
    complete), plus a collision matrix of solo probes."""
    owners = {}
    for owner, pkgs in DECL_OWNERS:
        t0 = time.monotonic()
        base_cfg = {"class": "article", "preamble": [{"package": p} for p in pkgs]}
        base = gc.generate(base_cfg, tex, pin, kernel, [], {})
        counters = sorted(n for n, d in base.get("counters", {}).items()
                          if d.get("the") and re.fullmatch(r"[A-Za-z]+", n))
        counter = counters[0]
        forms = {}
        for form, decl in decl_forms(counter):
            cfg = {"class": "article", "preamble": base_cfg["preamble"] + [{"definer": decl}]}
            c = gc.generate(cfg, tex, pin, kernel, [], {})
            entry = {"declaration": decl, "config_key": c["config_key"],
                     "complete": bool(c["complete"] and base["complete"])}
            if c["load_outcome"]["status"] != "ok":
                entry["load_outcome"] = {k: c["load_outcome"].get(k)
                                         for k in ("status", "error_class", "message")}
            else:
                entry.update(_names_diff(base, c))
            if not entry["complete"]:
                entry["incomplete_reasons"] = (c.get("incomplete_reasons") or [])[:3]
            forms[form] = entry
        prober = Prober(tex, base_cfg)
        rows = [{"id": rid, "context": "preamble", "preamble": prior + decl,
                 "body": (use + " x").strip()}
                for rid, prior, decl, use in decl_collisions(counter)]
        matrix = run_definer_rows(prober, rows, workers)
        owners[owner] = {"configuration": gc.normalize_config(base_cfg),
                         "config_key": base["config_key"], "base_complete": base["complete"],
                         "counter_argument": counter, "forms": forms,
                         "collisions": matrix,
                         "probe_documents_sha256": gc.sha256_bytes(
                             "\n".join(sorted(prober.docs)).encode("utf-8"))}
        report["decl_%s_secs" % owner] = round(time.monotonic() - t0, 1)
    return {"schema": DECL_SCHEMA,
            "generator": {"tool": "scripts/tools/gen_contract.py decl-templates",
                          "module": "scripts/tools/contract_signatures.py",
                          "version": gc.GENERATOR_VERSION,
                          "signature_version": SIGNATURE_VERSION},
            "declaration": "newtheorem",
            "pin": {k: pin[k] for k in ("image", "arch", "engine_banner", "fmt_sha256",
                                         "tlpdb_sha256")},
            "method": ("per owner combination (the base configuration article plus the "
                       "owner packages): a complete contract of the base, and one per "
                       "form with the declaration as a preamble definer; `defines` etc. "
                       "are the difference of the two closed worlds, `defines` the names "
                       "that carry the declared name (zzq) and `incidental_defines` every "
                       "other name first defined (scratch, or a side effect such as a "
                       "counter's reset list). `collisions`: solo "
                       "probes (grading environment, the oracle's pass protocol) of the "
                       "declaration after a prior definition of its name, and of unknown "
                       "counter arguments"),
            "owners": owners}


# ---------------------------------------------------------------------------
# CLI (called from gen_contract.py)
# ---------------------------------------------------------------------------

def sidecar_path(repo: Path, contract_path: Path) -> Path:
    return repo / SIG_DIR / contract_path.name


def cmd_signatures(a) -> int:
    repo = Path(a.repo).resolve()
    cpath = Path(a.contract).resolve()
    report: dict = {}
    names = [n for n in a.names.split(",") if n] if a.names else None
    with gc.Tex(gc.read_image(repo), Path(a.work).expanduser() if a.work else None) as tex:
        side = generate_signatures(tex, repo, cpath, workers=a.workers, names=names,
                                   batch=not a.no_batch, report=report)
    out = Path(a.out) if a.out else sidecar_path(repo, cpath)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(gc.canonical_json(side), encoding="utf-8")
    report["out"] = str(out)
    report["bytes"] = out.stat().st_size
    report["summary"] = side["summary"]
    report["solo"] = side["solo"]
    if side["batch_triage"]:
        report["batch"] = {k: side["batch_triage"][k] for k in ("agree", "disagree",
                                                                 "inconclusive")}
    report["consistent"] = side["consistent"]
    print(json.dumps(report, indent=1, sort_keys=True), file=sys.stderr)
    return 0


def cmd_probe_names(a) -> int:
    report: dict = {}
    cells = tuple(c for c in (a.cells or ",".join(CELLS)).split(",") if c)
    bad = [c for c in cells if c not in CELLS]
    if bad:
        raise SystemExit("contract_signatures: unknown cells %s" % bad)
    res = probe_names(Path(a.contract), [n for n in a.names.split(",") if n], cells=cells,
                      cache=Path(a.sig_cache).expanduser(), workers=a.workers,
                      work=Path(a.work).expanduser() if a.work else None,
                      repo=Path(a.repo).resolve(), report=report)
    print(json.dumps(res, indent=1, sort_keys=True, ensure_ascii=False))
    print(json.dumps(report, sort_keys=True), file=sys.stderr)
    return 0


def cmd_decl_templates(a) -> int:
    repo = Path(a.repo).resolve()
    report: dict = {}
    with gc.Tex(gc.read_image(repo), Path(a.work).expanduser() if a.work else None) as tex:
        pin = gc.get_pin(tex, tex.image)
        kernel = gc.load_kernel(tex, pin, Path(a.cache).expanduser(), False, report)
        out = generate_decl_templates(tex, kernel, pin, workers=a.workers, report=report)
    p = Path(a.out) if a.out else repo / DECL_DIR / "newtheorem.json"
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(gc.canonical_json(out), encoding="utf-8")
    report["out"] = str(p)
    print(json.dumps(report, indent=1, sort_keys=True), file=sys.stderr)
    return 0
