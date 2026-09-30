#!/usr/bin/env python3
"""Gate: the strict kernel L_S0 and its evidence describe each other (ADR-012 M2).

Pure: no TeX, no docker, no build. It reads the Coq sources, the committed
extraction and the committed, oracle-graded artefacts, and fails when they no
longer belong together:

  1. PROBE-TAGGED SEMANTICS (design §C.3 review rule: "every Runs constructor
     cites its probe family ids"). Every constructor of the inductive `Runs`
     in proofs/Strict/Semantics.v carries a `probe S0/<constructor>` comment,
     and corpora/strict_s0/rule_probes.json has that family with at least one
     graded probe, every one of which agrees with the oracle, and at least one
     whose run actually used the constructor. A constructor without a family,
     or a family whose documents all bypass it, is a rule nobody has tested.
  2. FRESH EVIDENCE. The rule probes, the differential and the signature file
     each record the sha256 of the extraction they ran
     (latex-parse/strict/strict_kernel_extracted.ml) and of the kernel/contract
     files they read; each must equal the committed file's. A semantics change
     without re-running the evidence fails here, the extraction's own drift
     from the proofs is check_extract_identity.py's (proof CI).
  3. NO DISAGREEMENT. The rule probes and the differential report 0
     disagreements and 0 oracle infrastructure failures, and the differential
     graded at least MIN_DIFFERENTIAL documents (the M2 phase-1 floor; ADR-012
     decision 6: any disagreement blocks a release).
  4. SIGNATURES ARE THE GENERATOR'S. Every signature names a member of the
     article closed world (contract_wf), and the candidate set is exactly the
     documented selection rule's (sha256 order of the closed world's control
     words minus par/begin/end, first n): nothing was added or dropped by
     hand.
  5. NO NAME IN COQ. Semantics.v, Contract.v, Bridge.v hold no string literal
     outside comments, and Decide.v only one-character literals (the fixed
     catcode classes); a control-word name can reach the kernel only through
     the contract parameter.
  6. EVERY ADMITTED NAME IS INERT (RULE R-INERT above, C-85, C-92, C-96):
     the signature file records the meaning at body start of every candidate
     and of every name and active character their expansion texts may hold
     (every reading of the printed text, against the closed world); the
     closure must be complete, every meaning in it of a kind the rule
     classifies, and `inertness_violation` must be None for every admitted
     name.
  7. EVERY BRANCH OF EVERY LOOK-AHEAD AND DISJUNCTIVE PREMISE IS EXERCISED
     (C-85). The rule probes' BRANCH MATRIX must cover every cell
     head|token|follower|tail that the grammar allows: every innermost frame
     (from Semantics.v `Inductive frame`, plus the empty stack) x every token
     class (from Syntax.v `Inductive tok`; a control word by each behaviour
     the admitted signatures have in that mode, and undefined) and, for each
     token whose `Runs` rule reads the NEXT token (derived from the
     constructors' conclusions and premises, not listed by hand), x every
     follower class (every token class, a control word by each admitted
     signature pair, undefined, and end of file) x, for ^ and _ in math,
     whether the tail noad already has the script. A cell is covered by an
     AGREEING probe, or, when membership excludes it (a script without a
     character or group argument, Decide.v `scripts_ok`), by a probe the
     extracted decider places outside the tier.
  8. SIGNATURE EVIDENCE IS COMPLETE. Every admitted name has a grade for
     every family of REQUIRED_SIGNATURE_FAMILIES (base, follower,
     display-follower, repetition, bounds); its display-follower grades are
     pdfTeX's "Display math should end with $$" (not transparent, C-85); its
     repetition and bound grades compile in every mode its signature does
     not make fatal; and the last interleaving round of the generator graded
     documents in text and math with 0 disagreements.
  9. CAPACITY BOUNDS (C-86, C-94). Decide.v defines max_groups, max_tokens
     and max_name and pins them (Examples) at the values this gate and the
     generators use; the ACCOUNT is pinned token for token (CAPACITY_ACCOUNT:
     a frame is one TeX group, an argument frame its command's g; the bound
     holds over every state of the run, Decide.peak; `bounded` is the token,
     name and group bounds together); the rule probes' BOUND family (the
     structure at the bounds) agrees with the oracle and its BOUND-OUT
     documents are outside the tier; every admitted argument signature's run
     behaviour carries its TeX groups, equal to the generator's stage-G
     measure.
 10. FAITHFUL'S BODY IS PINNED (OPEN-121 final review, MEDIUM-1).
     Bridge.v's `Definition Faithful` must be, token for token (comments stripped, whitespace normalised),
     FAITHFUL_BODY: oracle_ok (render d) <-> Runs ... Compiles. The pinned
     STATEMENT of strict_ready_iff_pdflatex (check_print_assumptions.py)
     cannot see this: a reviewer redefined Faithful as `oracle_ok (render d)
     <-> decide C d = ProvenReady` -- which makes the corollary a tautology
     -- and coqc printed the same statement, Closed. Independently of the
     pin, the body must mention `Runs` and none of `decide`/`run`/`step`
     (the decider must never be smuggled into the premise), and Bridge.v may
     define nothing but Faithful (no shadowing Definition/Notation/...).
     That definer scan reads every Coq SENTENCE (a `Module` on the Require
     line is a sentence too, re-review MEDIUM-1) and admits only the pinned
     Require sentence, Faithful and the two bridge Corollaries. Since the
     second re-review (HIGH-1, C-88) the scan strips control prefixes
     (Time, Timeout n, Redirect, attributes, ...) first, the comment
     stripper lexes strings inside comments as Coq does, Bridge.v may hold
     no double quote at all, and the WHOLE comment-stripped code of
     Bridge.v is pinned sentence by sentence (BRIDGE_SENTENCES, an
     allow-list: a sentence no keyword names still fails).
     check_print_assumptions.py pins the ELABORATED body too (coqc `Print`).
 11. THE CAPACITY ACCOUNT IS PROBED (C-94). corpora/strict_s0/capacity.json
     (measure_strict_capacity.py, fresh against the committed extraction and
     signature files) holds, for EVERY ordered pair of frame kinds the
     extracted model can stack (strict_decide.exe --frame-pairs: a search
     through the extracted step over every token of the grammar), a stream
     at exactly max_groups groups that agrees with pdfTeX with the pair on
     the peak's stack, one at max_groups + 1 outside the tier, and pdfTeX's
     own first overflow inside the window the account predicts. The frame
     kinds and the search alphabet are checked against the extracted
     `frame` and `tok` types (derived from the model, not listed here), every
     admitted command's argument frame is in some pair, the measured margin
     is positive, and every other capacity pdfTeX reports is at most half
     used at the bounds.
 12. REUSE PROVENANCE (LOW-2 of the C-94 review). A grade reused by any
     evidence file comes from a file committed to this repository, recorded
     by path, commit and sha256 (verified when the commit is present): never
     a /tmp path or a local grade store.
 13. NO ADMITTED NAME READS THE CLOCK (RULE R-CLOCK below, OPEN-118 known
     limit (b)): no admitted name -- phase-1 name or argument command -- is,
     or expands through its recorded meaning closure (read as R-INERT reads
     it) to, a run-dependent primitive (CLOCK_PRIMITIVES: \\year/\\month/
     \\day/\\time and pdfTeX's random, timer and file-date primitives) or a
     date-dependent name of the kernel file, so oracle_ok on the fragment
     cannot depend on the day it is graded (MEASURED clock-independent, see
     the rule's comment).

Run: python3 scripts/tools/check_strict_kernel.py [--repo .]
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

MIN_DIFFERENTIAL = 3000
DIFFERENTIAL = "corpora/strict_s0/differential_v4.json"
# ADR-012 step 2, slice A: the one-argument commands' signatures
ARG_SIGNATURES = "corpora/contracts/strict/article-s1-arg-signatures.json"
REQUIRED_ARG_FAMILIES = [
    "A-T-ALONE", "A-T-EMPTY", "A-T-SPACE", "A-T-MID", "A-T-PAR", "A-T-GROUP", "A-T-UNDEF",
    "A-T-PARARG", "A-T-BLANKARG", "A-T-PARLATE", "A-T-DD", "A-T-BRK", "A-T-BRKOPEN",
    "A-T-DOLLAR", "A-T-SUP", "A-T-SHIFT", "A-T-NEST", "A-T-NESTPAR", "A-T-STRAY",
    "A-T-NOEND",
    "A-M-ALONE", "A-M-EMPTY", "A-M-SCRIPTS", "A-M-TAIL", "A-M-DOLLAR", "A-M-SUP",
    "A-M-UNDEF", "A-M-PARARG", "A-M-DD", "A-M-BRK", "A-M-DISPLAY", "A-M-GROUP",
    "A-M-SCRIPTARG", "A-M-NEST", "A-M-PAREN", "A-M-BRACKETS",
    "A-D-FOLLOW",
    "A-R-TEXT", "A-R-TEXT-ALT", "A-R-PARS", "A-R-GROUPS", "A-R-MATH", "A-R-FORMULAS",
    "A-R-DISPLAYS", "A-R-NEST-TEXT", "A-R-NEST-MATH", "A-R-BIG-TEXT", "A-R-BIG-MATH",
    "A-R-BIG-ARG",
] + [f"A-F{w}-{k}" for w in "TM" for k in (
    "CHARS", "OPEN", "CLOSE", "PAR", "BLANK", "DOLLAR", "DISPLAY", "MOPEN", "BOPEN",
    "SUP", "UNDEF", "SPACE", "SELF")] + ["A-FT-END", "A-FT-EOF", "A-FM-MCLOSE", "A-FM-BCLOSE"]
ARG_REPETITION = {"text": ["A-R-TEXT", "A-R-TEXT-ALT", "A-R-PARS", "A-R-GROUPS",
                           "A-R-NEST-TEXT", "A-R-BIG-TEXT", "A-R-BIG-ARG"],
                  "math": ["A-R-MATH", "A-R-FORMULAS", "A-R-DISPLAYS", "A-R-NEST-MATH",
                           "A-R-BIG-MATH"]}
REQUIRED_SIGNATURE_FAMILIES = [
    # base (generator version 2)
    "T-ALONE", "T-MID", "T-GROUP", "T-PAR", "T-DOLLAR", "T-SUP", "T-SPACE",
    "M-ALONE", "M-MID", "M-GROUP", "M-RESET", "M-SUB", "M-DISPLAY", "T-UNDEF",
    "M-PAR",
    # follower (version 3)
    "FT-CHARS", "FT-OPEN", "FT-CLOSE", "FT-PAR", "FT-DISPLAY", "FT-MOPEN",
    "FT-BOPEN", "FT-MCLOSE", "FT-BCLOSE", "FT-SUB", "FT-EOF",
    "FM-CHARS", "FM-OPEN", "FM-CLOSE", "FM-PAR", "FM-SPACE", "FM-MOPEN",
    "FM-BOPEN", "FM-MCLOSE", "FM-BCLOSE", "FM-UNDEF", "FM-DDOLLAR",
    "FM-GDOLLAR", "FM-END", "FM-EOF",
    # display follower (version 3)
    "D-FOLLOW-DOLLAR", "D-FOLLOW-CHAR", "D-FOLLOW-BRACKET", "D-FOLLOW-GROUP",
    # repetition and bounds (version 3)
    "R-TEXT", "R-TEXT-ALT", "R-PARS", "R-GROUPS", "R-MATH", "R-MATH-ALT",
    "R-FORMULAS", "R-DISPLAYS", "R-NEST-TEXT", "R-NEST-MATH",
    "R-NEST-EACH-TEXT", "R-NEST-EACH-MATH", "R-BIG-TEXT", "R-BIG-MATH",
]
DISPLAY_FOLLOWER_FAMILIES = ["D-FOLLOW-DOLLAR", "D-FOLLOW-CHAR",
                             "D-FOLLOW-BRACKET", "D-FOLLOW-GROUP"]
REPETITION_TEXT = ["R-TEXT", "R-TEXT-ALT", "R-PARS", "R-GROUPS",
                   "R-NEST-TEXT", "R-NEST-EACH-TEXT", "R-BIG-TEXT"]
REPETITION_MATH = ["R-MATH", "R-MATH-ALT", "R-FORMULAS", "R-DISPLAYS",
                   "R-NEST-MATH", "R-NEST-EACH-MATH", "R-BIG-MATH"]
STRUCTURAL = {"par", "begin", "end"}

# The kernel's capacity bounds (proofs/Strict/Decide.v, C-86, C-94). Checked
# below against the Coq source: the definitions and their pinning Examples.
# MAX_GROUPS bounds TeX's grouping level (Decide.groups over every state of
# the run), not a brace depth (C-94).
MAX_GROUPS = 200
MAX_TOKENS = 200 * 100
MAX_NAME = 100
MAX_MEM = 20000 * 100
# C-100: the dimension account's bound, in whole points (Decide.v max_dim)
MAX_DIM = 80 * 100
CAPACITY = "corpora/strict_s0/capacity.json"

# ---------------------------------------------------------------------------
# RULE R-INERT (design §I.4, correction C-85): a control word that is not
# INERT is never admitted, whatever its probes say. Probes attest behaviour in
# the contexts they build; a name whose effect reaches beyond its own
# occurrence (it changes how later input is read, skipped, expanded, traced or
# written, or leaves a condition open) can behave differently in a context no
# probe built. The rule is applied to \meaning at body start, recorded by
# gen_strict_signatures.py from the pinned image for every candidate AND for
# every name its expansion texts reach (the closure below), by this module's
# `inertness_violation`, in the generator (stage 0) and again by this gate
# for every admitted name.
#
# A token t "is" primitive p when the recorded meaning of t is \p with p one
# of the engine's primitives (kernel file); so a name \let to a primitive is
# that primitive, and a primitive name LaTeX redefined (\input, \end) is not.
# A name is NOT inert when
#   (P) it is a primitive of a class of NON_INERT_PRIMITIVE_CLASSES, or any
#       conditional (a primitive whose name begins with "if", or else, fi,
#       or, unless), or a tracing parameter (a primitive beginning "tracing");
#   (C) it is \let to a character of a STRUCTURAL category (begin-group,
#       end-group, math shift, alignment tab, macro parameter, superscript,
#       subscript), or it is an active character or undefined;
#   (R) it is a register (\count, \dimen, \skip, \muskip, \toks): as a
#       command it starts an assignment that reads the following tokens;
#   (M) it is a macro and
#       - its expansion text is EMPTY (transparent to expansion: the
#         display-$ look-ahead of Semantics.v sees through it), or
#       - its expansion text has unbalanced conditionals (tokens beginning
#         with "if", or \unless, against \fi), or
#       - its expansion CLOSURE reaches a primitive of MACRO_STATE_CHANGERS
#         (code tables, interaction, input/output, diagnostics and tracing,
#         deferred execution, \immediate, \scantokens, and since C-98 the
#         definitions \def ... \let and the assignments \global, \advance,
#         \multiply, \divide, \setbox). The closure follows
#         every control sequence of an expansion text to its recorded
#         meaning, transitively, and every character that is ACTIVE at body
#         start to the active character's meaning.
#
# HOW AN EXPANSION TEXT IS READ (correction C-96; C-92 was the first
# instance). \meaning prints a token list as text, and until C-96 the closure
# took `\\([A-Za-z@]+)` of that text as the control words: `\hook_use:nnw`
# was read as `\hook` (recorded meaning "undefined"), and the walk stopped
# there silently, so no expl3 code was ever screened (six admitted names reach
# \par, whose code is expl3: paragraph hooks and a conditional). The text
# follows TeX's printing rules exactly (tex.web print_cs): a control sequence
# of two or more characters is printed as \name and ONE space, a
# one-character name c as \c, followed by a space only when c is a letter at
# print time. A name may itself hold spaces and backslashes, and \meaning
# hides category codes, so the text of one token list can have several
# readings (the ambiguity recorded in D-3). The closure therefore takes
# EVERY reading: at each backslash, every name of the closed world (the
# kernel's names, updated by the configuration) that the printing rule
# allows there, and the longest printed name even outside the closed world
# (dumped like any other: an undefined name has meaning "undefined"); and a
# printed backslash may also be a CHARACTER token (\@backslashchar's text is
# one backslash), which runs no code. Every name the walk reaches must have a
# meaning of a kind the rule classifies (`meaning_kind`: a macro, a
# primitive, undefined, a character, a register or \chardef-like constant,
# a font); a meaning of any other shape is UNRESOLVABLE, and a name whose
# closure holds one is REJECTED, never passed silently. Every printed character that
# may be an active character at body start (the lexical contract's catcode
# 13: `~`, the ^^ notation of control characters, every byte of a non-ASCII
# character) is followed to that active character's meaning (key
# "active:<code>"). Over-reading only adds names to a closure, so it can
# reject more names, never admit more.
#         The closure is a screen, not a proof (design §I.4): it does not
#         evaluate \csname targets or conditionals; the probes (follower,
#         repetition, interleaving) remain the behavioural check.
# ---------------------------------------------------------------------------
NON_INERT_PRIMITIVE_CLASSES = {
    "expansion control": {
        "expandafter", "noexpand", "futurelet", "csname", "endcsname", "the",
        "unexpanded", "detokenize", "scantokens", "string", "meaning", "number",
        "romannumeral", "fontname", "jobname", "primitive", "pdfprimitive",
        "lastnamedcs", "begincsname", "topmark", "firstmark", "botmark",
        "splitfirstmark", "splitbotmark", "topmarks", "firstmarks", "botmarks",
        "splitfirstmarks", "splitbotmarks", "pdfstrcmp", "pdfescapestring",
        "pdfescapename", "pdfescapehex", "pdfunescapehex", "expanded",
    },
    "prefix": {"global", "long", "outer", "protected", "immediate"},
    "interaction": {"batchmode", "nonstopmode", "scrollmode", "errorstopmode",
                    "interactionmode"},
    "input/output": {
        "write", "openout", "closeout", "openin", "closein", "read", "readline",
        "message", "errmessage", "special", "input", "endinput", "pdfliteral",
        "pdfobj", "pdfannot", "pdfoutline", "pdfdest", "pdfinfo", "pdfcatalog",
        "pdfnames", "pdftrailer", "pdfximage", "pdfrefximage",
    },
    "diagnostic": {"show", "showbox", "showlists", "showthe", "showgroups",
                   "showifs", "showtokens", "errorcontextlines", "showboxdepth",
                   "showboxbreadth"},
    "code table / reading state": {"catcode", "lccode", "uccode", "sfcode",
                                   "mathcode", "delcode", "endlinechar",
                                   "escapechar", "newlinechar"},
    "deferred execution": {"aftergroup", "afterassignment", "everypar",
                           "everymath", "everydisplay", "everyhbox",
                           "everyvbox", "everyjob", "everycr", "everyeof",
                           "output"},
    "definition": {"def", "edef", "gdef", "xdef", "let", "chardef",
                   "mathchardef", "countdef", "dimendef", "skipdef",
                   "muskipdef", "toksdef", "font", "letcharcode"},
    "job end": {"end", "dump"},
}
MACRO_STATE_CHANGERS = (
    NON_INERT_PRIMITIVE_CLASSES["interaction"]
    | NON_INERT_PRIMITIVE_CLASSES["input/output"]
    | NON_INERT_PRIMITIVE_CLASSES["diagnostic"]
    | NON_INERT_PRIMITIVE_CLASSES["code table / reading state"]
    | NON_INERT_PRIMITIVE_CLASSES["deferred execution"]
    | {"immediate", "scantokens"}
    # C-98 LOW-4 of the round-2 review: a definition or an assignment the
    # expansion makes (\gdef\mbox{x}, \thicklines' \let, \narrower's
    # \advance) changes what a LATER token means or measures: the screen
    # rejects it rather than model it (3 phase-1 names left, measured)
    | NON_INERT_PRIMITIVE_CLASSES["definition"]
    | {"global", "advance", "multiply", "divide", "setbox"}
)
STRUCTURAL_CHARACTER_MEANINGS = (
    "begin-group character", "end-group character", "math shift character",
    "alignment tab character", "macro parameter character",
    "superscript character", "subscript character",
)
_MACRO = re.compile(r"^((?:\\(?:long|protected|outer) ?)*)macro:(.*?)->(.*)$", re.S)
_REGISTER = re.compile(r"^\\(count|dimen|skip|muskip|toks)\d+$")
# One reading of a printed control sequence may be at most this long (the
# closed world's longest name has 90 characters).
MAX_PRINTED_NAME = 128
ACTIVE_PREFIX = "active:"
# The characters that are active at body start in `article` (the lexical
# contract's catcode 13: the control characters but tab, line feed and
# return, `~`, and every byte from 128); used when no contract is given.
DEFAULT_ACTIVE = frozenset(list(range(1, 9)) + [11, 12] + list(range(14, 32))
                           + [126] + list(range(128, 256)))


def _is_letter(c: str) -> bool:
    return c.isascii() and c.isalpha()


def expansion_text(meaning: str) -> str | None:
    m = _MACRO.match(meaning)
    return m.group(3) if m else None


def body_readings(text: str, world: set[str], active=DEFAULT_ACTIVE,
                  occurrences: list | None = None) -> tuple[set[str], list[str]]:
    """(every name and active character a printed expansion text may hold,
    the backslashes that have no reading). See HOW AN EXPANSION TEXT IS
    READ above. `occurrences`, when given, receives the readings of each
    backslash in order (one list per control sequence printed)."""
    names: set[str] = set()
    unresolved: list[str] = []
    covered = -1  # the end of the longest reading of an earlier backslash
    n = len(text)
    i = 0
    while i < n:
        c = text[i]
        if c == "\\":
            cands, longest = [], None
            for ln in range(1, min(MAX_PRINTED_NAME, n - i - 1) + 1):
                nm = text[i + 1:i + 1 + ln]
                if ln == 1:
                    ok = (not _is_letter(nm)) or text[i + 2:i + 3] == " "
                else:
                    ok = text[i + 1 + ln:i + 2 + ln] == " "
                if not ok:
                    continue
                if longest is None and ln >= 2 and " " not in nm:
                    longest = nm
                if nm in world or (ln == 1 and not _is_letter(nm)):
                    cands.append(nm)
            if longest is not None:
                cands.append(longest)
            # with no reading as a control sequence, the backslash is a
            # character token (catcode other), or part of an earlier reading
            if cands and occurrences is not None:
                occurrences.append(cands)
            for nm in cands:
                names.add(nm)
                covered = max(covered, i + 1 + len(nm))
            i += 1
            continue
        # a character that may be active at body start
        if c == "^" and text[i:i + 2] == "^^" and i + 2 < n:
            h = text[i + 2:i + 4]
            if re.fullmatch(r"[0-9a-f]{2}", h):
                names.add(f"{ACTIVE_PREFIX}{int(h, 16)}")
            o = ord(text[i + 2])
            if o < 128:
                names.add(f"{ACTIVE_PREFIX}{(o + 64) % 128 if o < 64 else o - 64}")
        elif ord(c) in active and c.isascii():
            names.add(f"{ACTIVE_PREFIX}{ord(c)}")
        elif not c.isascii():
            for b in c.encode("utf-8", "surrogateescape"):
                if b in active:
                    names.add(f"{ACTIVE_PREFIX}{b}")
        i += 1
    return {x for x in names if not x.startswith(ACTIVE_PREFIX)
            or int(x[len(ACTIVE_PREFIX):]) in active}, unresolved


_KIND_PATTERNS = (
    ("undefined", re.compile(r"^undefined$")),
    ("character", re.compile(r"^(the letter|the character|begin-group character|"
                             r"end-group character|math shift character|"
                             r"alignment tab character|macro parameter character|"
                             r"superscript character|subscript character|"
                             r"blank space|active character) ", re.S)),
    ("constant", re.compile(r"^\\(char|mathchar|count|dimen|skip|muskip|toks|"
                            r"attribute)\"?[0-9A-F]+$")),
    ("font", re.compile(r"^select font ")),
)


def meaning_kind(meaning: str | None, primitives: set[str]) -> str | None:
    """The kind of a recorded meaning, or None when the rule cannot classify
    it (C-96: an unresolvable step, which rejects every name reaching it)."""
    if meaning is None:
        return None
    if _MACRO.match(meaning):
        return "macro"
    if primitive_of(meaning, primitives) is not None:
        return "primitive"
    for k, pat in _KIND_PATTERNS:
        if pat.search(meaning):
            return k
    return None


def body_tokens(meaning: str, world: set[str] | None = None,
                active=DEFAULT_ACTIVE) -> list[str] | None:
    """The names (and active characters) a macro's expansion text may hold,
    by every reading (None if the meaning is not a macro). Without a
    `world`, only the longest printed names are read."""
    t = expansion_text(meaning)
    if t is None:
        return None
    got, _ = body_readings(t, world or set(), active)
    return sorted(got)


def closed_world(repo: Path) -> set[str]:
    """The article configuration's closed world at body start: the kernel's
    names, updated by the contract's defined_names (the loader's rule)."""
    contract = json.loads((Path(repo) / "corpora/contracts/article.json").read_text())
    kern = json.loads((Path(repo) / contract["kernel"]["file"]).read_text())
    world = set(kern["names"])
    for n, v in contract["defined_names"].items():
        (world.discard if v.get("kind") == "Undefined" else world.add)(n)
    return world


def active_chars(repo: Path) -> frozenset:
    """The characters of catcode 13 at body start (the lexical contract)."""
    lx = json.loads((Path(repo) / "corpora/contracts/strict/article-s0-lexical.json"
                     ).read_text())
    return frozenset(i for i, c in enumerate(lx["catcodes"]) if c == 13)


def _conditional(p: str) -> bool:
    return p.startswith("if") or p in {"else", "fi", "or", "unless"}


def primitive_of(meaning: str | None, primitives: set[str]) -> str | None:
    if meaning and meaning.startswith("\\") and meaning[1:] in primitives:
        return meaning[1:]
    return None


def closure(name: str, meanings: dict[str, str], world: set[str] | None = None,
            active=DEFAULT_ACTIVE, primitives: set[str] | None = None
            ) -> tuple[set[str], set[str], dict[str, str]]:
    """(the names reached from `name` through expansion texts, by every
    reading; the names met without a recorded meaning; the reached names
    whose meaning `meaning_kind` cannot classify, with that meaning -- only
    when `primitives` is given)."""
    world = world or set()
    seen, missing, unresolved, stack = set(), set(), {}, [name]
    while stack:
        x = stack.pop()
        if x in seen:
            continue
        if x not in meanings:
            missing.add(x)
            continue
        seen.add(x)
        if primitives is not None and meaning_kind(meanings[x], primitives) is None:
            unresolved[x] = meanings[x]
        t = expansion_text(meanings[x])
        if t is None:
            continue
        stack.extend(body_readings(t, world, active)[0])
    return seen, missing, unresolved


def inertness_violation(name: str, meanings: dict[str, str],
                        primitives: set[str], world: set[str] | None = None,
                        active=DEFAULT_ACTIVE) -> str | None:
    """None when `name` is inert by RULE R-INERT, else the reason. Raises
    KeyError when the recorded closure of meanings is incomplete. `world` is
    the closed world at body start (the readings of printed names, C-96)."""
    meaning = meanings[name]
    p = primitive_of(meaning, primitives)
    if p is not None:
        if _conditional(p):
            return f"conditional primitive \\{p}"
        if p.startswith("tracing"):
            return f"tracing parameter \\{p}"
        for cls, names in NON_INERT_PRIMITIVE_CLASSES.items():
            if p in names:
                return f"{cls} primitive \\{p}"
        return None
    if any(meaning.startswith(c) for c in STRUCTURAL_CHARACTER_MEANINGS):
        return f"let to a structural character ({meaning})"
    if meaning.startswith("active character") or meaning == "undefined":
        return f"not a command of the fragment ({meaning})"
    if _REGISTER.match(meaning):
        return f"register ({meaning}): as a command it reads an assignment"
    text = expansion_text(meaning)
    if text is None:
        return None
    if text.strip() == "":
        return "macro with an empty expansion text (transparent to expansion)"
    reached, missing, unresolved = closure(name, meanings, world, active, primitives)
    if missing:
        raise KeyError(f"meaning closure of {name} is incomplete: {sorted(missing)[:5]}")
    # the conditionals of the name's OWN text: a control sequence one of whose
    # readings is a conditional primitive (\\if..., \\unless) or \\fi (a name
    # beginning "if" counts too, as before C-96)
    occ: list = []
    body_readings(text, world or set(), active, occ)

    def is_(cands, pred):
        return any(pred(c, primitive_of(meanings.get(c), primitives) or "") for c in cands)
    opens = sum(1 for cs in occ if is_(cs, lambda c, q: c.startswith("if") or c == "unless"
                                       or (q.startswith("if") or q == "unless")))
    closes = sum(1 for cs in occ if is_(cs, lambda c, q: c == "fi" or q == "fi"))
    if opens != closes:
        return (f"macro whose expansion text has unbalanced conditionals "
                f"({opens} if-tokens, {closes} \\fi)")
    if unresolved:
        x = sorted(unresolved)[0]
        return (f"its expansion closure reaches \\{x}, whose meaning the rule cannot "
                f"classify ({unresolved[x][:60]!r}; C-96: unresolvable, rejected)")
    for x in sorted(reached):
        t_ = expansion_text(meanings[x])
        for t in (sorted(body_readings(t_, world or set(), active)[0]) if t_ is not None else ()):
            q = primitive_of(meanings.get(t), primitives)
            if q is not None and (q in MACRO_STATE_CHANGERS or q.startswith("tracing")):
                via = "" if x == name else f" via \\{x}"
                return f"expansion reaches \\{q}{via} (state-changing)"
    return None


_MACRO_PARAMS = re.compile(r"^((?:\\(?:long|protected|outer) ?)*)macro:(.*?)->", re.S)


def arg_candidates(meanings: dict[str, str], admitted1: set[str]) -> list[str]:
    """The slice-A selection rule (gen_strict_arg_signatures.candidates): the
    control words of the closed world minus par/begin/end and the phase-1
    admitted names, whose meaning at body start -- through one robust wrapper
    to the inner name "X " -- is a macro with parameter text exactly #1."""
    out = []
    for n in sorted(meanings):
        if not re.fullmatch(r"[A-Za-z]+", n) or n in STRUCTURAL or n in admitted1:
            continue
        m = meanings[n]
        if m == f"macro:->\\protect \\{n}  ":
            m = meanings.get(n + " ", "")
        mm = _MACRO_PARAMS.match(m)
        if mm and mm.group(2) == "#1":
            out.append(n)
    return out


# ---------------------------------------------------------------------------
# RULE R-CLOCK (OPEN-118 known limit (b), measured 2026-09-28): no admitted
# name reads the clock. The oracle imposes SOURCE_DATE_EPOCH=0, which pins the
# PDF's dates only; \year, \month, \day and \time follow the container's clock
# (FORCE_SOURCE_DATE is not set), so a name that reads them could make
# oracle_ok depend on the day of grading, and Faithful (bytes -> outcome)
# would not be a property of the bytes. MEASURED: every probe-family document
# of the 130 admitted names, the interleaving documents, the rule probes and
# 600 differential documents grade identically (rc, PDF, first error, line,
# and the PDF's bytes with its dates and /ID removed) under the protocol and
# under two forced dates that differ in every field (1971-02-03 04:05 and
# 2049-11-28 23:59, FORCE_SOURCE_DATE=1). This rule keeps that true for the
# next signature file: a name is a CLOCK READER when
#   * its recorded meaning is one of CLOCK_PRIMITIVES (itself or \let to it),
#   * the expansion closure (`closure`, the same as R-INERT's) meets a token
#     whose recorded meaning is one of them, or
#   * it or its closure names one of the kernel file's `date_dependent_names`
#     (gen_contract.py measured those as differing between two dates: expl3's
#     \c_sys_year_int and friends).
# Only the four primitives are listed by hand; everything that reaches them is
# derived from the recorded meanings, as R-INERT's closure is. The same screen
# limit applies: a name of non-letter characters is not followed (§I.4), and a
# name BUILT at run time (\csname year\endcsname) is not followed either — a
# known limit, closed only by ADR-013's token-exact closure (instrument I1).
# ---------------------------------------------------------------------------
# Review of the clock branch (MEASURED 2026-09-29, protocol environment, the
# same document five times): the four date primitives are not pdfTeX's only
# per-run inputs. \pdfrandomseed is seeded from the real time on EVERY run
# (246203157, 1742160, 176765163 on three runs) even with FORCE_SOURCE_DATE=1,
# so \pdfuniformdeviate/\pdfnormaldeviate differ per run; \pdfelapsedtime is
# a timer (44510, 61401, 60100); \pdffilemoddate returns a file's real
# modification time and FORCE_SOURCE_DATE does not pin it. \pdfcreationdate
# is pinned by SOURCE_DATE_EPOCH=0 and is left out. The rule therefore covers
# every primitive whose value is not a function of the input bytes.
CLOCK_PRIMITIVES = frozenset((
    "year", "month", "day", "time",
    "pdfrandomseed", "pdfsetrandomseed", "pdfuniformdeviate",
    "pdfnormaldeviate", "pdfelapsedtime", "pdfresettimer", "pdffilemoddate",
))


def clock_violation(name: str, meanings: dict[str, str], primitives: set[str],
                    date_names=(), world: set[str] | None = None,
                    active=DEFAULT_ACTIVE) -> str | None:
    """None when `name` reads no clock by RULE R-CLOCK, else the reason.
    Raises KeyError when the recorded closure of meanings is incomplete.
    The closure and the tokens of each expansion text are read exactly as
    R-INERT reads them (every reading, C-96), so the clock screen sees every
    name R-INERT's closure sees (merge of OPEN-118 (b) into C-94..C-98)."""
    p = primitive_of(meanings[name], primitives)
    if p in CLOCK_PRIMITIVES:
        return f"it is the run-dependent primitive \\{p}"
    if name in date_names:
        return "it is a date-dependent name of the kernel file"
    reached, missing, _ = closure(name, meanings, world, active)
    if missing:
        raise KeyError(f"meaning closure of {name} is incomplete: {sorted(missing)[:5]}")
    dated = [re.compile(r"\\" + re.escape(d) + r"(?![A-Za-z@_:])") for d in date_names]
    dset = set(date_names)
    for x in sorted(reached):
        via = "" if x == name else f" via \\{x}"
        t_ = expansion_text(meanings[x])
        toks = sorted(body_readings(t_, world or set(), active)[0]) if t_ is not None else ()
        for t in toks:
            q = primitive_of(meanings.get(t), primitives)
            if q in CLOCK_PRIMITIVES:
                return f"expansion reaches the run-dependent primitive \\{q}{via}"
        for t in toks:
            if t in dset:
                return f"expansion reaches the date-dependent name \\{t}{via}"
        for d, rx in zip(date_names, dated):
            if t_ is not None and rx.search(t_):
                return f"expansion reaches the date-dependent name \\{d}{via}"
    return None


def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def strip_coq_comments(text: str) -> str:
    """The code of a Coq file with its comments removed, lexed as Coq lexes
    it: a `"` opens a string both in code and INSIDE a comment, and a comment
    delimiter inside such a string does not count (`""` inside a string is
    an escaped quote, which toggling handles). The OPEN-121 re-review 2
    (HIGH-1) hid a Definition between `(* "(*" *)` and `(* "*)" *)`: Coq
    reads two comments and a Definition, a lexer that ignores strings reads
    one comment. A string left open at the end of the file (Coq rejects the
    file) keeps everything after it as code, so nothing is hidden."""
    out, depth, i, in_str = [], 0, 0, False
    while i < len(text):
        c = text[i]
        if in_str:
            if c == '"':
                in_str = False
            if depth == 0:
                out.append(c)
            i += 1
        elif c == '"':
            in_str = True
            if depth == 0:
                out.append(c)
            i += 1
        elif text.startswith("(*", i):
            depth += 1
            i += 2
        elif text.startswith("*)", i) and depth:
            depth -= 1
            i += 2
        else:
            if depth == 0:
                out.append(c)
            i += 1
    if depth:
        # An unterminated comment: Coq rejects the file; report its text as
        # code rather than hide it.
        return text
    return "".join(out)


# ------------------------------------------------------ check 7 helpers ---

def _block(text: str, header: str) -> str:
    i = text.index(header)
    j = text.index(".\n", i)
    return text[i:j]


def _balanced(text: str, i: int) -> int:
    """Index just past the parenthesised/bracketed group starting at i."""
    open_, close = text[i], {"(": ")", "[": "]"}[text[i]]
    depth = 0
    for k in range(i, len(text)):
        if text[k] == open_:
            depth += 1
        elif text[k] == close:
            depth -= 1
            if depth == 0:
                return k + 1
    raise ValueError("unbalanced")


def lookahead_tokens(sem: str) -> dict[str, set[str]]:
    """Runs constructor -> the head token constructors whose rule READS
    beyond its own token: its conclusion names a second explicit token, ends
    the stream right after it ([t]), or a premise inspects the rest. A
    premise that only hands the rest on (the recursive Runs, and since slice
    A the Stops and Scans continuations, which read the rest by their own
    rules and have their own cells) is not an inspection."""
    body = sem[sem.index("Inductive Runs"):]
    parts = re.split(r"^\|\s*(R_\w+)\s*:", body, flags=re.M)
    out: dict[str, set[str]] = {}
    for name, blk in zip(parts[1::2], parts[2::2]):
        code = strip_coq_comments(blk)
        k = code.rfind("Runs C (mkState")
        i = code.index("(mkState", k)
        j = _balanced(code, i)
        while code[j] == " ":
            j += 1
        lst = code[j:_balanced(code, j)]
        premises = re.sub(r"forall[^,]*,", "", code[:k])  # drop the binders
        if lst.startswith("["):
            elems = [e.strip() for e in lst[1:-1].split(";") if e.strip()]
            reads = True  # the rule is stated for the END of the stream
        else:
            elems = [e.strip() for e in lst[1:-1].split("::")]
            explicit = [e for e in elems if e not in ("rest", "[]")]
            inspects = any(re.search(r"\brest\b", seg) and "Runs C" not in seg
                           and "Stops" not in seg and "Scans" not in seg
                           for seg in premises.split("->"))
            reads = len(explicit) >= 2 or inspects
        if reads and elems:
            head = elems[0].split()[0]
            out.setdefault(head, set()).add(name)
    return out


def inductive_ctors(text: str, header: str) -> list[str]:
    return re.findall(r"^\|\s*(\w+)", strip_coq_comments(_block(text, header)), re.M)


# token constructor (Syntax.v) -> branch labels (strict_decide.ml tok_name)
TOK_LABELS = {
    "TChar": ["char"], "TSpace": ["space"], "TPar": ["blank_line", "par"],
    "TOpen": ["open"], "TClose": ["close"], "TDollar": ["dollar"],
    "TMOpenInline": ["open_paren"], "TMCloseInline": ["close_paren"],
    "TMOpenDisplay": ["open_bracket"], "TMCloseDisplay": ["close_bracket"],
    "TScript": ["sup", "sub"], "TCs": [], "TEnd": ["end"],
}
# frame constructor (Semantics.v) -> head labels; "top" is the empty stack.
# FArg (slice A): one head per mode an argument runs in; a head no admitted
# argument signature runs in is unreachable under the contract (dormant).
FRAME_LABELS = {"FSimple": ["simple"], "FShift": ["inline", "display"],
                "FMGroup": ["mgroup"], "FArg": ["arg.text", "arg.textr", "arg.math"]}
MATH_HEADS = {"inline", "display", "mgroup", "arg.math"}
ARG_HEAD_OF_PAY = {"text": "arg.text", "text_restricted": "arg.textr", "math": "arg.math"}
# the scanner's token classes (strict_decide.ml tok_name; \end{document} is
# never inside an argument: Decide.wfa)
SCAN_TOKEN_LABELS = ["char", "space", "blank_line", "par", "open", "close", "dollar",
                     "open_paren", "close_paren", "open_bracket", "close_bracket",
                     "sup", "sub", "cs"]
SCAN_FLAGS_OF_LONG = {"long": "nosh|noou", "short_inner": "sh|noou", "short_outer": "sh|ou"}


def _cls(b) -> str:
    return b if isinstance(b, str) else "fatal." + b[1]


def _acls(h: dict, where: str) -> str:
    """strict_decide.ml arg_text_cls / arg_math_cls."""
    b = h[where]
    if b[0] in ("now", "after"):
        return f"{b[0]}.{b[1]}"
    if where == "text":
        return f"run.{'material' if b[1] else 'noop'}.{b[2]}"
    return f"run.{b[1]}"


def run_pay(b: list, where: str) -> str:
    """The payload mode of a run behaviour: ["run", material, P, G] in text,
    ["run", P, G] in math (G: the command's TeX groups, C-94)."""
    return b[2] if where == "text" else b[1]


def run_groups(b: list, where: str) -> int:
    """The TeX groups a run behaviour holds open (C-94)."""
    return b[3] if where == "text" else b[2]


def arg_runs(asigs: dict) -> set[str]:
    """The payload modes the admitted argument signatures run in."""
    return {run_pay(h[w], w) for h in asigs.values() for w in ("text", "math")
            if h[w][0] == "run"}


def required_cells(syntax: str, sem: str, sigs: dict, asigs: dict | None = None
                   ) -> tuple[set[str], set[str], list[str]]:
    """(cells that must be covered by an agreeing probe, cells that must be
    covered by an outside-the-tier probe, structural findings)."""
    asigs = asigs or {}
    finds = []
    toks = inductive_ctors(syntax, "Inductive tok :=")
    if set(toks) != set(TOK_LABELS):
        finds.append(f"Syntax.v tok constructors {sorted(set(toks) ^ set(TOK_LABELS))} "
                     f"are not mapped to branch labels (update TOK_LABELS)")
    frames = inductive_ctors(sem, "Inductive frame :=")
    if set(frames) != set(FRAME_LABELS):
        finds.append(f"Semantics.v frame constructors {sorted(set(frames) ^ set(FRAME_LABELS))} "
                     f"are not mapped to head labels (update FRAME_LABELS)")
    la = lookahead_tokens(sem)
    reads = set()
    for t in la:
        if t not in TOK_LABELS:
            finds.append(f"look-ahead head token {t} (constructors {sorted(la[t])}) unknown")
        reads |= set(TOK_LABELS.get(t, []))
    # a control word reads ahead only through the argument rules (R_arg_*):
    # the look-ahead is a property of the argument classes, not of every name
    arg_reads = "TCs" in la and all(c.startswith("R_arg_") for c in la["TCs"])
    if "TCs" in la and not arg_reads:
        finds.append(f"a control word reads ahead through {sorted(la['TCs'])}: "
                     f"the matrix knows the argument rules only")
    live_args = {ARG_HEAD_OF_PAY[p] for p in arg_runs(asigs)}
    heads = ["top"] + [h for f in frames for h in FRAME_LABELS.get(f, [])
                       if not h.startswith("arg.") or h in live_args]
    plain = [lab for t in toks for lab in TOK_LABELS.get(t, [])]
    tcls = sorted({_cls(v["text"]) for v in sigs.values()})
    mcls = sorted({_cls(v["math"]) for v in sigs.values()})
    pairs = sorted({f"{_cls(v['text'])}/{_cls(v['math'])}" for v in sigs.values()})
    atcls = sorted({_acls(v, "text") for v in asigs.values()})
    amcls = sorted({_acls(v, "math") for v in asigs.values()})
    followers = (plain + ["cs:undef"] + [f"cs:{q}" for q in pairs]
                 + (["cs:arg"] if asigs else []) + ["eof"])
    need_ok, need_out = set(), set()
    for h in heads:
        math = h in MATH_HEADS
        in_arg = h.startswith("arg.")
        cs = ["cs:undef"] + [f"cs:{'m' if math else 't'}.{c}" for c in (mcls if math else tcls)]
        acs = [f"cs:{'am' if math else 'at'}.{c}" for c in (amcls if math else atcls)]
        for t in plain + cs + acs:
            if t == "end" and in_arg:
                need_out.add(f"{h}|end|-|-")  # Decide.wfa: \end{document} in an argument
                continue
            if not (t in reads or (t in acs and arg_reads)):
                need_ok.add(f"{h}|{t}|-|-")
                continue
            tails = (["tail-", "tail+"] if math else ["tail-"]) if t in ("sup", "sub") else ["-"]
            for f in followers:
                for tl in tails:
                    cell = f"{h}|{t}|{f}|{tl}"
                    if t in ("sup", "sub") and f not in ("char", "open"):
                        need_out.add(cell)  # Decide.v scripts_ok
                    elif t in acs and f != "open":
                        need_out.add(cell)  # Decide.wfa: the argument's brace
                    elif in_arg and f in ("end", "eof"):
                        need_out.add(cell)  # Decide.wfa: an argument left open
                    else:
                        need_ok.add(cell)
    # the argument scanner (Semantics.Scans): every token class, directly in
    # the outermost argument (k1) and inside a group in it (k2), for each
    # longness an admitted command that runs its argument has
    longs = {v["long"] for v in asigs.values()
             if v["text"][0] == "run" or v["math"][0] == "run"}
    for lg in sorted(longs):
        for t in SCAN_TOKEN_LABELS:
            for k in ("k1", "k2"):
                need_ok.add(f"scan|{t}|{k}|{SCAN_FLAGS_OF_LONG[lg]}")
    return need_ok, need_out, finds


# ------------------------------------ check 10 (OPEN-121 review M-1) ---

FAITHFUL_BODY = ("forall d, in_strict_doc C d -> "
                 "(oracle_ok (render d) <-> Runs C init (flatten_doc d) Compiles)")
FAITHFUL_HEAD = ("Definition Faithful (oracle_ok : list Ascii.ascii -> Prop) "
                 "(C : contract) : Prop :=")
# Identifiers the premise must never mention: the decider and its machinery.
FAITHFUL_FORBIDDEN = ("decide", "run", "step")
# Vernacular that could define, shadow or re-resolve a name inside Bridge.v.
# It is matched at the start of every Coq SENTENCE, not of every line: the
# OPEN-121 re-review (MEDIUM-1) put `Module Semantics. Definition Runs ... End
# Semantics. Import Semantics.` on the Require line, where a line-start scan
# never looked.
_DEFINERS = r"Definition|Fixpoint|CoFixpoint|Let|Notation|Infix|Instance|" \
    r"Inductive|CoInductive|Variant|Record|Structure|Class|Axiom|Axioms|" \
    r"Parameter|Parameters|Hypothesis|Hypotheses|Variable|Variables|" \
    r"Conjecture|Coercion|Canonical|Ltac|Ltac2|Module|Section|End|Context|" \
    r"Program|Local|Global|Polymorphic|Monomorphic|Theorem|Lemma|Corollary|" \
    r"Proposition|Fact|Remark|Example|Property|Function|Equations|Scheme|" \
    r"Primitive|Register|Include|Import|Export|Open|Require|From|Load|" \
    r"Declare|Set|Unset|Arguments|Hint|Existing|Opaque|Transparent|Strategy|" \
    r"Reserved|Delimit|Bind|Tactic|Abbreviation"
# Control prefixes Coq accepts in front of a vernacular command: they hide
# the command's keyword from a sentence-start match (re-review 2, HIGH-1:
# `Time Definition in_strict_doc ... := False.`). They are stripped before
# matching, and any sentence that carries one is itself a finding.
_CONTROL_PREFIX = re.compile(
    r"^(?:(?:Time|Instructions|Profile|Succeed|Fail|Timeout\s+\d+|"
    r"Redirect\s+\S+|Local|Global|Polymorphic|Monomorphic|Program|"
    r"Cumulative|NonCumulative|Private)\s+|#\[[^\]]*\]\s*)+")
# The whole code of Bridge.v (comments removed, sentence by sentence,
# whitespace normalised) is PINNED: an allow-list, not a deny-list. Every
# evasion of a keyword scan found so far (a Module on the Require line, a
# control prefix, a comment-string) adds a sentence that is not on this
# list. Changing Bridge.v's code therefore means changing this list, in
# review, together with check_print_assumptions.py's kernel pins.
BRIDGE_SENTENCES = [
    "From LaTeXPerfectionist.Strict Require Import Syntax Contract Semantics Decide",
    "Definition Faithful (oracle_ok : list Ascii.ascii -> Prop) (C : contract) : Prop "
    ":= forall d, in_strict_doc C d -> "
    "(oracle_ok (render d) <-> Runs C init (flatten_doc d) Compiles)",
    "Corollary strict_ready_iff_pdflatex : forall oracle_ok C d, "
    "Faithful oracle_ok C -> in_strict_doc C d -> "
    "(decide C d = ProvenReady <-> oracle_ok (render d))",
    "Proof",
    "intros oracle_ok C d HF Hs",
    "destruct (strict_decider_exact C d Hs) as [Hready _]",
    "rewrite Hready", "symmetry", "apply HF", "exact Hs",
    "Qed",
    "Corollary strict_not_ready_pdflatex : forall oracle_ok C d r l, "
    "Faithful oracle_ok C -> in_strict_doc C d -> "
    "decide C d = ProvenNotReady r l -> ~ oracle_ok (render d)",
    "Proof",
    "intros oracle_ok C d r l HF Hs Hd Hok",
    "apply (proj2 (strict_ready_iff_pdflatex oracle_ok C d HF Hs)) in Hok",
    "rewrite Hd in Hok", "discriminate",
    "Qed",
]

# The only definer sentences Bridge.v may contain: the Require sentence
# exactly (whitespace normalised), and Faithful and the two bridge
# Corollaries by their first two words.
_BRIDGE_REQUIRE = ("From LaTeXPerfectionist.Strict Require Import "
                   "Syntax Contract Semantics Decide")
_BRIDGE_DEFINES = {("Definition", "Faithful"),
                   ("Corollary", "strict_ready_iff_pdflatex"),
                   ("Corollary", "strict_not_ready_pdflatex")}


def coq_sentences(code: str) -> list[str]:
    """Split comment-stripped Coq into sentences: a `.` followed by whitespace
    or the end ends one (a `.` inside a qualified name such as Ascii.ascii
    does not). Leading bullets and braces are dropped: they are not part of
    the sentence that follows them."""
    out = []
    for sent in re.split(r"\.(?=\s|$)", code):
        sent = " ".join(re.sub(r"^[\s\-+*{}]*", "", sent).split())
        if sent:
            out.append(sent)
    return out


def faithful_findings(bridge: str) -> list[str]:
    code = strip_coq_comments(bridge)
    out: list[str] = []
    defs = []
    if '"' in bridge:
        out.append("Bridge.v: contains a `\"` (a string, even inside a comment, "
                   "changes where Coq's comments end; OPEN-121 re-review 2, HIGH-1)")
    sents = coq_sentences(code)
    for sent in sents:
        pm = _CONTROL_PREFIX.match(sent)
        if pm:
            defs.append(("prefix", pm.group(0).strip()))
            sent = sent[pm.end():]
        m = re.match(rf"({_DEFINERS})\b\s*(\S*)", sent)
        if not m:
            continue
        if sent == _BRIDGE_REQUIRE or (m.group(1), m.group(2)) in _BRIDGE_DEFINES:
            continue
        defs.append((m.group(1), m.group(2)))
    if defs:
        out.append(f"Bridge.v: defines more than Faithful: {defs} (a name defined here "
                   f"could shadow what Faithful's body reads; OPEN-121 review M-1)")
    pinned = [" ".join(x.split()) for x in BRIDGE_SENTENCES]
    if sents != pinned:
        extra = [x for x in sents if x not in pinned]
        missing = [x for x in pinned if x not in sents]
        out.append(f"Bridge.v: its code is not the pinned sentence list BRIDGE_SENTENCES "
                   f"(re-review 2, HIGH-1); not pinned: {[x[:80] for x in extra]}; "
                   f"missing: {[x[:80] for x in missing]}"
                   + ("" if extra or missing else "; same sentences, other order"))
    head = " ".join(FAITHFUL_HEAD.split())
    norm = " ".join(code.split())
    i = norm.find(head)
    if i < 0:
        return out + [f"Bridge.v: no `{head}` (OPEN-121 review M-1)"]
    j = norm.find(". ", i)
    body = norm[i + len(head):j if j >= 0 else len(norm)].strip()
    if body != " ".join(FAITHFUL_BODY.split()):
        out.append(f"Bridge.v: Faithful's body is not the pinned one (OPEN-121 review M-1)\n"
                   f"      pinned: {FAITHFUL_BODY}\n      found:  {body}")
    idents = set(re.findall(r"[A-Za-z_][A-Za-z_0-9']*", body))
    if "Runs" not in idents:
        out.append("Bridge.v: Faithful's body does not mention Runs (OPEN-121 review M-1)")
    bad = sorted(idents & set(FAITHFUL_FORBIDDEN))
    if bad:
        out.append(f"Bridge.v: Faithful's body mentions {bad} -- the decider must never "
                   f"be a premise's content (OPEN-121 review M-1)")
    return out


# The capacity account (Decide.v, C-94), pinned token for token (comments
# stripped, whitespace normalised): a frame is one TeX group, an argument its
# command's g; the account is taken over every state of the run; and it is
# part of `bounded` with the token and name bounds.
CAPACITY_ACCOUNT = [
    ("Definition frame_groups (f : frame) : nat := match f with | FArg _ _ g _ _ => g "
     "| _ => 1 end.", "frame_groups"),
    ("Fixpoint groups (fs : list frame) : nat := match fs with | [] => 0 | f :: r => "
     "frame_groups f + groups r end.", "groups"),
    ("Fixpoint peak (C : contract) (s : state) (ts : list tok) : nat := match ts with "
     "| [] => groups (s_frames s) | t :: rest => Nat.max (groups (s_frames s)) "
     "(match step C s t (hd_error rest) with | Go1 s' => peak C s' rest | Go2 s' => "
     "match rest with [] => 0 | _ :: rest' => peak C s' rest' end | _ => 0 end) end.",
     "peak"),
    ("Definition bounded (C : contract) (ts : list tok) : bool := Nat.leb (length ts) "
     "max_tokens && short_names ts && Nat.leb (peak C init ts) max_groups && Nat.leb "
     "(mem C ts) max_mem && Nat.leb (dim C ts) max_dim.", "bounded"),
    # C-100: the dimension account
    ("Definition seg_start (s : state) (t : tok) : bool := match t, s_frames s with | "
     "TPar _, [] => true | _, _ => false end.", "seg_start"),
    ("Fixpoint dim_run (C : contract) (s : state) (acc : nat) (ts : list tok) : nat := "
     "match ts with | [] => acc | t :: rest => let m := in_math (s_frames s) in let a := "
     "if seg_start s t then c_dim C m t else acc + c_dim C m t in maxl a (match step "
     "C s t (hd_error rest) with | Go1 s' => dim_run C s' a rest | Go2 s' => match rest "
     "with | [] => a | t2 :: rest' => dim_run C s' (a + c_dim C m t2) rest' end | _ => a "
     "end) end.", "dim_run"),
    ("Definition dim (C : contract) (ts : list tok) : nat := dim_run C init (c_dim C false "
     "(TPar false)) ts.", "dim"),
    ("Definition maxl (a b : nat) : nat := if Nat.leb a b then b else a.", "maxl"),
    # C-98: the main-memory account
    ("Definition copy_of (C : contract) (n : name) : nat := match c_arg C n with "
     "Some a => as_copy a | None => 0 end.", "copy_of"),
    ("Fixpoint open_copies (opens : list (nat * nat)) : nat := match opens with [] => 0 "
     "| (_, c) :: r => c + open_copies r end.", "open_copies"),
    ("Fixpoint held_from (C : contract) (b : nat) (opens : list (nat * nat)) (ts : list "
     "tok) : nat := match ts with | [] => 0 | t :: r => open_copies opens + match t with "
     "| TCs n => if is_argcmd C n then match r with | TOpen :: r' => open_copies opens + "
     "held_from C (S b) ((b, copy_of C n) :: opens) r' | _ => held_from C b opens r end "
     "else held_from C b opens r | TOpen => held_from C (S b) opens r | TClose => "
     "held_from C (pred b) (filter (fun x => Nat.ltb (fst x) (pred b)) opens) r | _ => "
     "held_from C b opens r end end.", "held_from"),
    ("Definition held (C : contract) (ts : list tok) : nat := held_from C 0 [] ts.", "held"),
    ("Fixpoint node_cost (C : contract) (ts : list tok) : nat := match ts with [] => 0 | "
     "t :: r => c_cost C t + node_cost C r end.", "node_cost"),
    ("Definition mem (C : contract) (ts : list tok) : nat := node_cost C ts + held C ts.",
     "mem"),
]
# The frame-kind labels of strict_decide.ml pushed_label, by the constructor
# of the extracted `frame` type each one names.
LABEL_CTOR = (("simple", "FSimple"), ("inline.", "FShift"), ("display.", "FShift"),
              ("mgroup", "FMGroup"), ("script", "FMGroup"), ("arg.", "FArg"))


def _ocaml_ctors(ml: str, typ: str) -> set[str]:
    m = re.search(rf"^type {typ} =(.*?)(?=^\S)", ml, re.S | re.M)
    return set(re.findall(r"\|\s*([A-Z]\w*)", m.group(1))) if m else set()


def capacity_findings(repo: Path, ext_sha: str, sig_sha: str, asig_sha: str | None,
                      asigs: dict, extract: Path) -> list[str]:
    """Check 11 (C-94): corpora/strict_s0/capacity.json, made by
    measure_strict_capacity.py from the committed extraction and contract,
    probes EVERY pair of frame kinds the extracted model can stack (its
    --frame-pairs search over every token of the grammar): at the group
    bound, agreeing with pdfTeX with the pair on the peak's frame stack; one
    group past it, outside the fragment; and pdfTeX's own overflow within the
    window the account predicts. The frame kinds are the extracted `frame`
    type's constructors and the search alphabet covers the extracted `tok`
    type's: derived from the model, not listed here."""
    out: list[str] = []
    p = repo / CAPACITY
    if not p.is_file():
        return [f"{CAPACITY}: missing (run measure_strict_capacity.py; C-94)"]
    d = json.loads(p.read_text())
    if d.get("kernel_extract_sha256") != ext_sha:
        out.append(f"{CAPACITY}: ran another extraction; re-run measure_strict_capacity.py")
    if d.get("signatures_sha256") != sig_sha or d.get("arg_signatures_sha256") != asig_sha:
        out.append(f"{CAPACITY}: ran other signature files; re-run it")
    if d.get("bounds") != {"max_groups": MAX_GROUPS, "max_tokens": MAX_TOKENS,
                           "max_name": MAX_NAME, "max_mem": MAX_MEM, "max_dim": MAX_DIM}:
        out.append(f"{CAPACITY}: bounds {d.get('bounds')} are not Decide.v's")
    ml = extract.read_text()
    toks = _ocaml_ctors(ml, "tok")
    frames = _ocaml_ctors(ml, "frame")
    if not toks or not frames:
        out.append("capacity: cannot read the extracted tok/frame types")
    alpha = {a[0] for a in d.get("frame_pairs", {}).get("alphabet", [])}
    tok_of_label = {"char": "TChar", "space": "TSpace", "par": "TPar", "open": "TOpen",
                    "close": "TClose", "dollar": "TDollar", "open_paren": "TMOpenInline",
                    "close_paren": "TMCloseInline", "open_bracket": "TMOpenDisplay",
                    "close_bracket": "TMCloseDisplay", "sup": "TScript", "sub": "TScript",
                    "cs": "TCs", "end": "TEnd"}
    covered = {tok_of_label.get(a) for a in alpha}
    if toks - covered:
        out.append(f"{CAPACITY}: the frame-pair search's alphabet misses the token "
                   f"constructors {sorted(toks - covered)} of the extracted model")
    pairs = d.get("pairs", [])
    if len(pairs) != d.get("frame_pairs", {}).get("n", -1) or not pairs:
        out.append(f"{CAPACITY}: {len(pairs)} pair records for "
                   f"{d.get('frame_pairs', {}).get('n')} model pairs")
    labels = {x for r in pairs for x in (r.get("below"), r.get("above")) if x != "top"}
    ctors = {c for lab in labels for pre, c in LABEL_CTOR if lab.startswith(pre)}
    if frames - ctors:
        out.append(f"{CAPACITY}: no probed pair has a frame of kind {sorted(frames - ctors)}")
    for n, h in asigs.items():
        for w, suf in (("text", "/t"), ("math", "/m")):
            if h[w][0] == "run" and not any(lab.endswith(f":{n}{suf}") for lab in labels):
                out.append(f"{CAPACITY}: the argument frame of {n!r} pushed in {w} is in "
                           f"no probed pair")
    # every derived number is recomputed here from the primary records
    # (M-1/M-2 of the round-2 review), never read from a stored summary
    def first_fail(steps, key):
        ok = {r[key] for r in steps if (r.get("oracle") or [1])[0] == 0 and r["oracle"][1]}
        bad = {r[key] for r in steps if r.get("oracle") and not (r["oracle"][0] == 0
                                                                 and r["oracle"][1])}
        if not bad:
            return None
        f = min(bad)
        return f if (f - 1) in ok else None
    fails_at = {}
    for r in pairs:
        fails_at[f"{r.get('below')}>{r.get('above')}"] = first_fail(
            r.get("overflow_steps", []), "target")
    known = [v for v in fails_at.values() if v]
    capv = max(known) - 1 if known else None
    lasts = []
    for fam, t in sorted(d.get("transients", {}).items()):
        ff = first_fail(t.get("steps", []), "depth")
        okp = [r["peak"] for r in t.get("steps", []) if ff and r["depth"] == ff - 1]
        if not okp:
            out.append(f"{CAPACITY}: transient {fam} is not a measured bracket")
        else:
            lasts.append(okp[0])
    if capv is None or not lasts:
        out.append(f"{CAPACITY}: no measured grouping capacity / transient")
        capv, tmax = 10 ** 9, 0
    else:
        tmax = max(capv - p for p in lasts)
        if capv - tmax - MAX_GROUPS < 1:
            out.append(f"{CAPACITY}: no margin: capacity {capv} - transient {tmax} "
                       f"<= max_groups {MAX_GROUPS}")
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import _strict_capacity as C
    bad = 0
    for r in pairs:
        tag = f"{r.get('below')}>{r.get('above')}"
        at, past = r.get("at", {}), r.get("past", {})
        o = at.get("oracle") or [1, False]
        why = None
        if not (at.get("verdict") == "ready" and o[0] == 0 and o[1]
                and at.get("peak") == MAX_GROUPS
                and C.adjacent(at.get("frames", []), r.get("below"), r.get("above"))):
            why = f"not probed at the bound (verdict {at.get('verdict')}, peak {at.get('peak')})"
        elif not (past.get("verdict") == "not_strict" and past.get("peak") == MAX_GROUPS + 1):
            why = "one group past the bound is not outside the fragment"
        elif not (isinstance(fails_at[tag], int)
                  and capv + 1 - tmax <= fails_at[tag] <= capv + 1):
            why = (f"pdfTeX overflows at {fails_at[tag]} groups, outside the "
                   f"account's window [{capv + 1 - tmax}, {capv + 1}]")
        if why:
            bad += 1
            if bad <= 10:
                out.append(f"{CAPACITY}: pair {tag} {why}")
    if bad > 10:
        out.append(f"{CAPACITY}: {bad} pairs fail in all")
    for fam, v in sorted(d.get("usage", {}).items()):
        o = v.get("oracle") or [1, False]
        if v.get("verdict") == "not_strict":
            if fam != "longest_line":
                out.append(f"{CAPACITY}: usage document {fam} is outside the fragment")
            continue  # the buffer's instrument (C-100)
        if not ((v.get("verdict") == "ready") == (o[0] == 0 and o[1])):
            out.append(f"{CAPACITY}: usage document {fam} disagrees")
    return out


def capacity_table(*files: dict) -> dict:
    """pdfTeX's report of every capacity, maximised over EVERY graded record
    of the given evidence files (pairs, transients, usage, the memory
    documents and the memory worst cases): {resource: (used, of, where)}."""
    table = {}

    def walk(x, where):
        if isinstance(x, dict):
            st = x.get("stats")
            if isinstance(st, dict) and "sha256" in x:
                for res, uo in st.items():
                    if isinstance(uo, list) and len(uo) == 2:
                        if res not in table or uo[0] > table[res][0]:
                            table[res] = (uo[0], uo[1], where)
            for k, v in x.items():
                walk(v, f"{where}/{k}" if len(where) < 120 else where)
        elif isinstance(x, list):
            for v in x:
                walk(v, where)
    for i, f in enumerate(files):
        walk(f, f"file{i}")
    return table


def _jmax(steps: list) -> int | None:
    """The deepest depth that compiled, from stage G's PRIMARY records
    [depth, sha256, rc, pdf, error], provided the next depth is recorded
    failing (else None: the measurement is not a bracket)."""
    ok = {j for j, _, rc, pdf, _ in steps if rc == 0 and pdf}
    bad = {j for j, _, rc, pdf, _ in steps if not (rc == 0 and pdf)}
    if not ok:
        return None
    j = max(ok)
    return j if (j + 1) in bad and not any(b < j for b in bad) else None


def derived_groups(cap: dict, n: str, w: str) -> int | None:
    """A command's TeX groups re-derived from stage G's graded depths (M-2 of
    the round-2 review: never from a count stored beside them)."""
    pr = cap.get("probes", {})
    kj = _jmax(pr.get("K/math", []))
    nj = _jmax(pr.get(f"{n}/{w}", []))
    if kj is None or nj is None:
        return None
    K = kj + 1
    return K - nj if w == "text" else K - 1 - nj


def _ok(r: dict) -> bool:
    o = r.get("oracle")
    return bool(o) and o[0] == 0 and o[1] and r.get("used") is not None


def _records(tree):
    """Every per-document record of a tree (a dict with the bytes' sha256)."""
    if isinstance(tree, dict):
        if "sha256" in tree:
            yield tree
        for v in tree.values():
            yield from _records(v)
    elif isinstance(tree, list):
        for v in tree:
            yield from _records(v)


def memory_findings(sig: dict, asig: dict) -> list[str]:
    """Check 13 (C-98, C-100): every cost of the memory account re-derived
    from the generators' PRIMARY records (each graded document's model counts
    and pdfTeX's reported memory), with the functions the generators use
    (_strict_capacity): the token cost and the boundary constants (slopes
    over the structural levels and the class pairs), every name's cost
    (slopes over its contexts, plus its letters and atoms re-derived from the
    dimension evidence), every command's copy factor and cost. EVERY memory
    record must carry pdfTeX's report (C-100: 83 of the C-98 bound records
    had none, and this check skipped them), and pdfTeX's report must be
    within the account on EVERY record (base + Decide.mem): the instruments,
    the bound documents, the worst cases and the round-1 review's documents.
    Every admitted name has a document at its bound (memory, tokens) and one
    past it outside; every argument command's worst cases (a filler of no
    dimensions, and the costliest) compile within half of main memory and one
    character past each is outside."""
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import _strict_capacity as C
    out = []
    mem1 = sig.get("memory", {})
    st = mem1.get("structural", {})
    if "BASE" not in st or not st["BASE"].get("used"):
        return ["signatures: no memory records (C-98; regenerate)"]
    m0, cap = st["BASE"]["used"], st["BASE"]["of"]
    try:
        T = C.token_cost(st)
        B = C.boundary_constants(st, mem1.get("class_pairs", {}))
    except (ValueError, KeyError) as e:
        return [f"signatures: the memory records do not give the token cost / boundary "
                f"constants ({e}; C-100)"]
    if sig.get("token_cost") != T or mem1.get("token_cost") != T:
        out.append(f"signatures: token_cost {sig.get('token_cost')} is not what the "
                   f"structural records give ({T})")
    if mem1.get("boundary") != B:
        out.append(f"signatures: the boundary constants {mem1.get('boundary')} are not "
                   f"what the records give ({B}; C-100)")
    if (m0 + MAX_MEM) * 2 > cap:
        out.append(f"memory account: base {m0} + max_mem {MAX_MEM} is more than half of "
                   f"main memory {cap} (C-98 margin)")
    # every record carries pdfTeX's report, and the report is within the
    # account wherever the model counted it
    # (stage G's documents are counted under a RAW contract, copy factor 1:
    # the held count its slope is taken over; their account under the
    # committed contract is check_strict_capacity.py's, which re-runs them)
    trees = [("signatures", mem1, True), ("signatures dim bound", sig.get("dim_bound", {}), True),
             ("arg signatures stage G", asig.get("capacity", {}).get("memory", {}), False),
             ("arg signatures", asig.get("capacity", {}).get("memory_bound", {}), True)]
    nrec = over = 0
    for label, tree, account in trees:
        for r in _records(tree):
            if "oracle" not in r:
                continue  # a document never graded (one past a bound)
            nrec += 1
            if r.get("used") is None:
                out.append(f"{label}: a graded memory record carries no pdfTeX report "
                           f"(sha256 {r.get('sha256', '')[:12]}; C-100)")
                continue
            if account and r.get("mem") is not None and _ok(r) and r["used"] > m0 + r["mem"]:
                over += 1
                if over <= 10:
                    out.append(f"{label}: pdfTeX reports {r['used']} words, more than the "
                               f"account {m0 + r['mem']} (sha256 {r['sha256'][:12]}; C-100)")
    if nrec == 0:
        out.append("signatures: no graded memory record")
    dd = None
    try:
        dd = _dims_derived(Path(__file__).resolve().parents[2], sig.get("dims_derivation", {}))
    except Exception as e:  # noqa: BLE001
        out.append(f"signatures: the dimension evidence does not load ({e})")
    dt = sig.get("dims_derivation", {})
    for n, h in sorted(sig.get("signatures", {}).items()):
        letters = (dd["letters"].get(n, 0) if dd and n in dt.get("text_names", []) else 0)
        atoms = (dd["atoms"].get(n, 0) if dd and n in dt.get("math_names", []) else 0)
        try:
            want = C.name_cost(mem1.get("names", {}).get(n, {}), m0, T, letters, atoms, B)
        except ValueError as e:
            out.append(f"signatures: {n!r}'s memory records: {e}")
            continue
        if want is None or h.get("cost") != want:
            out.append(f"signatures: {n!r}'s cost {h.get('cost')} is not what its memory "
                       f"documents give ({want}; C-98, C-100)")
        ctxs = {f.split("@")[0] for f in mem1.get("names", {}).get(n, {})}
        need = set()
        if not isinstance(h["text"], list):
            need.add("R-MEM-TEXT")
        if not isinstance(h["math"], list):
            need |= {"R-MEM-MATH", "R-MEM-DISPLAY"}
            if h["math"] == "noad":
                need |= {"R-MEM-MSCRIPT", "R-MEM-DSCRIPT"}
        if need - ctxs:
            out.append(f"signatures: {n!r} has no memory documents in {sorted(need - ctxs)}")
        for ctx in need & ctxs:
            lv = [f for f in mem1["names"][n] if f.startswith(ctx + "@")]
            if len(lv) < 3:
                out.append(f"signatures: {n!r} {ctx} has {len(lv)} counts, not 3 (the slope "
                           f"past the high-water mark; C-100)")
        capn = mem1.get("cap", {}).get(n, {})
        for f, r in capn.items():
            if f.endswith("-PAST"):
                if r.get("verdict") != "not_strict":
                    out.append(f"signatures: {n!r} {f} is {r.get('verdict')}, not outside")
            elif not (r.get("verdict") in ("ready", "not_ready") and r.get("oracle")
                      and (r["oracle"][0] == 0) == (r["verdict"] == "ready")):
                out.append(f"signatures: {n!r} at the bound ({f}) does not agree")
        for where, beh in (("TEXT", h["text"]), ("MATH", h["math"])):
            if isinstance(beh, list):
                continue
            if f"R-CAP-{where}" not in capn or f"R-CAP-{where}-PAST" not in capn:
                out.append(f"signatures: {n!r} has no document at the bound in {where} "
                           f"and one past it (C-98)")
    if len(mem1.get("review", {})) < 3:
        out.append("signatures: the round-1 review's memory documents are not recorded "
                   "(C-100)")
    cap_a = asig.get("capacity", {})
    am = cap_a.get("memory", {})
    for n, h in sorted(asig.get("arg_signatures", {}).items()):
        try:
            d = C.copy_and_cost(am.get("records", {}).get(n, {}), m0, T)
        except ValueError as e:
            out.append(f"arg signatures: {n!r}'s memory records: {e}")
            continue
        if d.get("copy") is None or h.get("copy") != d["copy"] or \
                not isinstance(h.get("cost"), int) or h["cost"] < d["cost"]:
            out.append(f"arg signatures: {n!r}'s copy/cost {h.get('copy')}/{h.get('cost')} "
                       f"are not what its memory documents give (copy {d.get('copy')}, "
                       f"cost at least {d.get('cost')}; C-98)")
        mb = cap_a.get("memory_bound", {}).get(n, {})
        for w in ("text", "math"):
            if h[w][0] != "run":
                continue
            for key in (w, f"{w}:costly"):
                r = mb.get(key)
                if not r:
                    out.append(f"arg signatures: {n!r} has no memory worst case {key} "
                               f"(C-98, C-100)")
                    continue
                at, past = r["at"], r["past"]
                if not (at.get("verdict") == "ready" and _ok(at) and at["used"] * 2 <= at["of"]
                        and at.get("mem", MAX_MEM + 1) <= MAX_MEM):
                    out.append(f"arg signatures: {n!r}'s memory worst case {key} does not "
                               f"compile within half of main memory ({at.get('used')} of "
                               f"{at.get('of')})")
                if not (past.get("verdict") == "not_strict" and r.get("past_over")):
                    out.append(f"arg signatures: {n!r}'s memory worst case {key} plus one "
                               f"is not outside the fragment")
    return out


def _dims_derived(repo: Path, block: dict) -> dict:
    """The derivation (_strict_dims.derive) of a dimension evidence file named
    by a signature file's dims block, after checking its sha256."""
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import _strict_dims as DM
    ev = block["evidence"]
    p = repo / ev["file"]
    if sha(p) != ev["sha256"]:
        raise ValueError(f"{ev['file']}: sha256 is not the one recorded")
    return DM.derive(json.loads(p.read_text())["measurement"])


def dims_findings(repo: Path, sig: dict, asig: dict) -> list[str]:
    """Check 14 (C-100): the dimension account re-derived from its PRIMARY
    records (TeX's box dumps, the characters' dimensions, the layout
    parameters, the noads; corpora/strict_s0/dims_s{0,1}.json, by sha256)
    with the generators' own function (_strict_dims.derive): the structural
    table the loader reads, every admitted name's and command's [text, math]
    dims, and each command's boundaries and scripts within the phase-1
    constants; every admitted name measured in every mode it runs in; every
    name with dimensions in a mode at the dimension bound (graded, agreeing,
    pdfTeX's own box within the account) and one past it outside."""
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import _strict_dims as DM
    out = []
    blk = sig.get("dims_derivation")
    if not blk or "dims" not in sig:
        return ["signatures: no dimension account (C-100; regenerate)"]
    try:
        dd = _dims_derived(repo, blk)
    except Exception as e:  # noqa: BLE001
        return [f"signatures: dimension evidence: {e}"]
    if DM.table(dd) != sig["dims"]:
        out.append("signatures: the structural dimension table is not what the evidence "
                   "gives (C-100)")
    for k in ("B_text", "B_math", "script", "open", "space", "par", "display", "inline"):
        if abs(blk.get(k, -1) - dd[k]) > 1e-9:
            out.append(f"signatures: dims_derivation.{k} {blk.get(k)} is not the evidence's "
                       f"{dd[k]}")
    tn, mn = set(blk.get("text_names", [])), set(blk.get("math_names", []))
    for n, h in sorted(sig.get("signatures", {}).items()):
        runs_t, runs_m = not isinstance(h["text"], list), not isinstance(h["math"], list)
        if (runs_t and n not in tn) or (runs_m and n not in mn):
            out.append(f"signatures: {n!r} is not measured in every mode it runs in")
            continue
        want = [DM.up(dd["items"][n][0]) if n in tn else 0,
                DM.up(dd["items"][n][1]) if n in mn else 0]
        if not runs_t:
            want[0] = 0
        if not runs_m:
            want[1] = 0
        if h.get("dim") != want:
            out.append(f"signatures: {n!r}'s dim {h.get('dim')} is not what the evidence "
                       f"gives ({want}; C-100)")
        db = sig.get("dim_bound", {}).get(n, {})
        for i, where in ((0, "TEXT"), (1, "MATH"), (1, "DISPLAY")):
            if not h.get("dim") or h["dim"][i] == 0:
                continue
            at, past = db.get(f"R-DIM-{where}"), db.get(f"R-DIM-{where}-PAST")
            if not at or not past:
                out.append(f"signatures: {n!r} has no document at the dimension bound in "
                           f"{where} and one past it (C-100)")
                continue
            o = at.get("oracle") or [1, False]
            if not (at.get("verdict") in ("ready", "not_ready")
                    and (o[0] == 0) == (at["verdict"] == "ready")):
                out.append(f"signatures: {n!r} at the dimension bound ({where}) does not agree")
            box = at.get("box")
            if box is None or sum(abs(v) for v in box) > at.get("dim", -1):
                out.append(f"signatures: {n!r} at the dimension bound ({where}): pdfTeX's box "
                           f"{box} is not within the account {at.get('dim')} (C-100)")
            if past.get("verdict") != "not_strict":
                out.append(f"signatures: {n!r} one past the dimension bound ({where}) is "
                           f"{past.get('verdict')}, not outside")
    ab = asig.get("dims_derivation")
    asigs = asig.get("arg_signatures", {})
    if asigs and not ab:
        return out + ["arg signatures: no dimension account (C-100; regenerate)"]
    if asigs:
        try:
            ev = ab["evidence"]
            p = repo / ev["file"]
            if sha(p) != ev["sha256"]:
                raise ValueError(f"{ev['file']}: sha256 is not the one recorded")
            m = json.loads(p.read_text())["measurement"]
            da, exc = DM.derive(m), DM.excesses(m)
        except Exception as e:  # noqa: BLE001
            return out + [f"arg signatures: dimension evidence: {e}"]
        tc, mc = set(ab.get("text_cmds", [])), set(ab.get("math_cmds", []))
        for n, h in sorted(asigs.items()):
            if (h["text"][0] == "run" and n not in tc) or (h["math"][0] == "run" and n not in mc):
                out.append(f"arg signatures: {n!r} is not measured in every mode it runs in")
                continue
            it = da["items"][n]
            tv = None
            if n in tc and h["text"][0] == "run":
                tv = it[0] - (da["B_text"] if it[0] > 0 else 0) + \
                    (blk["B_text"] if it[0] > 0 else 0)
            mv = None
            if n in mc and h["math"][0] == "run":
                mv = it[1] - da["atoms"][n] * da["B_math"] + da["atoms"][n] * blk["B_math"]
            want = [DM.up(tv), DM.up(mv)]
            if h.get("dim") != want:
                out.append(f"arg signatures: {n!r}'s dim {h.get('dim')} is not what the "
                           f"evidence gives ({want}; C-100)")
            wt = max([e for k, e in exc["text"].items() if n in k.split("|")] + [0.0])
            wm = max([e for k, e in exc["math"].items() if n in k.split("|")[1:]] + [0.0])
            ws = max([e for k, e in exc["script"].items() if k.split("|")[1] == n] + [0.0])
            if wt > blk["B_text"] or wm > blk["B_math"] or ws > blk["script"]:
                out.append(f"arg signatures: {n!r} makes a boundary past the phase-1 "
                           f"constants (text {wt:.3f}, math {wm:.3f}, script {ws:.3f}; C-100)")
    return out


def reuse_findings(repo: Path, label: str, reuse) -> list[str]:
    """Check 12 (LOW-2 of the C-94 review): a reused grade's source is a
    COMMITTED file, recorded by repository path, commit and sha256, never a
    local path or store; when the commit is available the file's sha256 is
    verified."""
    if not reuse:
        return []
    srcs = reuse.get("sources") if isinstance(reuse, dict) and "sources" in reuse else [reuse]
    out = []
    for src in srcs:
        f, c, h = src.get("file", ""), src.get("commit", ""), src.get("sha256", "")
        if (not re.fullmatch(r"[0-9a-f]{40}", str(c)) or not re.fullmatch(r"[0-9a-f]{64}", str(h))
                or not f or f.startswith("/") or ".." in Path(f).parts):
            out.append(f"{label}: grades reused from {f or src} which is not a committed "
                       f"file (path, commit, sha256; LOW-2)")
            continue
        import subprocess
        g = subprocess.run(["git", "show", f"{c}:{f}"], cwd=repo, capture_output=True)
        if g.returncode == 0 and hashlib.sha256(g.stdout).hexdigest() != h:
            out.append(f"{label}: reuse source {f}@{c[:12]} does not have the recorded sha256")
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=".")
    args = ap.parse_args()
    repo = Path(args.repo).resolve()
    fails: list[str] = []

    sem = (repo / "proofs/Strict/Semantics.v").read_text()
    syntax = (repo / "proofs/Strict/Syntax.v").read_text()
    decide_v = (repo / "proofs/Strict/Decide.v").read_text()
    # the constructors of the three semantic relations: Runs, and since slice A
    # Scans (the argument scanner) and Stops (where an error is reported)
    ctors = []
    for header, prefix in (("Inductive Scans", "SC_"), ("Inductive Stops", "Stop_"),
                           ("Inductive Runs", "R_")):
        body = sem[sem.index(header):]
        body = body[:body.index(".\n\n") if header != "Inductive Runs" else len(body)]
        found = re.findall(rf"^\|\s*({prefix}\w+)\s*:", body, re.M)
        for c in found:
            pre = body[:body.index(f"| {c} :")]
            last_comment = pre[pre.rfind("(*"):]
            if f"probe S0/{c}" not in last_comment:
                fails.append(f"Semantics.v: constructor {c} has no `probe S0/{c}` comment "
                             f"directly above it")
        ctors += found
    if len([c for c in ctors if c.startswith("R_")]) < 40:
        fails.append(f"Semantics.v: found {len(ctors)} constructors; the parser "
                     f"of this gate is broken or the relation shrank")

    extract = repo / "latex-parse/strict/strict_kernel_extracted.ml"
    sig_path = repo / "corpora/contracts/strict/article-s0-signatures.json"
    contract_path = repo / "corpora/contracts/article.json"
    contract = json.loads(contract_path.read_text())
    kernel_path = repo / contract["kernel"]["file"]
    cur = {"kernel_sha256": sha(kernel_path), "contract_sha256": sha(contract_path)}
    ext_sha = sha(extract)

    def fresh(label: str, d: dict, want_sig: bool) -> None:
        if d.get("kernel_extract_sha256") != ext_sha:
            fails.append(f"{label}: ran another extraction (kernel_extract_sha256 "
                         f"{str(d.get('kernel_extract_sha256'))[:12]} != committed "
                         f"{ext_sha[:12]}); re-run it")
        for k, v in cur.items():
            if d.get("source", {}).get(k) != v:
                fails.append(f"{label}: source {k} is not the committed file's")
        if want_sig and d.get("signatures_sha256") != sha(sig_path):
            fails.append(f"{label}: ran another signature file; re-run it")

    sig = json.loads(sig_path.read_text())
    fresh("signatures", sig, False)
    asig_path = repo / ARG_SIGNATURES
    asig = json.loads(asig_path.read_text()) if asig_path.is_file() else {}
    asigs = asig.get("arg_signatures", {})
    if asig:
        fresh("arg signatures", asig, False)
        if asig.get("signatures_sha256") != sha(sig_path):
            fails.append("arg signatures: attested against another phase-1 signature "
                         "file (the context and interleaving stages read it); re-run it")
    rp = json.loads((repo / "corpora/strict_s0/rule_probes.json").read_text())
    fresh("rule_probes", rp, True)
    df = json.loads((repo / DIFFERENTIAL).read_text())
    fresh("differential", df, True)
    for label, d in (("rule_probes", rp), ("differential", df)):
        if d.get("arg_signatures_sha256") != (sha(asig_path) if asig else None):
            fails.append(f"{label}: ran another argument-signature file; re-run it")

    # DORMANT constructors (slice A): a rule whose premise no admitted
    # signature satisfies cannot fire on any document under the committed
    # contract; it needs no family (it is listed). Derived from the files.
    runs_in = lambda pred: any(pred(h) for h in asigs.values())  # noqa: E731
    run_any = lambda h: h["text"][0] == "run" or h["math"][0] == "run"  # noqa: E731
    live = {
        "R_arg_text_now": runs_in(lambda h: h["text"][0] == "now"),
        "R_arg_text_after": runs_in(lambda h: h["text"][0] == "after"),
        "R_arg_text_run": runs_in(lambda h: h["text"][0] == "run"),
        "R_arg_math_now": runs_in(lambda h: h["math"][0] == "now"),
        "R_arg_math_after": runs_in(lambda h: h["math"][0] == "after"),
        "R_arg_math_run": runs_in(lambda h: h["math"][0] == "run"),
        "R_close_arg": runs_in(run_any),
        "R_par_short": runs_in(lambda h: run_any(h) and h["long"] != "long"),
        "R_dollar_restricted_open": "text_restricted" in arg_runs(asigs),
        "R_mopen_display_restricted": "text_restricted" in arg_runs(asigs),
        "SC_par_outer": runs_in(lambda h: run_any(h) and h["long"] == "short_outer"),
        "SC_par_short": runs_in(lambda h: run_any(h) and h["long"] == "short_inner"),
        "SC_par_long": runs_in(lambda h: run_any(h) and h["long"] == "long"),
    }
    # the phase-1 control-word rules likewise (C-96 left no admitted name
    # that is fatal in math): live iff some admitted signature has the class
    for where, cls, rule in (("text", "material", "R_cs_text_material"),
                             ("text", "noop", "R_cs_text_noop"),
                             ("text", None, "R_cs_text_fatal"),
                             ("math", "noad", "R_cs_math_noad"),
                             ("math", "noop", "R_cs_math_noop"),
                             ("math", None, "R_cs_math_fatal")):
        live[rule] = any((h[where] == cls) if cls else isinstance(h[where], list)
                         for h in sig.get("signatures", {}).values())
    deferring = runs_in(lambda h: run_any(h) or "after" in (h["text"][0], h["math"][0]))
    for c in ("SC_close_last", "SC_close", "SC_open", "SC_skip", "Stop_defer"):
        live[c] = deferring
    dormant = sorted(c for c in ctors if live.get(c, True) is False)

    fam = rp.get("by_family", {})
    for c in ctors:
        if c in dormant:
            continue
        f = fam.get(c)
        if not f or f.get("n", 0) < 1:
            fails.append(f"rule_probes: no probe family for constructor {c}")
        elif f.get("agree") != f.get("n"):
            fails.append(f"rule_probes: family {c}: {f['n'] - f['agree']} of {f['n']} "
                         f"probes disagree with the oracle")
        elif f.get("exercised", 0) < 1:
            fails.append(f"rule_probes: family {c}: no probe's run used {c}")
    for label, d in (("rule_probes", rp), ("differential", df)):
        s_ = d.get("summary", {})
        if s_.get("disagree") != 0 or d.get("disagreements"):
            fails.append(f"{label}: {s_.get('disagree')} disagreement(s) with the oracle")
        if s_.get("oracle_infrastructure_failures") != 0:
            fails.append(f"{label}: {s_.get('oracle_infrastructure_failures')} ungraded "
                         f"document(s) (oracle infrastructure failures)")
        if s_.get("agree") != s_.get("graded"):
            fails.append(f"{label}: agree {s_.get('agree')} != graded {s_.get('graded')}")
    if df.get("summary", {}).get("graded", 0) < MIN_DIFFERENTIAL:
        fails.append(f"differential: graded {df.get('summary', {}).get('graded')} "
                     f"documents, the floor is {MIN_DIFFERENTIAL}")
    ub = df.get("summary", {}).get("upper_bound_95", {})
    if "not over L_S0" not in str(ub.get("scope", "")):
        fails.append("differential: the upper bound does not state that it is a bound "
                     "over the generator's distribution, not over L_S0 (C-85)")

    # 4. signatures: contract_wf and the selection rule
    kern = json.loads(kernel_path.read_text())
    members = set(kern["names"])
    for n, v in contract["defined_names"].items():
        (members.discard if v.get("kind") == "Undefined" else members.add)(n)
    sigs = sig.get("signatures", {})
    for n in sigs:
        if n not in members:
            fails.append(f"signatures: {n!r} is not defined in the closed world")
    words = sorted((m for m in members if re.fullmatch(r"[A-Za-z]+", m)
                    and m not in STRUCTURAL),
                   key=lambda m: hashlib.sha256(m.encode()).hexdigest())
    want = set(words[:sig.get("selection", {}).get("n", -1)])
    got = set(sigs) | set(sig.get("rejected", {}))
    if want != got:
        fails.append(f"signatures: candidate set differs from the selection rule "
                     f"({len(got - want)} extra, {len(want - got)} missing)")
    if set(sigs) & set(sig.get("rejected", {})):
        fails.append("signatures: a name is both admitted and rejected")
    # 4b. argument signatures (slice A): contract_wf and the selection rule
    if asig:
        for n in asigs:
            if n not in members:
                fails.append(f"arg signatures: {n!r} is not defined in the closed world")
            if n in sigs:
                fails.append(f"arg signatures: {n!r} has both kinds of signature (contract_wf)")
        sel = asig.get("selection", {})
        sm = asig.get("selection_meanings", {})
        if sel.get("only"):
            fails.append("arg signatures: generated with --only (not the selection rule)")
        want_a = arg_candidates(sm, set(sigs))
        words_all = {m for m in members if re.fullmatch(r"[A-Za-z]+", m)}
        if not words_all <= set(sm):
            fails.append(f"arg signatures: selection meanings lack "
                         f"{len(words_all - set(sm))} closed-world control words")
        if set(sel.get("names", [])) != set(want_a):
            fails.append("arg signatures: the candidate list is not the selection rule's")
        got_a = set(asigs) | set(asig.get("rejected", {}))
        if got_a != set(want_a):
            fails.append(f"arg signatures: admitted+rejected differ from the candidates "
                         f"({len(got_a - set(want_a))} extra, {len(set(want_a) - got_a)} missing)")
        if set(asigs) & set(asig.get("rejected", {})):
            fails.append("arg signatures: a name is both admitted and rejected")

    # 5. no name in Coq
    for f in ("Semantics.v", "Contract.v", "Bridge.v", "Decide.v"):
        code = strip_coq_comments((repo / "proofs/Strict" / f).read_text())
        for lit in re.findall(r'"((?:[^"]|"")*)"', code):
            if f == "Decide.v" and len(lit) == 1:
                continue
            fails.append(f"proofs/Strict/{f}: string literal {lit!r} outside a comment "
                         f"(names reach the kernel only through the contract)")

    # 6. every admitted name is inert (RULE R-INERT)
    meanings = sig.get("meanings", {})
    prims = set(kern.get("primitives", {}).get("names", []))
    world = set(members)
    lexp = repo / "corpora/contracts/strict/article-s0-lexical.json"
    active = (active_chars(repo) if lexp.is_file() else DEFAULT_ACTIVE)
    if not prims:
        fails.append("kernel file: no primitives list (RULE R-INERT needs it)")
    for n in sorted(sigs):
        if n not in meanings:
            fails.append(f"signatures: admitted {n!r} has no recorded meaning (R-INERT)")
            continue
        try:
            v = inertness_violation(n, meanings, prims, world, active)
        except KeyError as e:
            fails.append(f"signatures: {e.args[0]} (R-INERT)")
            continue
        if v:
            fails.append(f"signatures: admitted {n!r} is not inert: {v} (R-INERT)")
    ameanings = asig.get("meanings", {})
    for n in sorted(asigs):
        try:
            v = inertness_violation(n, ameanings, prims, world, active)
        except KeyError as e:
            fails.append(f"arg signatures: {e.args[0]} (R-INERT)")
            continue
        if v:
            fails.append(f"arg signatures: admitted {n!r} is not inert: {v} (R-INERT)")

    # 13. no admitted name reads the clock (RULE R-CLOCK, OPEN-118 (b)); the
    # argument commands too, and read as R-INERT reads (world, active)
    missing_clock = sorted(CLOCK_PRIMITIVES - prims)
    if missing_clock:
        fails.append(f"kernel file: the primitives list lacks the clock primitives "
                     f"{missing_clock} (RULE R-CLOCK would be vacuous)")
    date_names = tuple(kern.get("date_dependent_names", []))
    for n in sorted(sigs):
        if n not in meanings:
            continue  # reported by check 6
        try:
            v = clock_violation(n, meanings, prims, date_names, world, active)
        except KeyError:
            continue  # reported by check 6
        if v:
            fails.append(f"signatures: admitted {n!r} reads the clock: {v} (R-CLOCK)")
    for n in sorted(asigs):
        if n not in ameanings:
            fails.append(f"arg signatures: admitted {n!r} has no recorded meaning (R-CLOCK)")
            continue
        try:
            v = clock_violation(n, ameanings, prims, date_names, world, active)
        except KeyError:
            continue  # reported by check 6
        if v:
            fails.append(f"arg signatures: admitted {n!r} reads the clock: {v} (R-CLOCK)")

    # 7. branch matrix
    need_ok, need_out, finds = required_cells(syntax, sem, sigs, asigs)
    fails += [f"branch matrix: {m}" for m in finds]
    covered_ok = {b for r in rp.get("probes", []) if r.get("agree")
                  for b in r.get("branches", [])}
    covered_out = {b for r in rp.get("outside_tier", [])
                   for b in r.get("branches", [])}
    miss_ok = sorted(need_ok - covered_ok)
    miss_out = sorted(need_out - covered_out - covered_ok)
    for cell in miss_ok[:25]:
        fails.append(f"branch matrix: cell {cell} is not exercised by an agreeing rule probe")
    for cell in miss_out[:25]:
        fails.append(f"branch matrix: cell {cell} (outside the tier by scripts_ok) has no probe")
    if len(miss_ok) + len(miss_out) > 50:
        fails.append(f"branch matrix: {len(miss_ok)} + {len(miss_out)} cells missing in all")
    bad_out = sorted({r.get("family") for r in rp.get("outside_tier", [])}
                     - {"BOUND-OUT", "MATRIX-OUT"})
    if bad_out:
        fails.append(f"rule_probes: outside-the-tier documents in families {bad_out}")

    # 8. signature evidence is complete
    ev = sig.get("evidence", {})
    for n, h in sorted(sigs.items()):
        e = ev.get(n, {})
        miss = [f for f in REQUIRED_SIGNATURE_FAMILIES if f not in e]
        if miss:
            fails.append(f"signatures: admitted {n!r} lacks probe families {miss[:6]}")
            continue
        for f in DISPLAY_FOLLOWER_FAMILIES:
            rc, pdf, err, _ = e[f]
            if rc == 0 or err != "! Display math should end with $$.":
                fails.append(f"signatures: admitted {n!r} is not a bad display-$ follower "
                             f"({f}: rc {rc}, {err!r}; C-85)")
        for fams, beh in ((REPETITION_TEXT, h["text"]), (REPETITION_MATH, h["math"])):
            if isinstance(beh, list):
                continue  # fatal in that mode: the first occurrence stops pdflatex
            for f in fams:
                rc, pdf, err, _ = e[f]
                if rc != 0 or not pdf:
                    fails.append(f"signatures: admitted {n!r} does not compile under "
                                 f"{f} (rc {rc}, pdf {pdf}, {err!r}; C-85/C-86)")
    il = sig.get("interleaving", {}).get("rounds", [])
    if not il or il[-1].get("disagree") != 0 or il[-1].get("documents", 0) < 1:
        fails.append("signatures: no interleaving round with 0 disagreements (stage 4)")
    elif not {"I-TEXT", "I-MATH"} <= set(il[-1].get("families", [])):
        fails.append("signatures: the last interleaving round lacks text or math documents")
    # 8b. argument-signature evidence is complete (slice A)
    aev = asig.get("evidence", {})
    for n, h in sorted(asigs.items()):
        e = aev.get(n, {})
        miss = [f for f in REQUIRED_ARG_FAMILIES if f not in e]
        if miss:
            fails.append(f"arg signatures: admitted {n!r} lacks probe families {miss[:6]}")
            continue
        rc, pdf, err, _ = e["A-D-FOLLOW"]
        if rc == 0 or err != "! Display math should end with $$.":
            fails.append(f"arg signatures: admitted {n!r} is not a bad display-$ follower "
                         f"(A-D-FOLLOW: rc {rc}, {err!r}; C-85)")
        for where, fams in ARG_REPETITION.items():
            if h[where][0] != "run":
                continue  # the first occurrence stops pdflatex, or nothing runs
            for f in fams:
                rc, pdf, err, _ = e[f]
                if rc != 0 or not pdf:
                    fails.append(f"arg signatures: admitted {n!r} does not compile under "
                                 f"{f} (rc {rc}, pdf {pdf}, {err!r}; C-85/C-86)")
    if asigs:
        ail = asig.get("interleaving", {}).get("rounds", [])
        if not ail or ail[-1].get("disagree") != 0 or ail[-1].get("documents", 0) < 1:
            fails.append("arg signatures: no interleaving round with 0 disagreements")
        ctx = asig.get("context", {})
        if ctx.get("disagree") != 0:
            fails.append(f"arg signatures: the context stage has {ctx.get('disagree')} "
                         f"disagreement(s) (phase-1 names in an argument's mode)")
        need_ctx = {f"{w}/{run_pay(h[w], w)}" for h in asigs.values()
                    for w in ("text", "math")
                    if h[w][0] == "run" and run_pay(h[w], w) != "math"
                    and not (w == "text" and run_pay(h[w], w) == "text")}
        if need_ctx - set(ctx.get("carriers", {})):
            fails.append(f"arg signatures: no context evidence for the modes "
                         f"{sorted(need_ctx - set(ctx.get('carriers', {})))}")

    # 9. capacity bounds (C-86, C-94): the pins, and the account pinned
    code_d = " ".join(strip_coq_comments(decide_v).split())
    for pin in ("Example max_groups_is_200 : max_groups = 200.",
                "Example max_tokens_is_20000 : max_tokens = Nat.mul 200 100.",
                "Example max_name_is_100 : max_name = 100.",
                "Example max_mem_is_100_tokens : max_mem = Nat.mul max_tokens 100.",
                "Example max_dim_is_8000 : max_dim = Nat.mul 80 100."):
        if pin not in decide_v:
            fails.append(f"Decide.v: missing the pin `{pin}`")
    if (MAX_GROUPS, MAX_TOKENS, MAX_NAME, MAX_MEM, MAX_DIM) != (200, 200 * 100, 100,
                                                                200 * 100 * 100, 80 * 100):
        fails.append("check_strict_kernel: MAX_GROUPS/MAX_TOKENS/MAX_NAME differ from Decide.v")
    import _strict_capacity as _C
    import _strict_dims as _DM
    if not (_C.DIM_BOUND == _DM.DIM_BOUND == MAX_DIM):
        fails.append("the harness's dimension bound (_strict_capacity/_strict_dims "
                     "DIM_BOUND) is not Decide.v's max_dim (C-100)")
    for want, what in CAPACITY_ACCOUNT:
        if want not in code_d:
            fails.append(f"Decide.v: {what} is not the pinned account `{want}` (C-94)")
    if not re.search(r"Definition in_strict_doc .*\n.*bounded C \(flatten_doc d\) = true",
                     decide_v):
        fails.append("Decide.v: in_strict_doc no longer requires `bounded` (C-86, C-94)")
    # slice A: an argument that does not close before \end{document} or the
    # end of the stream is outside the tier (pdfTeX reads on past what the
    # fragment models), and so is a one-argument command without its brace
    if not re.search(r"Definition in_strict_toks .*\n.*wfa C 0 ts = true\.", decide_v):
        fails.append("Decide.v: in_strict_toks no longer requires `wfa` (slice A: "
                     "arguments well formed)")
    b = fam.get("BOUND", {})
    if b.get("n", 0) < 6 or b.get("agree") != b.get("n"):
        fails.append(f"rule_probes: BOUND family {b.get('agree')}/{b.get('n')} agree "
                     f"(at least 6, all agreeing)")
    if sum(1 for r in rp.get("outside_tier", []) if r.get("family") == "BOUND-OUT") < 2:
        fails.append("rule_probes: fewer than 2 BOUND-OUT documents outside the tier")
    for n, h in sorted(asigs.items()):
        for w in ("text", "math"):
            if h[w][0] == "run" and not (len(h[w]) == (4 if w == "text" else 3)
                                         and isinstance(run_groups(h[w], w), int)
                                         and run_groups(h[w], w) >= 0):
                fails.append(f"arg signatures: {n!r} runs in {w} without its measured "
                             f"TeX groups (C-94)")
            elif h[w][0] == "run":
                gm = derived_groups(asig.get("capacity", {}), n, w)
                if gm != run_groups(h[w], w):
                    fails.append(f"arg signatures: {n!r}'s groups in {w} "
                                 f"({run_groups(h[w], w)}) are not what stage G's graded "
                                 f"depths give ({gm}; M-2)")
    # 13. THE MEMORY ACCOUNT IS RECOMPUTED FROM PRIMARY RECORDS (C-98)
    fails += memory_findings(sig, asig)
    # 14. THE DIMENSION ACCOUNT IS RE-DERIVED FROM PRIMARY RECORDS (C-100)
    fails += dims_findings(repo, sig, asig)
    # 11. THE CAPACITY ACCOUNT IS PROBED (C-94)
    fails += capacity_findings(repo, ext_sha, sha(sig_path),
                               sha(asig_path) if asig else None, asigs, extract)
    capd = json.loads((repo / CAPACITY).read_text()) if (repo / CAPACITY).is_file() else {}
    for res, (used, of, where) in sorted(capacity_table(capd, sig, asig).items()):
        if used * 2 > of:
            fails.append(f"capacity: {res}: {used} of {of} used by a graded document "
                         f"({where}), more than half (C-94/C-98 margin)")
    # 12. REUSE PROVENANCE (LOW-2 of the C-94 review): every reused grade comes
    # from a committed file, named by path, commit and sha256
    fails += reuse_findings(repo, "signatures", sig.get("reuse"))
    if asig:
        fails += reuse_findings(repo, "arg signatures", asig.get("reuse"))
    fails += reuse_findings(repo, "rule_probes", rp.get("reuse"))
    fails += reuse_findings(repo, "differential", df.get("reuse"))

    # 10. Faithful's body is pinned (OPEN-121 review M-1)
    fails += faithful_findings((repo / "proofs/Strict/Bridge.v").read_text())

    if fails:
        for m in fails:
            print(f"FAIL {m}")
        print(f"[strict-kernel] FAIL — {len(fails)} finding(s)")
        return 1
    print(f"[strict-kernel] OK — {len(ctors)} constructors of Runs/Scans/Stops, each "
          f"probe-tagged and attested ({len(dormant)} dormant under the contract: "
          f"{dormant}); {rp['summary']['graded']} rule probes and "
          f"{df['summary']['graded']} differential documents agree with the oracle; "
          f"branch matrix {len(need_ok)} + {len(need_out)} cells covered; "
          f"{len(sigs)} signatures and {len(asigs)} argument signatures by their "
          f"selection rules, every one inert and clock-free, with complete evidence")
    return 0


if __name__ == "__main__":
    sys.exit(main())
