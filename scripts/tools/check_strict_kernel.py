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
  6. EVERY ADMITTED NAME IS INERT (RULE R-INERT above, C-85): the signature
     file records the meaning at body start of every candidate and of every
     name their expansion texts reach; the closure must be complete, and
     `inertness_violation` must be None for every admitted name.
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
  9. CAPACITY BOUNDS (C-86). Decide.v defines max_brace_depth and max_tokens
     and pins them (Examples) at the values this gate and the generators use,
     the rule probes' BOUND family (the structure at the bounds) agrees with
     the oracle, and its BOUND-OUT documents are outside the tier.
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
 11. NO ADMITTED NAME READS THE CLOCK (RULE R-CLOCK below, OPEN-118 known
     limit (b)): no admitted name is, or expands through its recorded
     meaning closure to, \\year/\\month/\\day/\\time or a date-dependent name
     of the kernel file, so oracle_ok on the fragment cannot depend on the
     day it is graded (MEASURED clock-independent, see the rule's comment).

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
DIFFERENTIAL = "corpora/strict_s0/differential_v2.json"
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

# The kernel's capacity bounds (proofs/Strict/Decide.v, C-86). Checked below
# against the Coq source: the definitions and their pinning Examples.
MAX_BRACE_DEPTH = 200
MAX_TOKENS = 200 * 100

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
#         deferred execution, \immediate, \scantokens). The closure follows
#         every token of letters and @ in an expansion text to its recorded
#         meaning, transitively. It does not follow a name holding other
#         characters (\T1\IJ, \?-cmd): a screen, not a proof, recorded in
#         §I.4; the probes (follower, repetition, interleaving) remain the
#         behavioural check.
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
)
STRUCTURAL_CHARACTER_MEANINGS = (
    "begin-group character", "end-group character", "math shift character",
    "alignment tab character", "macro parameter character",
    "superscript character", "subscript character",
)
_MACRO = re.compile(r"^((?:\\(?:long|protected|outer) )*)macro:(.*?)->(.*)$", re.S)
_REGISTER = re.compile(r"^\\(count|dimen|skip|muskip|toks)\d+$")
_TOKEN = re.compile(r"\\([A-Za-z@]+)")


def _conditional(p: str) -> bool:
    return p.startswith("if") or p in {"else", "fi", "or", "unless"}


def body_tokens(meaning: str) -> list[str] | None:
    """The letter/@ control-word names of a macro's expansion text (None if
    the meaning is not a macro)."""
    m = _MACRO.match(meaning)
    return _TOKEN.findall(m.group(3)) if m else None


def primitive_of(meaning: str | None, primitives: set[str]) -> str | None:
    if meaning and meaning.startswith("\\") and meaning[1:] in primitives:
        return meaning[1:]
    return None


def closure(name: str, meanings: dict[str, str]) -> tuple[set[str], set[str]]:
    """(the macros reached from `name` through expansion texts, the tokens
    met without a recorded meaning)."""
    seen, missing, stack = set(), set(), [name]
    while stack:
        x = stack.pop()
        if x in seen:
            continue
        if x not in meanings:
            missing.add(x)
            continue
        seen.add(x)
        for t in body_tokens(meanings[x]) or ():
            stack.append(t)
    return seen, missing


def inertness_violation(name: str, meanings: dict[str, str],
                        primitives: set[str]) -> str | None:
    """None when `name` is inert by RULE R-INERT, else the reason. Raises
    KeyError when the recorded closure of meanings is incomplete."""
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
    toks = body_tokens(meaning)
    if toks is None:
        return None
    if _MACRO.match(meaning).group(3).strip() == "":
        return "macro with an empty expansion text (transparent to expansion)"
    opens = sum(1 for t in toks if t.startswith("if") or t == "unless")
    closes = sum(1 for t in toks if t == "fi")
    if opens != closes:
        return (f"macro whose expansion text has unbalanced conditionals "
                f"({opens} if-tokens, {closes} \\fi)")
    reached, missing = closure(name, meanings)
    if missing:
        raise KeyError(f"meaning closure of {name} is incomplete: {sorted(missing)[:5]}")
    for x in sorted(reached):
        for t in body_tokens(meanings[x]) or ():
            q = primitive_of(meanings.get(t), primitives)
            if q is not None and (q in MACRO_STATE_CHANGERS or q.startswith("tracing")):
                via = "" if x == name else f" via \\{x}"
                return f"expansion reaches \\{q}{via} (state-changing)"
    return None


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
# limit applies: a name of non-letter characters is not followed (§I.4).
# ---------------------------------------------------------------------------
CLOCK_PRIMITIVES = frozenset(("year", "month", "day", "time"))


def clock_violation(name: str, meanings: dict[str, str], primitives: set[str],
                    date_names=()) -> str | None:
    """None when `name` reads no clock by RULE R-CLOCK, else the reason.
    Raises KeyError when the recorded closure of meanings is incomplete."""
    p = primitive_of(meanings[name], primitives)
    if p in CLOCK_PRIMITIVES:
        return f"it is the clock primitive \\{p}"
    if name in date_names:
        return "it is a date-dependent name of the kernel file"
    reached, missing = closure(name, meanings)
    if missing:
        raise KeyError(f"meaning closure of {name} is incomplete: {sorted(missing)[:5]}")
    dated = [re.compile(r"\\" + re.escape(d) + r"(?![A-Za-z@_:])") for d in date_names]
    for x in sorted(reached):
        via = "" if x == name else f" via \\{x}"
        for t in body_tokens(meanings[x]) or ():
            q = primitive_of(meanings.get(t), primitives)
            if q in CLOCK_PRIMITIVES:
                return f"expansion reaches the clock primitive \\{q}{via}"
        m = _MACRO.match(meanings[x])
        for d, rx in zip(date_names, dated):
            if m and rx.search(m.group(3)):
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
    the stream right after it ([t]), or a premise inspects the rest."""
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
            # a premise other than the recursive Runs one that mentions rest
            inspects = any(re.search(r"\brest\b", seg) and "Runs C" not in seg
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
# frame constructor (Semantics.v) -> head labels; "top" is the empty stack
FRAME_LABELS = {"FSimple": ["simple"], "FShift": ["inline", "display"],
                "FMGroup": ["mgroup"]}
MATH_HEADS = {"inline", "display", "mgroup"}


def _cls(b) -> str:
    return b if isinstance(b, str) else "fatal." + b[1]


def required_cells(syntax: str, sem: str, sigs: dict) -> tuple[set[str], set[str], list[str]]:
    """(cells that must be covered by an agreeing probe, cells that must be
    covered by an outside-the-tier probe, structural findings)."""
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
    heads = ["top"] + [h for f in frames for h in FRAME_LABELS.get(f, [])]
    plain = [lab for t in toks for lab in TOK_LABELS.get(t, [])]
    tcls = sorted({_cls(v["text"]) for v in sigs.values()})
    mcls = sorted({_cls(v["math"]) for v in sigs.values()})
    pairs = sorted({f"{_cls(v['text'])}/{_cls(v['math'])}" for v in sigs.values()})
    followers = plain + ["cs:undef"] + [f"cs:{q}" for q in pairs] + ["eof"]
    need_ok, need_out = set(), set()
    for h in heads:
        math = h in MATH_HEADS
        cs = ["cs:undef"] + [f"cs:{'m' if math else 't'}.{c}" for c in (mcls if math else tcls)]
        for t in plain + cs:
            if t not in reads:
                need_ok.add(f"{h}|{t}|-|-")
                continue
            tails = (["tail-", "tail+"] if math else ["tail-"]) if t in ("sup", "sub") else ["-"]
            for f in followers:
                for tl in tails:
                    cell = f"{h}|{t}|{f}|{tl}"
                    if t in ("sup", "sub") and f not in ("char", "open"):
                        need_out.add(cell)  # Decide.v scripts_ok
                    else:
                        need_ok.add(cell)
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


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=".")
    args = ap.parse_args()
    repo = Path(args.repo).resolve()
    fails: list[str] = []

    sem = (repo / "proofs/Strict/Semantics.v").read_text()
    syntax = (repo / "proofs/Strict/Syntax.v").read_text()
    decide_v = (repo / "proofs/Strict/Decide.v").read_text()
    body = sem[sem.index("Inductive Runs"):]
    ctors = re.findall(r"^\|\s*(R_\w+)\s*:", body, re.M)
    if len(ctors) < 40:
        fails.append(f"Semantics.v: found {len(ctors)} Runs constructors; the parser "
                     f"of this gate is broken or the relation shrank")
    for c in ctors:
        pre = body[:body.index(f"| {c} :")]
        last_comment = pre[pre.rfind("(*"):]
        if f"probe S0/{c}" not in last_comment:
            fails.append(f"Semantics.v: constructor {c} has no `probe S0/{c}` comment "
                         f"directly above it")

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
    rp = json.loads((repo / "corpora/strict_s0/rule_probes.json").read_text())
    fresh("rule_probes", rp, True)
    df = json.loads((repo / DIFFERENTIAL).read_text())
    fresh("differential", df, True)

    fam = rp.get("by_family", {})
    for c in ctors:
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
    if not prims:
        fails.append("kernel file: no primitives list (RULE R-INERT needs it)")
    for n in sorted(sigs):
        if n not in meanings:
            fails.append(f"signatures: admitted {n!r} has no recorded meaning (R-INERT)")
            continue
        try:
            v = inertness_violation(n, meanings, prims)
        except KeyError as e:
            fails.append(f"signatures: {e.args[0]} (R-INERT)")
            continue
        if v:
            fails.append(f"signatures: admitted {n!r} is not inert: {v} (R-INERT)")

    # 11. no admitted name reads the clock (RULE R-CLOCK, OPEN-118 (b))
    missing_clock = sorted(CLOCK_PRIMITIVES - prims)
    if missing_clock:
        fails.append(f"kernel file: the primitives list lacks the clock primitives "
                     f"{missing_clock} (RULE R-CLOCK would be vacuous)")
    date_names = tuple(kern.get("date_dependent_names", []))
    for n in sorted(sigs):
        if n not in meanings:
            continue  # reported by check 6
        try:
            v = clock_violation(n, meanings, prims, date_names)
        except KeyError:
            continue  # reported by check 6
        if v:
            fails.append(f"signatures: admitted {n!r} reads the clock: {v} (R-CLOCK)")

    # 7. branch matrix
    need_ok, need_out, finds = required_cells(syntax, sem, sigs)
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

    # 9. capacity bounds
    for pin in ("Example max_brace_depth_is_200 : max_brace_depth = 200.",
                "Example max_tokens_is_20000 : max_tokens = Nat.mul 200 100."):
        if pin not in decide_v:
            fails.append(f"Decide.v: missing the pin `{pin}`")
    if (MAX_BRACE_DEPTH, MAX_TOKENS) != (200, 200 * 100):
        fails.append("check_strict_kernel: MAX_BRACE_DEPTH/MAX_TOKENS differ from Decide.v")
    if not re.search(r"Definition in_strict_doc .*\n.*bounded \(flatten_doc d\) = true",
                     decide_v):
        fails.append("Decide.v: in_strict_doc no longer requires `bounded` (C-86)")
    b = fam.get("BOUND", {})
    if b.get("n", 0) < 6 or b.get("agree") != b.get("n"):
        fails.append(f"rule_probes: BOUND family {b.get('agree')}/{b.get('n')} agree "
                     f"(at least 6, all agreeing)")
    if sum(1 for r in rp.get("outside_tier", []) if r.get("family") == "BOUND-OUT") < 2:
        fails.append("rule_probes: fewer than 2 BOUND-OUT documents outside the tier")

    # 10. Faithful's body is pinned (OPEN-121 review M-1)
    fails += faithful_findings((repo / "proofs/Strict/Bridge.v").read_text())

    if fails:
        for m in fails:
            print(f"FAIL {m}")
        print(f"[strict-kernel] FAIL — {len(fails)} finding(s)")
        return 1
    print(f"[strict-kernel] OK — {len(ctors)} Runs constructors, each probe-tagged and "
          f"attested; {rp['summary']['graded']} rule probes and "
          f"{df['summary']['graded']} differential documents agree with the oracle; "
          f"branch matrix {len(need_ok)} + {len(need_out)} cells covered; "
          f"{len(sigs)} signatures by the selection rule, every one inert and "
          f"clock-free, "
          f"with complete follower/repetition evidence")
    return 0


if __name__ == "__main__":
    sys.exit(main())
