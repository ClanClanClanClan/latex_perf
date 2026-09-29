#!/usr/bin/env python3
"""check_print_assumptions.py — assert that every capstone theorem is axiom-free.

WHY THIS EXISTS
---------------
The project's headline verification claim is that the capstones rest on nothing but
the global context — no axioms, no admits, no unproved `Variable`/`Hypothesis`
leaking in through a Section. `Print Assumptions` is the only thing in Coq that can
establish that: the `grep`-based zero-admit gate in proof.yml checks *syntax* in the
proof files, but it cannot see an axiom inherited transitively from a dependency, and
it cannot see a Section hypothesis that was never discharged.

Before this gate, `Print Assumptions` was effectively decorative:

  - Exactly ONE executed site existed, `proofs/BodyTokenFrontEnd.v:1544`. It is a
    *printing* vernacular — it cannot fail a build, so it stayed green no matter what
    it printed. Nothing in CI ever read its output. The file itself conceded the
    point: "checked manually on every release".
  - The other three capstones had NO executed `Print Assumptions` at all — the claims
    at `CompileGuaranteeBridge.v:31`, `CompileGuaranteeExtract.v:15` and
    `LanguageContractExtract.v:20` are comments.

Additionally, `dune build proofs` caches: on a cache hit it prints nothing, so even
grepping the build log would silently pass. This gate therefore invokes `coqc`
directly, once per capstone, against the built theory — so the output is always
produced and always inspected.

WHAT IT CHECKS
--------------
For each capstone, `Print Assumptions` must print exactly "Closed under the global
context". Anything else — an axiom list, a Section variable, a missing constant — is
a failure, and the offending assumptions are echoed so the break is actionable.

It also pins, by coqc's own output: the STATEMENT of the strict bridge corollary
(`Check`) and the BODY of the premise it names (`Print Faithful`, BODY_PINS).
The body pin exists because a pinned statement cannot see what a premise
MEANS: the OPEN-121 final review redefined Faithful as `oracle_ok (render d)
<-> decide C d = ProvenReady` (the corollary then proves decide = decide),
and `Check` printed the same statement while Print Assumptions stayed Closed.
`Print` shows the ELABORATED body with SHORTEST unambiguous names, so a
top-level local shadowing of `Runs` or `flatten_doc` changes the output but a
shadow MODULE named `Semantics` does not (C-87); the body must further
mention Semantics.Runs and no Decide.* constant. The textual twin of this pin
(pure, kill-tested) is check 10 of check_strict_kernel.py.

`Print` resolves names but prints them SHORT, so a shadow module named
`Semantics` inside Bridge.v prints `Semantics.Runs` too (re-review MEDIUM-1).
The last arm (CONVERTIBILITY_PINS) therefore asks the KERNEL: `eq_refl :
Faithful = <term>` with every name fully qualified, in a file that Requires
the library without Importing it. The same arm checks the TYPES of both
bridge corollaries against fully qualified statements (re-review 2, HIGH-1,
C-88: a shadow `in_strict_doc := False` in Bridge.v printed the pinned
statement), and `Print Module` must list exactly Bridge's three constants.
BridgeBytes.v (M2 phase 2) is pinned the same way: FaithfulBytes' body, both
bytes corollaries' printed statements and fully qualified types, and its
field list (the bytes PR's review, LOW-2; MEASURED on a build with a
`Time`-prefixed shadow `in_strict_bytes := False`: both printed statement
pins passed, both type pins and the field list failed).

USAGE
    python3 scripts/tools/check_print_assumptions.py [--repo .] [--build]

`--build` runs `dune build proofs` first; omit it in CI where the proofs were just
built (avoids a redundant multi-minute rebuild and any dune lock contention).

Exit 0 if every capstone is closed; exit 1 otherwise.
"""

from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

CLOSED = "Closed under the global context"


def resolve_tool(name: str, repo: Path) -> str:
    """Absolute path to an opam-installed binary.

    Resolved ONCE, from the repo root, because `opam exec` infers the switch from
    the CURRENT DIRECTORY. CI uses a repo-local switch (`_opam/`), so invoking
    `opam exec -- coqc` from a temp working directory fails with "No switch is
    currently set". Resolving here and calling the binary directly makes the
    later invocations cwd-independent (and skips an opam round-trip each time)."""
    r = subprocess.run(
        ["opam", "exec", "--", "which", name],
        cwd=repo, capture_output=True, text=True,
    )
    path = (r.stdout or "").strip().splitlines()
    if r.returncode == 0 and path and Path(path[-1]).exists():
        return path[-1]
    fallback = shutil.which(name)
    if fallback:
        return fallback
    raise SystemExit(
        f"[print-assumptions] FATAL: cannot locate `{name}`. Tried `opam exec -- which "
        f"{name}` from {repo} and PATH."
    )

# (theorem, module to Require, why it matters)
CAPSTONES = [
    (
        "PdflatexFatalChannels.model_fatal_iff",
        "LaTeXPerfectionist.PdflatexFatalChannels",
        "D1: model_fatal holds IFF one of exactly three syntactic channels does. "
        "This is the ONLY-IF half PdflatexModel.v lacks -- it is what licenses "
        "saying the three channels are EXHAUSTIVE *within the model's image of a "
        "project*. It does NOT say 'nothing else a document contains': what a "
        "document contains reaches the model only through the OCaml encoder, "
        "which is outside Coq, so a feature the encoder never turns into a token "
        "or an edge is invisible to this theorem. If it ever rests on an axiom, "
        "every completeness claim built on it is void.",
    ),
    (
        "BodyTokenFrontEnd.compile_safe_of_source",
        "LaTeXPerfectionist.BodyTokenFrontEnd",
        "bytes -> verdict: connects a body built by the EXTRACTED front-end to "
        "pdflatex_compile_safe. This is the theorem about the code that actually runs.",
    ),
    (
        "CompileGuaranteeBridge.project_wf_dec_compile_safe",
        "LaTeXPerfectionist.CompileGuaranteeBridge",
        "the decidable checker (project_closed_b && features && nodup) implies the "
        "model-level compile-safety theorem.",
    ),
    (
        "CompileGuaranteeBridge.project_wf_dec_compile_safe_modulo_label_uniqueness",
        "LaTeXPerfectionist.CompileGuaranteeBridge",
        "C1: the checker WITHOUT the nodup conjunct still implies the full "
        "compile-safety conclusion. This is the theorem that licenses certifying "
        "a document carrying duplicate \\label keys, so it must stay axiom-free "
        "for the shipped verdict to mean anything.",
    ),
    (
        "PdflatexModel.pdflatex_compile_safe",
        "LaTeXPerfectionist.PdflatexModel",
        "the headline model theorem: well-typed project + supported profile => "
        "pdflatex succeeds.",
    ),
    (
        "LanguageContract.classify_lp_core_sound",
        "LaTeXPerfectionist.LanguageContract",
        "the LP-Core tier decision is sound (feature-list -> tier step).",
    ),
    # The strict-tier kernel L_S0 (ADR-012, milestone M2 phase 1; proofs/Strict).
    (
        "LaTeXPerfectionist.Strict.Decide.strict_decider_exact",
        "LaTeXPerfectionist.Strict.Decide",
        "ADR-012 trust layer (2): the extracted decider equals the declarative "
        "semantics Runs in BOTH directions (READY iff Runs Compiles; NOT-READY r l "
        "iff Runs Fatal r l). Every PROVEN verdict of the strict tier rests on it.",
    ),
    (
        "LaTeXPerfectionist.Strict.Decide.runs_deterministic",
        "LaTeXPerfectionist.Strict.Decide",
        "the semantics Runs gives a document at most one outcome (proved on the "
        "relation itself, not through the decider).",
    ),
    (
        "LaTeXPerfectionist.Strict.Decide.runs_total",
        "LaTeXPerfectionist.Strict.Decide",
        "every strict document has an outcome, so the decider never answers "
        "NotStrict inside the tier.",
    ),
    # ADR-012 step 2, slice A: the two relations Runs now concludes through.
    (
        "LaTeXPerfectionist.Strict.Decide.scans_deterministic",
        "LaTeXPerfectionist.Strict.Decide",
        "the argument scanner Scans (where an error inside an argument is "
        "reported) gives at most one outcome, proved on the relation itself.",
    ),
    (
        "LaTeXPerfectionist.Strict.Decide.stops_deterministic",
        "LaTeXPerfectionist.Strict.Decide",
        "Stops (stop now, or defer to the argument's end) gives at most one "
        "outcome.",
    ),
    (
        "LaTeXPerfectionist.Strict.Decide.decide_total",
        "LaTeXPerfectionist.Strict.Decide",
        "the tree decider never answers NotStrict inside the tier (with the "
        "argument well-formedness condition wfa in the membership).",
    ),
    # C-94: the capacity account. The group bound is a bound over every state
    # the run reaches, not a proxy over the token stream.
    (
        "LaTeXPerfectionist.Strict.Decide.peak_spec",
        "LaTeXPerfectionist.Strict.Decide",
        "C-94: the peak the membership bounds is the most TeX groups any state "
        "the run reaches holds (Reaches, a declarative relation over step).",
    ),
    (
        "LaTeXPerfectionist.Strict.Decide.strict_groups_bounded",
        "LaTeXPerfectionist.Strict.Decide",
        "C-94: every state the run of a strict document reaches holds at most "
        "max_groups TeX groups (a formula and an argument's groups included).",
    ),
    (
        "LaTeXPerfectionist.Strict.Decide.in_strict_dec",
        "LaTeXPerfectionist.Strict.Decide",
        "membership in the strict fragment is decidable.",
    ),
    (
        "LaTeXPerfectionist.Strict.Bridge.strict_ready_iff_pdflatex",
        "LaTeXPerfectionist.Strict.Bridge",
        "ADR-012 bridge: under the named premise Faithful (a Definition, never an "
        "Axiom), PROVEN READY iff the oracle compiles. An Axiom here would make "
        "faithfulness an unstated assumption of every strict verdict.",
    ),    (
        "LaTeXPerfectionist.Strict.Bridge.strict_not_ready_pdflatex",
        "LaTeXPerfectionist.Strict.Bridge",
        "the NOT-READY side of the bridge under the same premise (OPEN-121 "
        "re-review 2: it was neither Closed-checked nor statement-pinned).",
    ),
    # M2 phase 2: the decision on the BYTES of a file (proofs/Strict/Lexer.v,
    # Front.v, DecideBytes.v, BridgeBytes.v).
    (
        "LaTeXPerfectionist.Strict.Lexer.lex_exact",
        "LaTeXPerfectionist.Strict.Lexer",
        "the executable lexer equals the declarative reading of a file (TeX Live's "
        "lines, states N/M/S, comments, control sequences) in both directions.",
    ),
    (
        "LaTeXPerfectionist.Strict.Lexer.lexfile_deterministic",
        "LaTeXPerfectionist.Strict.Lexer",
        "a file is read one way only.",
    ),
    (
        "LaTeXPerfectionist.Strict.Front.parse_exact",
        "LaTeXPerfectionist.Strict.Front",
        "the executable parser (front matter, body, kernel tokens with lines) equals "
        "the declarative Parse in both directions.",
    ),
    (
        "LaTeXPerfectionist.Strict.Front.parse_deterministic",
        "LaTeXPerfectionist.Strict.Front",
        "a file parses one way at most.",
    ),
    (
        "LaTeXPerfectionist.Strict.DecideBytes.in_strict_bytes_dec",
        "LaTeXPerfectionist.Strict.DecideBytes",
        "membership of a file in the strict fragment is decidable.",
    ),
    (
        "LaTeXPerfectionist.Strict.DecideBytes.decide_bytes_exact",
        "LaTeXPerfectionist.Strict.DecideBytes",
        "ADR-012 trust layer (2) on bytes: READY iff Runs Compiles, and NOT-READY r "
        "on line ln iff Runs Fatal r l with ln the declarative reported line (the "
        "line of the last token the outcome depends on).",
    ),
    (
        "LaTeXPerfectionist.Strict.DecideBytes.decide_bytes_not_strict_iff",
        "LaTeXPerfectionist.Strict.DecideBytes",
        "the bytes decider answers NotStrict exactly outside the fragment.",
    ),
    (
        "LaTeXPerfectionist.Strict.DecideBytes.determined_threshold_unique",
        "LaTeXPerfectionist.Strict.DecideBytes",
        "the reported token of a NOT-READY is unique (the declarative location is "
        "a function of the outcome).",
    ),
    (
        "LaTeXPerfectionist.Strict.BridgeBytes.strict_ready_iff_pdflatex_bytes",
        "LaTeXPerfectionist.Strict.BridgeBytes",
        "ADR-012 bridge on bytes: under the named premise FaithfulBytes (a "
        "Definition, never an Axiom), PROVEN READY on a file iff the oracle "
        "compiles that file.",
    ),
    (
        "LaTeXPerfectionist.Strict.BridgeBytes.strict_not_ready_pdflatex_bytes",
        "LaTeXPerfectionist.Strict.BridgeBytes",
        "under FaithfulBytes, a file the bytes decider rejects does not compile.",
    ),
]

# The bridge corollary's STATEMENT, pinned (design §0: "a new gate checks the
# corollary's statement textually, so that Faithful is its only non-structural
# premise"). Print Assumptions cannot see a premise: a premise is part of the
# statement, and a Closed theorem may still assume anything in its hypotheses.
# `Check` prints the statement; whitespace is normalised before comparing.
STATEMENT_PINS = [
    (
        "LaTeXPerfectionist.Strict.Bridge.strict_ready_iff_pdflatex",
        "LaTeXPerfectionist.Strict.Syntax LaTeXPerfectionist.Strict.Contract "
        "LaTeXPerfectionist.Strict.Decide LaTeXPerfectionist.Strict.Bridge",
        "forall (oracle_ok : list Ascii.ascii -> Prop) (C : contract) (d : doc), "
        "Faithful oracle_ok C -> in_strict_doc C d -> "
        "decide C d = ProvenReady <-> oracle_ok (render d)",
    ),
    (
        "LaTeXPerfectionist.Strict.BridgeBytes.strict_ready_iff_pdflatex_bytes",
        "LaTeXPerfectionist.Strict.Syntax LaTeXPerfectionist.Strict.Contract "
        "LaTeXPerfectionist.Strict.Decide LaTeXPerfectionist.Strict.DecideBytes "
        "LaTeXPerfectionist.Strict.BridgeBytes",
        "forall (oracle_ok : list Ascii.ascii -> Prop) (C : bcontract) (b : list Ascii.ascii), "
        "FaithfulBytes oracle_ok C -> in_strict_bytes C b -> "
        "decide_bytes C b = ProvenReady <-> oracle_ok b",
    ),
    # The bytes PR's review, LOW-2: the NOT-READY side on bytes pinned too,
    # as the kernel pins strict_not_ready_pdflatex (C-88).
    (
        "LaTeXPerfectionist.Strict.BridgeBytes.strict_not_ready_pdflatex_bytes",
        "LaTeXPerfectionist.Strict.Syntax LaTeXPerfectionist.Strict.Contract "
        "LaTeXPerfectionist.Strict.Decide LaTeXPerfectionist.Strict.DecideBytes "
        "LaTeXPerfectionist.Strict.BridgeBytes",
        "forall (oracle_ok : list Ascii.ascii -> Prop) (C : bcontract) (b : list Ascii.ascii) "
        "(r : reason) (ln : nat), "
        "FaithfulBytes oracle_ok C -> in_strict_bytes C b -> "
        "decide_bytes C b = ProvenNotReady r ln -> ~ oracle_ok b",
    ),
]


# (constant, modules to Require, the pinned `Print` output up to `Arguments`,
#  identifiers the body MUST mention, identifier prefixes it must NOT mention)
BODY_PINS = [
    (
        "LaTeXPerfectionist.Strict.Bridge.Faithful",
        "LaTeXPerfectionist.Strict.Bridge",
        "Faithful = fun (oracle_ok : list Ascii.ascii -> Prop) (C : Contract.contract) "
        "=> forall d : Syntax.doc, Decide.in_strict_doc C d -> "
        "oracle_ok (Syntax.render d) <-> "
        "Semantics.Runs C Semantics.init (Syntax.flatten_doc d) Semantics.Compiles "
        ": (list Ascii.ascii -> Prop) -> Contract.contract -> Prop",
        ["Semantics.Runs"],
        # Decide.in_strict_doc is the structural membership premise; any other
        # Decide.* constant (decide, run, step, ...) is the decider itself.
        ["Decide.decide", "Decide.run", "Decide.step", "Semantics.step",
         "Semantics.run"],
    ),
    (
        "LaTeXPerfectionist.Strict.BridgeBytes.FaithfulBytes",
        "LaTeXPerfectionist.Strict.BridgeBytes",
        "FaithfulBytes = fun (oracle_ok : list Ascii.ascii -> Prop) "
        "(C : DecideBytes.bcontract) => forall (b : list Ascii.ascii) "
        "(ks : list Front.ktok), DecideBytes.in_strict_bytes C b -> "
        "Front.Parse (DecideBytes.bc_lex C) b ks -> oracle_ok b <-> "
        "Semantics.Runs (DecideBytes.bc_kernel C) Semantics.init (Front.toks_of ks) "
        "Semantics.Compiles : (list Ascii.ascii -> Prop) -> DecideBytes.bcontract -> Prop",
        ["Semantics.Runs", "Front.Parse"],
        # DecideBytes.in_strict_bytes is the structural membership premise; the
        # decider, the executable reader and parser are never its content.
        ["DecideBytes.decide_bytes", "DecideBytes.rd", "Decide.decide", "Decide.run",
         "Decide.step", "Front.parse", "Front.front", "Front.body", "Front.prologue",
         "Lexer.lex", "Lexer.lexl", "Lexer.lex_lines", "DecideBytes.in_strict_bytes_b"],
    ),
]

# (constant, module to Require WITHOUT Import, the term it must be convertible
#  to, every name FULLY QUALIFIED). The printed body pin above is not enough:
# the OPEN-121 re-review (MEDIUM-1) put `Module Semantics. Definition Runs ...
# := run C s ts = Some o. End Semantics. Import Semantics.` on Bridge.v's
# Require line, and coqc's `Print` still showed `Semantics.Runs` -- resolved to
# the shadow LaTeXPerfectionist.Strict.Bridge.Semantics.Runs. A kernel
# `eq_refl` against fully qualified names cannot be satisfied by a shadow: the
# shadow's constant is a different constant, and it unfolds to the decider.
_S = "LaTeXPerfectionist.Strict."
_LIST_ASCII = "Coq.Init.Datatypes.list Coq.Strings.Ascii.ascii"
# (constant, module to Require WITHOUT Import, kind, term). kind "body": the
# constant must be convertible to the term (`eq_refl : c = term`); kind
# "type": the constant must have the term as its type (`c : term`, kernel
# conversion). Every name is FULLY QUALIFIED.
#
# The "type" rows exist because the printed STATEMENT_PINS above compare a
# RENDERING of the statement, the class C-87 records for the body: the
# OPEN-121 re-review 2 (HIGH-1) defined a shadow `in_strict_doc := False`
# inside Bridge.v, after Faithful and before the corollary (hidden from the
# textual check by a `Time` prefix, and separately by a comment that holds a
# string with a comment delimiter), and `Check` still printed
# `in_strict_doc C d` -- the corollary was vacuous (premise False) and every
# printed pin passed. Against a fully qualified type in a Require-only file,
# a shadow constant is another constant and does not convert.
CONVERTIBILITY_PINS = [
    (
        _S + "Bridge.Faithful",
        _S + "Bridge",
        "body",
        f"fun (oracle_ok : {_LIST_ASCII} -> Prop) "
        f"(C : {_S}Contract.contract) => "
        f"forall d, {_S}Decide.in_strict_doc C d -> "
        f"(oracle_ok ({_S}Syntax.render d) <-> "
        f"{_S}Semantics.Runs C {_S}Semantics.init "
        f"({_S}Syntax.flatten_doc d) {_S}Semantics.Compiles)",
    ),
    (
        _S + "Bridge.strict_ready_iff_pdflatex",
        _S + "Bridge",
        "type",
        f"forall (oracle_ok : {_LIST_ASCII} -> Prop) "
        f"(C : {_S}Contract.contract) (d : {_S}Syntax.doc), "
        f"{_S}Bridge.Faithful oracle_ok C -> "
        f"{_S}Decide.in_strict_doc C d -> "
        f"({_S}Decide.decide C d = {_S}Decide.ProvenReady "
        f"<-> oracle_ok ({_S}Syntax.render d))",
    ),
    (
        _S + "Bridge.strict_not_ready_pdflatex",
        _S + "Bridge",
        "type",
        f"forall (oracle_ok : {_LIST_ASCII} -> Prop) "
        f"(C : {_S}Contract.contract) (d : {_S}Syntax.doc) "
        f"(r : {_S}Contract.reason) (l : Coq.Init.Datatypes.nat), "
        f"{_S}Bridge.Faithful oracle_ok C -> "
        f"{_S}Decide.in_strict_doc C d -> "
        f"{_S}Decide.decide C d = {_S}Decide.ProvenNotReady r l -> "
        f"Coq.Init.Logic.not (oracle_ok ({_S}Syntax.render d))",
    ),
    (
        _S + "BridgeBytes.FaithfulBytes",
        _S + "BridgeBytes",
        "body",
        f"fun (oracle_ok : {_LIST_ASCII} -> Prop) "
        f"(C : {_S}DecideBytes.bcontract) => "
        f"forall b ks, {_S}DecideBytes.in_strict_bytes C b -> "
        f"{_S}Front.Parse ({_S}DecideBytes.bc_lex C) b ks -> "
        f"(oracle_ok b <-> {_S}Semantics.Runs "
        f"({_S}DecideBytes.bc_kernel C) {_S}Semantics.init "
        f"({_S}Front.toks_of ks) {_S}Semantics.Compiles)",
    ),
    # Both bytes corollaries' TYPES, fully qualified (the bytes PR's review,
    # LOW-2: the rule C-88 applied to Bridge.v, applied to BridgeBytes.v).
    (
        _S + "BridgeBytes.strict_ready_iff_pdflatex_bytes",
        _S + "BridgeBytes",
        "type",
        f"forall (oracle_ok : {_LIST_ASCII} -> Prop) "
        f"(C : {_S}DecideBytes.bcontract) (b : {_LIST_ASCII}), "
        f"{_S}BridgeBytes.FaithfulBytes oracle_ok C -> "
        f"{_S}DecideBytes.in_strict_bytes C b -> "
        f"({_S}DecideBytes.decide_bytes C b = {_S}Decide.ProvenReady "
        f"<-> oracle_ok b)",
    ),
    (
        _S + "BridgeBytes.strict_not_ready_pdflatex_bytes",
        _S + "BridgeBytes",
        "type",
        f"forall (oracle_ok : {_LIST_ASCII} -> Prop) "
        f"(C : {_S}DecideBytes.bcontract) (b : {_LIST_ASCII}) "
        f"(r : {_S}Contract.reason) (ln : Coq.Init.Datatypes.nat), "
        f"{_S}BridgeBytes.FaithfulBytes oracle_ok C -> "
        f"{_S}DecideBytes.in_strict_bytes C b -> "
        f"{_S}DecideBytes.decide_bytes C b = {_S}Decide.ProvenNotReady r ln -> "
        f"Coq.Init.Logic.not (oracle_ok b)",
    ),
]

# The kernel's own list of what Bridge.v defines (`Print Module`, one field
# per line at the first indentation of `Struct`): exactly these, so a shadow
# constant, module, inductive or axiom inside Bridge.v fails here whatever
# the text of Bridge.v looks like (re-review 2, HIGH-1). A Notation is not a
# module field; it cannot reach the Require-only kernel pins above.
MODULE_FIELDS = [
    (
        _S + "Bridge",
        [("Definition", "Faithful"),
         ("Parameter", "strict_ready_iff_pdflatex"),
         ("Parameter", "strict_not_ready_pdflatex")],
    ),
    # BridgeBytes.v likewise (the bytes PR's review, LOW-2).
    (
        _S + "BridgeBytes",
        [("Definition", "FaithfulBytes"),
         ("Parameter", "strict_ready_iff_pdflatex_bytes"),
         ("Parameter", "strict_not_ready_pdflatex_bytes")],
    ),
]


def module_fields(out: str) -> list[tuple[str, str]] | None:
    """(kind, name) of every field of a `Print Module` of a plain Struct, or
    None if the output is not a plain `Module M := Struct ... End`."""
    lines = [ln for ln in out.splitlines() if ln.strip()]
    text = " ".join(" ".join(lines).split())
    if not re.match(r"^Module \S+ := Struct ", text) or not text.endswith(" End"):
        return None
    fields = []
    for ln in lines:
        m = re.match(r"^ {5}(\S+) (\S+)", ln)
        if m:
            fields.append((m.group(1), m.group(2)))
    return fields


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=".")
    ap.add_argument(
        "--build", action="store_true", help="run `dune build proofs` before checking"
    )
    ap.add_argument(
        "--vodir", default=None,
        help="built proofs directory (default <repo>/_build/default/proofs); "
             "lets a kill-test point the gate at a mutated build")
    args = ap.parse_args()
    repo = Path(args.repo).resolve()

    coqc = resolve_tool("coqc", repo)

    if args.build:
        print("[print-assumptions] building proofs ...")
        r = subprocess.run(
            ["opam", "exec", "--", "dune", "build", "proofs"], cwd=repo
        )
        if r.returncode != 0:
            print("[print-assumptions] FAIL: `dune build proofs` failed", file=sys.stderr)
            return 1

    vodir = (Path(args.vodir).resolve() if args.vodir
             else repo / "_build" / "default" / "proofs")
    gendir = vodir / "generated"
    if not vodir.is_dir():
        print(
            f"[print-assumptions] FAIL: {vodir} not found — build the proofs first "
            f"(`dune build proofs`, or pass --build).",
            file=sys.stderr,
        )
        return 1

    failures: list[str] = []

    with tempfile.TemporaryDirectory(prefix="print-assumptions-") as work:
        workdir = Path(work)
        for idx, (thm, module, why) in enumerate(CAPSTONES):
            src = workdir / f"PA{idx}.v"
            src.write_text(
                f"Require Import {module}.\nPrint Assumptions {thm}.\n",
                encoding="utf-8",
            )
            proc = subprocess.run(
                [
                    coqc,
                    "-R", str(vodir), "LaTeXPerfectionist",
                    "-Q", str(gendir), "LaTeXPerfectionist.Generated",
                    src.name,
                ],
                cwd=workdir,
                capture_output=True,
                text=True,
            )
            out = (proc.stdout or "") + (proc.stderr or "")

            if proc.returncode != 0:
                tail = "\n      ".join(out.strip().splitlines()[-12:])
                failures.append(
                    f"{thm}: coqc failed (exit {proc.returncode})\n      {tail}"
                )
                continue

            if CLOSED in out:
                print(f"[print-assumptions] OK   {thm}: {CLOSED}")
            else:
                # Echo whatever Coq reported instead — that IS the finding.
                reported = "\n      ".join(
                    ln for ln in out.strip().splitlines()
                    if ln.strip() and not ln.startswith("Warning")
                ) or "(no output)"
                failures.append(
                    f"{thm}: NOT closed under the global context.\n"
                    f"      why this theorem matters: {why}\n"
                    f"      Coq reported:\n      {reported}"
                )

        for idx, (thm, module, want) in enumerate(STATEMENT_PINS):
            src = workdir / f"ST{idx}.v"
            src.write_text(f"Require Import {module}.\nCheck {thm}.\n", encoding="utf-8")
            proc = subprocess.run(
                [coqc, "-R", str(vodir), "LaTeXPerfectionist",
                 "-Q", str(gendir), "LaTeXPerfectionist.Generated", src.name],
                cwd=workdir, capture_output=True, text=True,
            )
            out = proc.stdout or ""  # Coq's warnings go to stderr
            # `Check` prints "<name>\n     : <statement>"; keep the statement.
            got = " ".join(out.split(":", 1)[1].split()) if ":" in out else ""
            if proc.returncode != 0 or got != " ".join(want.split()):
                failures.append(
                    f"{thm}: statement is not the pinned one (the bridge's premises "
                    f"changed; Faithful must stay its only non-structural premise).\n"
                    f"      pinned: {' '.join(want.split())}\n      Coq:    {got or out.strip()[:400]}"
                )
            else:
                print(f"[print-assumptions] OK   {thm}: statement pinned")

        for idx, (const, module, want, must, mustnot) in enumerate(BODY_PINS):
            src = workdir / f"BP{idx}.v"
            src.write_text(f"Require Import {module}.\nPrint {const}.\n", encoding="utf-8")
            proc = subprocess.run(
                [coqc, "-R", str(vodir), "LaTeXPerfectionist",
                 "-Q", str(gendir), "LaTeXPerfectionist.Generated", src.name],
                cwd=workdir, capture_output=True, text=True,
            )
            out = proc.stdout or ""  # Coq's warnings go to stderr
            got = " ".join(out.split("Arguments", 1)[0].split())
            short = const.rsplit(".", 1)[1]
            if proc.returncode != 0 or got != " ".join(want.split()):
                failures.append(
                    f"{short}: body is not the pinned one (a premise's statement "
                    f"can stay pinned while its meaning changes; OPEN-121 review M-1).\n"
                    f"      pinned: {' '.join(want.split())}\n"
                    f"      Coq:    {got or out.strip()[:400]}"
                )
            else:
                print(f"[print-assumptions] OK   {const}: body pinned")
            idents = set(re.findall(r"[A-Za-z_][A-Za-z_0-9'.]*", got))
            for m in must:
                if m not in idents:
                    failures.append(f"{short}: body does not mention {m}")
            bad = sorted(i for i in idents for b in mustnot if i == b)
            if bad:
                failures.append(f"{short}: body mentions {bad} -- the decider must "
                                f"never be a premise's content")

        for idx, (const, module, kind, term) in enumerate(CONVERTIBILITY_PINS):
            src = workdir / f"CV{idx}.v"
            # Require, never Import: nothing from the checked library may
            # enter the short-name space the pinned term is read in.
            probe = (f"(eq_refl : {const} = {term})" if kind == "body"
                     else f"({const} : {term})")
            src.write_text(f"Require {module}.\nCheck {probe}.\n", encoding="utf-8")
            proc = subprocess.run(
                [coqc, "-R", str(vodir), "LaTeXPerfectionist",
                 "-Q", str(gendir), "LaTeXPerfectionist.Generated", src.name],
                cwd=workdir, capture_output=True, text=True,
            )
            short = const.rsplit(".", 1)[1]
            what = "body" if kind == "body" else "statement"
            if proc.returncode != 0:
                err = [ln for ln in (proc.stderr or "").splitlines()
                       if ln.strip() and "overriding-logical-loadpath" not in ln]
                tail = "\n      ".join(err[-12:])
                failures.append(
                    f"{short}: {what} not convertible to the pinned fully qualified "
                    f"{what} (a shadowed name prints the same but is another "
                    f"constant; OPEN-121 re-reviews MEDIUM-1 and HIGH-1).\n      {tail}")
            else:
                print(f"[print-assumptions] OK   {const}: {what} convertible to the "
                      f"pinned fully qualified {what}")

        for pm_idx, (mod, want_fields) in enumerate(MODULE_FIELDS):
            src = workdir / f"PM{pm_idx}.v"
            src.write_text(f"Require {mod}.\nPrint Module {mod}.\n", encoding="utf-8")
            proc = subprocess.run(
                [coqc, "-R", str(vodir), "LaTeXPerfectionist",
                 "-Q", str(gendir), "LaTeXPerfectionist.Generated", src.name],
                cwd=workdir, capture_output=True, text=True,
            )
            got_fields = module_fields(proc.stdout or "") if proc.returncode == 0 else None
            if got_fields != want_fields:
                failures.append(
                    f"{mod}: defines other than {want_fields} (OPEN-121 re-review 2, "
                    f"HIGH-1: a constant defined in the bridge file can shadow what the bridge "
                    f"reads).\n      Coq: {got_fields if got_fields is not None else (proc.stdout or proc.stderr or '').strip()[:400]}")
            else:
                print(f"[print-assumptions] OK   {mod}: fields are exactly "
                      f"{[n for _, n in want_fields]}")

    if failures:
        print("\n[print-assumptions] FAIL — capstone(s) depend on unproved assumptions:\n")
        for f in failures:
            print(f"  - {f}\n")
        return 1

    print(
        f"[print-assumptions] PASS — all {len(CAPSTONES)} capstones are closed under "
        f"the global context."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
