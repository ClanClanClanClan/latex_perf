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
     it is in PRE_BASELINE with the ledger row that removes it. EVERY
     tracked JSON file is CLASSIFIED (C-128): GRADED, ORACLE_RECORDS,
     PRE_BASELINE or NO_ORACLE; an unclassified file fails. The block at
     every GRADED and ORACLE_RECORDS LOCATION is checked whatever it
     records (a block stripped of its identity fails, it is not skipped),
     and names the pinned image, the architecture of record and that
     architecture's fingerprints. A broad discovery (any IDENTITY_KEYS key)
     is the second net: a block at any other path fails unless pinned in
     NOT_THE_ORACLE or NOT_A_BLOCK. A GRADED block records the protocol
     clock, and its grading_code names EXACTLY the oracle core and its
     producer's grader (GRADERS), each at its current behaviour.
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
     Makefile/.mk, .ml, other-language and workflow file, any tracked file
     without a known extension whose shebang names a shell or python, and the
     command-running non-script files of `_command_file_kind` (composite
     actions, pre-commit hooks, compose/k8s manifests, Dockerfiles, justfile,
     tox.ini, Procfile, .envrc, package.json, latexmkrc, notebooks).
     WHAT IS MODELLED -- exactly this, each shape with a kill-test in
     check_gate_selftests.py; anything else is a residual (below):
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
               EVALUATED by a small interpreter (no eval): + * % on strings
               (`%` with a tuple or a dict of literals), f-strings, str
               methods (join/format/replace/split/decode/...) called bound or
               unbound (`str.__add__('pdfl', 'atex')`), slicing, chr,
               bytes/str, `map(chr|str, ...)`, `functools.reduce(operator.add,
               ...)`, base64/b16/b32/hex decoding, a comprehension or generator
               over a literal iterable, either branch of a conditional, a
               walrus, a starred operand (so the KEYS of an unpacked dict
               literal, `[*{'-progname=pdflatex': 1}]`, are values), a name
               bound exactly once in the file by `NAME = expr` or by tuple
               unpacking of literals (`a, b = 'pdfl', 'atex'`), and a class
               attribute bound once in its class body (`C.P`). Data positions
               are exempt as for literals.
       shell   a bare engine token anywhere on a code line (comments
               stripped), except inside an echo/printf MESSAGE. A message is
               ONE command (the line is split at `;`, `&&`, `||`, `|` outside
               quotes), and stops being one when (1) a later stage of the
               pipeline RUNS its input -- the stage's argv[0], after wrapper
               commands (`timeout 60`, `nice -n 5`, `env A=b`, `stdbuf -oL`,
               `sudo`, ...) and their options are stripped, is a shell or
               interpreter, `xargs`, `parallel`, awk, or a `while`/`until`
               loop; (2) it holds a command substitution; (3) it is written
               to a file (`> run.sh`; /dev/null, /dev/std*, a descriptor and
               the CI's $GITHUB_* streams are not files); `printf -v` is an
               assignment, and its value is computed. The commands inside
               every `$(...)` and backquote pair (outside single quotes) are
               scanned as commands of their own, wherever they stand. An
               engine the SHELL makes is resolved: assembled from a variable
               followed by an engine's tail (`${P}latex`); a word that expands
               variables the file assigns LITERAL values (`NAME=w`,
               `NAME+=w`, with export/local/readonly/declare; every value
               kept), plain or with `,,`/`^^`/`,`/`^`, `/pat/rep`,
               `//pat/rep`, `:off:len`, `#`/`##`/`%`/`%%` with a literal
               pattern (`${P}${Q}`, `${E,,}`, `${E/X/}`, `${E:1}`); dequoted
               from one word (`"pdf"latex`, `pdf\\latex`, an ANSI-C
               `$'pdf\\x6catex'`); a parameter expansion's default, including
               an indirect or positional one (`${E:-pdftex}`,
               `${!n:-pdftex}`, `${1:-pdftex}`); a brace expansion
               (`pdf{latex,}`); a glob matching an engine name (`pdfla[t]ex`,
               at least three literal letters). A here-document fed to a
               Python interpreter (`python3 - <<'EOF'`) is scanned as Python.
               A `case` label is a pattern; the value of `jq --arg NAME VALUE`
               is data. Makefiles are scanned as shell after make's variables
               with literal values (`P = pdfl`, `+=`, `:=`, `?=`; recursive;
               undefined = empty) are expanded and GNU make's text functions
               over literal arguments are evaluated (`$(subst X,,pdfXlatex)`,
               `$(addprefix ...)`, `$(if C,A,B)`, ...).
       other   in a tracked .c/.h/.rs/.js/.ts/.rb/.pl/.go/.lua file, a
               package.json or a latexmkrc, a quoted literal that is an engine
               or an engine command line.
       OCaml   a file that spawns processes (Sys.command, Unix.system,
               Unix.create_process, Unix.open_process*, Unix.exec*, Unix.fork,
               Lwt_process, Bos.OS/Bos.Cmd, Feather, Shexp_process) must not
               name an engine as a word of a string literal.
       workflow  as shell, minus `name:` keys and YAML mapping KEYS (their
               values are scanned), with an exact allow-list of the in-image
               canary lines of tex-oracle.yml. Composite actions, pre-commit
               hooks, compose files and .github/ and infra/k8s/ YAML likewise.
     KNOWN RESIDUALS (OPEN-118 known limit (g)): a static scan cannot see a
     value that is not a function of the file's literals -- a name read from
     the environment, a file, argv or the network. NOT MODELLED, therefore
     residual: Python -- a variable bound more than once or by a parameter,
     loop, import or augmented assignment; a call the interpreter does not
     model (any function of one's own, `codecs.decode(s, "rot13")`, `ord`
     arithmetic through a loop, `operator.concat` via a variable, a lambda);
     a dict iterated by name (`d = {...}; [*d]`: only a dict LITERAL
     unpacked in place is resolved); `eval`/`exec` of a string built at run
     time; a `DATA_KEYS` value later used as argv; a function of one's own
     named `run_engine`. Shell -- a variable whose value is not a literal
     (`read E`, `E=$(...)`, `E=$X`), an array element, `eval`, `source`/`.`
     of a generated file, a script written to a file by anything other than
     echo/printf (`cat > f <<EOF`, `tee`, `sed`) and run later, `sh -c`/
     `bash -c` of a variable, a pattern with glob characters in `${E/p/r}`.
     make -- target-specific and command-line variables, `define` blocks,
     `$(shell ...)`/`$(call ...)`/`$(eval ...)`/`$(foreach ...)`. Other
     languages: string operations (only literals are scanned there). Files:
     YAML/TOML/JSON/INI outside `_command_file_kind` are treated as DATA and
     not scanned; an untracked file. And `aleph`, the one vocabulary word
     not scanned (SCAN_DATA_WORDS: it is also the LaTeX symbol \\aleph,
     listed as data in this repository).
     MEASURED 2026-09-28 with the round-5 reviewer's harness (51 shapes,
     the reviewer's session scratchpad, not in the repository): 49 caught; the other two (`$(firstword $(subst
     ., ,pdfl.x)atex)` and `$(subst $(space),,$(E))` with `space` undefined)
     do not start an engine under GNU make at all (`make -n` prints `pdfl
     main.tex` and `pdfl atex main.tex`); with `space` defined the second is
     caught.

Run: python3 scripts/tools/check_oracle_pin.py --repo .
"""
from __future__ import annotations

import argparse
import gzip
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
    # OPEN-128 (1): the class census, each run-dependent input observed by a
    # document graded twice (two times, two run directories).
    ("corpora/oracle_baseline/clock_census.json", ("oracle",)),
    # OPEN-128 (8): the same documents graded at one commit on both platforms
    # of the one launch definition (it replaces equivalence.json, the 97/97
    # container-vs-native comparison of the retired native backend).
    ("corpora/oracle_baseline/platform_residuals.json", ("oracle_local",)),
    ("corpora/oracle_baseline/platform_residuals.json", ("oracle_ci",)),
    # The strict kernel L_S0's evidence (ADR-012 M2 phase 1, OPEN-121).
    ("corpora/contracts/strict/article-s0-signatures.json", ("oracle",)),
    ("corpora/strict_s0/rule_probes.json", ("oracle",)),
    ("corpora/strict_s0/differential_v2.json", ("oracle",)),
    # The L_S0 bytes evidence check_strict_bytes holds the FaithfulBytes/PROVEN
    # corollaries against, and the lexical reading it is checked with. They
    # were outside this list until review round 2 of OPEN-126 (C-127): an
    # x86_64 block in either passed every gate.
    ("corpora/strict_s0/bytes_probes.json", ("oracle",)),
    ("corpora/strict_s0/bytes_differential.json", ("oracle",)),
    ("corpora/contracts/strict/article-s0-lexical.json", ("oracle",)),
)

# EVERY OTHER RECORDED ORACLE IDENTITY (C-127). GRADED was a hand list, and
# nothing tied it to the artefacts that actually record an oracle: review
# round 2 set `arch` to x86_64 (with the x86_64 fingerprints) in two L_S0
# evidence files outside it and 36 workflow gates passed. So this gate now
# DISCOVERS every oracle block in every tracked JSON file (`oracle_blocks`:
# a dict holding a tree fingerprint key, an `arch`, or an image named by
# digest), and every block must be EITHER a GRADED entry, OR matched by one
# row below, OR pinned in NOT_THE_ORACLE. An unregistered block fails, and
# so does a row below that matches nothing. Every GRADED block and every
# block matched below must name the pinned image, the architecture of
# record and that architecture's fingerprints (`identity_findings`); GRADED
# adds its version, backend, clock and grading-code checks. A row's `*`
# matches within one path segment. Each row may pin the CLOCK its blocks
# were graded with (None: not checked; contracts record none), and the
# GRADER files its producer must name in `grading_code` beside the oracle
# core (None: the block predates grading_code and must not claim one).
#
# CLASSIFIED BY LOCATION, NOT BY CONTENT (C-128, review round 3). Until then
# a row was only a filter over the blocks the discovery had found, and the
# discovery recognised a block by the very identity fields being checked: a
# contract pin or an O-5 block with its arch and fingerprints deleted was no
# longer a "block", so it was checked by nothing, and the row still matched
# the other files. Now EVERY tracked file a row's glob matches must hold a
# dict at the row's key path, and that dict is checked whatever it records;
# every tracked data file must be classified (NO_ORACLE below, C-129);
# and the discovery is only a second net for blocks at unregistered paths.
ORACLE_RECORDS = (
    # Since OPEN-128 (7) a contract records the clock it was generated under
    # (the protocol's): a contract regenerated under another clock fails.
    ("corpora/contracts/*.json", ("pin",), _oracle.PROTOCOL_CLOCK, None,
     "an M1 contract's generation pin (gen_contract.py)"),
    ("corpora/contracts/kernel/*.json", ("pin",), _oracle.PROTOCOL_CLOCK, None,
     "the kernel name-set a contract's pin refers to (gen_contract.py)"),
    ("corpora/contracts/probes/*.json", ("pin",), _oracle.PROTOCOL_CLOCK, None,
     "a contract's signature probes (gen_contract.py probes)"),
    ("corpora/oracle_baseline/diff_apply_fixes_real_*.json", ("after_oracle",),
     None, None, "OPEN-118 re-grade diff: the oracle of its re-graded side"),
    ("corpora/oracle_baseline/diff_real_roots_sample*.json", ("oracle_after",),
     None, None, "OPEN-118 re-grade diff: the oracle of its re-graded side"),
    ("corpora/oracle_baseline/regrade_open126_sample*.json", ("oracle_before",),
     None, None, "OPEN-126 re-grade diff: the oracle of the grades it re-graded"),
    ("corpora/oracle_baseline/regrade_open126_sample*.json", ("oracle_after",),
     "real", ("scripts/tools/diff_real_roots.py",),
     "OPEN-126 re-grade diff: the protocol re-grade (real clock)"),
    ("corpora/oracle_baseline/o5_forced_clock_sample*.json", ("oracle",),
     "forced", ("scripts/tools/diff_real_roots.py",),
     "OPEN-126 (d): the O-5 experiment, graded with the clock FORCED"),
    ("corpora/oracle_baseline/summary.json", ("oracle",), None, None,
     "OPEN-118: the oracle-baseline change's summary"),
    # OPEN-128 (7): the full re-grade under the fixed clock and the one launch
    # definition. Its BEFORE side is OPEN-126's grade (real clock, recorded
    # grading code); its AFTER side the protocol re-grade.
    ("corpora/oracle_baseline/regrade_open128_sample*.json", ("oracle_before",),
     "real", ("scripts/tools/diff_real_roots.py",),
     "OPEN-128 re-grade diff: the oracle of the grades it re-graded (OPEN-126)"),
    ("corpora/oracle_baseline/regrade_open128_sample*.json", ("oracle_after",),
     _oracle.PROTOCOL_CLOCK, ("scripts/tools/diff_real_roots.py",),
     "OPEN-128 re-grade diff: the protocol re-grade (fixed clock)"),
)

# THE GRADER of every GRADED artefact that records grading_code (C-128,
# review round 3): `grading_code.files` must be EXACTLY the oracle core
# (_oracle.GRADING_CODE_CORE) plus these files. Until then the gate required
# only the core, so a block whose `files` map dropped the grader (sha256
# recomputed) named "its current grading code" while the grader had changed.
# Every GRADED artefact outside GRADING_CODE_PENDING must have an entry.
GRADERS = {
    "corpora/real_roots/results.json": ("scripts/tools/diff_real_roots.py",),
    "corpora/real_roots/manifest.json": ("scripts/tools/diff_real_roots.py",),
    "corpora/real_roots/results_sample2.json": ("scripts/tools/diff_real_roots.py",),
    "corpora/real_roots/results_sample3.json": ("scripts/tools/diff_real_roots.py",),
    "corpora/real_roots/manifest_sample3.json": ("scripts/tools/diff_real_roots.py",),
    # OPEN-128 (8): the 13 producers that were GRADING_CODE_PENDING.
    "corpora/apply_fixes_real/results.json":
        ("scripts/tools/gen_apply_fixes_real_differential.py",),
    "corpora/apply_fixes_real/results_virgin.json":
        ("scripts/tools/gen_apply_fixes_real_differential.py",),
    "corpora/apply_fixes_real/results_fresh.json":
        ("scripts/tools/gen_apply_fixes_real_differential.py",),
    "corpora/strict_battery/manifest.json": ("scripts/tools/gen_strict_battery.py",),
    "corpora/false_ready/manifest.json":
        ("scripts/tools/false_ready_oracle.sh", "scripts/tools/_oracle.sh"),
    "corpora/apply_fixes/manifest.json":
        ("scripts/tools/check_apply_fixes_roundtrip.py",),
    "corpora/contracts/strict/article-s0-signatures.json":
        ("scripts/tools/gen_strict_signatures.py", "scripts/tools/gen_contract.py"),
    "corpora/strict_s0/rule_probes.json":
        ("scripts/tools/strict_differential.py", "scripts/tools/_strict_s0.py"),
    "corpora/strict_s0/differential_v2.json":
        ("scripts/tools/strict_differential.py", "scripts/tools/_strict_s0.py"),
    "corpora/strict_s0/bytes_probes.json":
        ("scripts/tools/strict_differential.py", "scripts/tools/_strict_s0.py"),
    "corpora/strict_s0/bytes_differential.json":
        ("scripts/tools/strict_differential.py", "scripts/tools/_strict_s0.py"),
    "corpora/contracts/strict/article-s0-lexical.json":
        ("scripts/tools/gen_strict_lexical.py", "scripts/tools/gen_contract.py"),
    "corpora/oracle_baseline/clock_census.json":
        ("scripts/tools/oracle_clock_census.py",),
    "corpora/oracle_baseline/platform_residuals.json":
        ("scripts/tools/check_oracle_platforms.py",),
}

# EVERY TRACKED DATA FILE IS CLASSIFIED (C-128; data files, not only JSON,
# since C-129: see is_data_file). A file is a GRADED artefact,
# matches an ORACLE_RECORDS row, is PRE_BASELINE, or is listed here as
# recording NO oracle block, with the reason; an unclassified file fails, and
# so does a file in two classes. Under corpora/ each file is named exactly
# (a new artefact there must be classified before it lands); elsewhere a row
# may name a directory (`**` crosses `/`). In a NO_ORACLE file the discovery
# must find nothing outside NOT_A_BLOCK.
NO_ORACLE = (
    ("corpora/apply_fixes_real/fix_meaning_review.json",
     "OPEN-112: a human review of the meaning audit; it grades nothing"),
    ("corpora/contracts/parser_fixtures/kernel_meanings_excerpt.json",
     "a parser fixture for check_gen_contract_parsers.py"),
    ("corpora/contracts/parser_fixtures/review_missing_names.json",
     "a parser fixture for check_gen_contract_parsers.py"),
    ("corpora/oracle_baseline/cli_verify_fe673dc1.json",
     "OPEN-126/C-120: a CLI re-verification; it runs no TeX engine"),
    ("corpora/oracle_baseline/diff_strict_battery.json",
     "OPEN-118: its before/after oracles are recorded as banner STRINGS "
     "(the before side a host TeX Live); it is a cell diff, checked by "
     "_results_summary, and the battery it diffs is GRADED"),
    ("corpora/perf/keystroke_budget.json", "a timing record; no TeX engine"),
    ("corpora/real_roots/proven_coverage_sample1.json",
     "CLI certificates joined to results.json's rows; no TeX engine"),
    ("corpora/real_roots/proven_coverage_sample2.json",
     "CLI certificates joined to results_sample2.json's rows; no TeX engine"),
    ("corpora/real_roots/proven_coverage_sample3.json",
     "CLI certificates joined to results_sample3.json's rows; no TeX engine"),
    ("corpora/real_roots/strict_boundary_sample2.json",
     "strict-tier boundary of sample 2 (CLI only); no TeX engine"),
    ("corpora/real_roots/strict_boundary_sample3.json",
     "strict-tier boundary of sample 3 (CLI only); no TeX engine"),
    (".github/*.json", "CI configuration"),
    # Non-JSON data files (C-129): configuration and specifications.
    (".github/actions/**", "CI composite actions"),
    (".github/workflows/*", "CI workflows (their engine starts are "
     "checked by the engine-start scan below)"),
    (".pre-commit-config.yaml", "pre-commit configuration"),
    ("docs/SUPPORT_MATRIX.yaml", "the support matrix"),
    ("governance/**", "governance facts"),
    ("mkdocs.yml", "documentation site configuration"),
    ("core/**", "engine source data (catalogues, baselines)"),
    ("data/**", "ML data"),
    ("generated/**", "generated project facts"),
    ("generator/**", "rule-generator batches"),
    ("infra/**", "dashboards"),
    ("keystroke_budget_measured.json", "a timing record; no TeX engine"),
    ("latex-parse/data/**", "engine source data (catalogues)"),
    ("ml/**", "ML evaluation results"),
    ("proofs/**", "proof-side data"),
    ("scripts/sandbox/**", "sandbox configuration"),
    ("scripts/tools/fixtures/**", "gate fixtures"),
    ("specs/**", "specifications"),
)

# Dicts the (broad) discovery finds that are NOT oracle blocks, each pinned
# to its exact key set: a per-package revision pair whose `image` is a TeX
# Live revision number, not an image.
NOT_A_BLOCK = {
    ("corpora/oracle_baseline/summary.json",
     ("tree_comparison", "host_newer_revision", "[]")):
        frozenset({"package", "host", "image"}),
    ("corpora/oracle_baseline/diff_real_roots_sample2.json",
     ("rows", "[]", "packages_with_revision_drift", "[]")):
        frozenset({"package", "host", "image"}),
}
# Oracle-shaped blocks that are NOT a grade, each with its reason. Pinned to
# its exact contents; an entry must declare itself (no image, a backend
# outside BACKENDS), so a real grade cannot be filed here to escape the
# architecture rule.
NOT_THE_ORACLE = {
    ("corpora/oracle_baseline/diff_real_roots_sample2.json",
     ("classification_inputs", "host_diagnostic")):
        "OPEN-118 (i): the host TeX Live's own fingerprint, recorded to "
        "CLASSIFY the one moved row; it grades nothing",
}
NOT_THE_ORACLE_SIZE = 1

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

# GRADED artefacts that do not yet name their GRADING CODE (OPEN-126). EMPTY
# since OPEN-128 (8): every producer records `grading_code`, and every GRADED
# artefact was re-graded under it. Pinned empty: an entry needs a ledger row.
GRADING_CODE_PENDING: dict = {}
GRADING_CODE_PENDING_SIZE = 0

# The CI job that grades must run on the architecture of record (ADR-015 E2,
# E9): GitHub's native arm64 runner.
TEX_ORACLE_WORKFLOW = ".github/workflows/tex-oracle.yml"
ARCH_RUNNERS = {"aarch64": ("ubuntu-24.04-arm", "ubuntu-22.04-arm")}
# ONE LAUNCH DEFINITION (ADR-015 E15, owner 2026-10-06; OPEN-128 (4)). The
# graders reach the engine only through _oracle.py, which starts every
# container itself (ContainerOracle.launch_argv). A workflow step that starts
# a container of the TeX image -- `docker run`/`exec`/`create`/`start` (or
# `docker container ...`) naming it, a job `container:` or a `services:`
# image naming it -- is a second launch definition and FAILS this gate; so
# does any `docker run/exec/create/start` at all in tex-oracle.yml (only
# `docker pull` remains there), and any mention of LP_ORACLE_IN_IMAGE (the
# retired native backend's selector) in a workflow. Until OPEN-128 this gate
# instead compared the in-image `docker run` lines' flags with the
# container's (INIMAGE_RUN_FLAGS, the tmpfs options): two definitions kept in
# step by hand (C-127, re-audit premise 21).
_DOCKER_START = re.compile(
    r"\bdocker\s+(?:container\s+)?(?:run|exec|create|start)\b")
_TEX_IMAGE_REF = re.compile(r"\$\{?\{?\s*(?:env\.)?TEX_IMAGE\b|texlive/texlive|TEX_IMAGE")


def workflow_launch_findings(repo: Path) -> list[str]:
    """See the block above: no workflow starts the TeX image itself."""
    out = []
    for rel in sorted(tracked_files(repo)):
        if not rel.startswith(".github/") or not rel.lower().endswith((".yml", ".yaml")):
            continue
        p = repo / rel
        if not p.is_file():
            continue
        lines = p.read_text(errors="replace").split("\n")
        # a command continued with a trailing backslash is one command
        joined, cur, start = [], "", 0
        for n, ln in enumerate(lines, 1):
            code = "" if ln.lstrip().startswith("#") else ln
            if not cur:
                start = n
            cur += code.rstrip("\\") + " " if code.rstrip().endswith("\\") else code
            if not code.rstrip().endswith("\\"):
                joined.append((start, cur))
                cur = ""
        for n, code in joined:
            if not code.strip():
                continue
            if "LP_ORACLE_IN_IMAGE" in code:
                out.append(f"{rel}:{n}: names LP_ORACLE_IN_IMAGE, the selector of "
                           f"the retired native backend (ADR-015 E15)")
            starts = _DOCKER_START.search(code)
            if starts and (rel == TEX_ORACLE_WORKFLOW or _TEX_IMAGE_REF.search(code)):
                out.append(f"{rel}:{n}: starts a container itself "
                           f"({code.strip()[:80]!r}); a grade's container is "
                           f"started only by _oracle.py's launch definition "
                           f"(ContainerOracle.launch_argv, ADR-015 E15)")
            if re.match(r"^\s*(container|image):\s*\S", code) and _TEX_IMAGE_REF.search(code):
                out.append(f"{rel}:{n}: a job container/service of the TeX image "
                           f"({code.strip()[:80]!r}); grading inside the image is "
                           f"retired (ADR-015 E15)")
    return out


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
# A pipeline stage that RUNS its standard input as code or as arguments, BY
# METHOD (C-91 review round 5): the stage's argv[0] after stripping wrapper
# commands (`timeout 60`, `nice -n 5`, `env A=b`, `stdbuf -oL`, `sudo`, ...,
# with their options and operands) is a RUNNER -- a shell or interpreter, a
# command that runs its input lines (`xargs`, `parallel`), a loop that reads
# them (`while read c; do $c; done`), or awk (`system($0)`). The round-5
# review MEASURED `| timeout 60 sh`, `| nice -n 5 sh`, `| parallel`, `| while
# read` and `| awk '{system($0)}'` scanning clean against the old prefix regex.
SH_RUNNERS = frozenset(("sh", "bash", "dash", "zsh", "ksh", "mksh", "busybox",
                        "eval", "source", ".", "xargs", "parallel", "python",
                        "python3", "perl", "ruby", "tclsh", "node", "php", "lua",
                        "texlua", "awk", "gawk", "mawk", "nawk", "busybox",
                        "while", "until", "fish", "csh", "tcsh", "rc", "expect"))
SH_WRAPPERS = frozenset(("sudo", "doas", "env", "timeout", "gtimeout", "nice",
                         "ionice", "nohup", "stdbuf", "setsid", "time", "command",
                         "exec", "builtin", "chrt", "taskset", "unbuffer",
                         "xvfb-run", "flock", "chroot", "systemd-run", "caffeinate",
                         "script", "watch", "then", "do", "else", "!", "{", "("))
ML_SPAWN = re.compile(r"Sys\.command|create_process|open_process|Unix\.exec|"
                      r"Unix\.system|Unix\.fork|Lwt_process|Bos\.(OS|Cmd)|"
                      r"Feather\.|Shexp_process")
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
# Workflow lines that run an engine INSIDE the pinned image. EMPTY since
# OPEN-128 (ADR-015 E15): the canary and the pin assertion go through the
# oracle (oracle_canary.py, `_oracle.py version`), and no step starts the
# image (workflow_launch_findings). Exact stripped lines; a new one fails.
WORKFLOW_ALLOW: dict = {}
FINGERPRINT_KEYS = ("tlpdb_sha256", "macro_layer_sha256", "fmt_sha256")
# The backend a recorded block may name: "container" (the only one since
# OPEN-128); "native" remains a known value of historical records.
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
# runs them in the pinned image. The measurement entry point (ADR-015 E7,
# OPEN-128 (2)) is the same: `measure(dir, "pdftex", ["-ini"], ...)` names the
# engine the ORACLE starts. RESIDUAL: a function of one's own named
# `run_engine` or `measure` that spawns what it is given is exempt too.
ORACLE_CALLS = {"run_engine", "measure"}
# The shell form of the measurement entry point: `python3 .../_oracle.py
# measure [OPTIONS] -- pdftex -ini` names the engine the oracle starts
# (one command; a `;`/`&&`/`|` starts another, which is scanned).
ORACLE_MEASURE_CMD = re.compile(
    r"^\s*(?:\S*/)?python3?\s+(?:\S*/)?_oracle\.py\s+measure(\s|$)")


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
_STR_DUNDERS = {"__add__", "__radd__", "__mul__", "__rmul__", "__mod__",
                "__getitem__", "__format__"}
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
    # Round 5 (C-91): a dict of literals (for `%(a)s` formatting, and its KEYS
    # when it is unpacked: `[*{'-progname=pdflatex': 1}]`), a walrus, a
    # starred operand, and a class attribute bound once (`C.P`).
    if isinstance(node, ast.Dict):
        if any(k is None for k in node.keys):
            raise _NoFold
        return {f(k): f(v) for k, v in zip(node.keys, node.values)}
    if isinstance(node, ast.NamedExpr):
        return f(node.value)
    if isinstance(node, ast.Starred):
        v = f(node.value)
        if not isinstance(v, (str, bytes, tuple, dict)):
            raise _NoFold
        return tuple(v)
    if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name):
        key = f"{node.value.id}.{node.attr}"
        if key in names:
            return f(names[key])
        raise _NoFold
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
        fname = fn.attr if isinstance(fn, ast.Attribute) else getattr(fn, "id", None)
        # map(chr|str, LITERALS) and functools.reduce(operator.add, LITERALS)
        if fname == "map" and len(node.args) == 2 and isinstance(node.args[0], ast.Name) \
                and node.args[0].id in ("chr", "str"):
            seq = f(node.args[1])
            if not isinstance(seq, tuple) or len(seq) > _FOLD_MAX:
                raise _NoFold
            try:
                return tuple((chr if node.args[0].id == "chr" else str)(x) for x in seq)
            except (TypeError, ValueError, OverflowError):
                raise _NoFold
        if fname == "reduce" and len(node.args) in (2, 3) and (
                getattr(node.args[0], "attr", None) in ("add", "concat", "iadd")
                or getattr(node.args[0], "id", None) in ("add", "concat")):
            seq = f(node.args[1])
            if not isinstance(seq, tuple) or not seq:
                raise _NoFold
            acc = f(node.args[2]) if len(node.args) == 3 else seq[0]
            for x in (seq if len(node.args) == 3 else seq[1:]):
                if type(x) is not type(acc) or not isinstance(x, (str, bytes)):
                    raise _NoFold
                acc = acc + x
            return acc
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
            if (isinstance(fn.value, ast.Name) and fn.value.id in ("str", "bytes")
                    and (fn.attr in _STR_METHODS or fn.attr in _STR_DUNDERS) and args):
                # the unbound form: str.__add__('pdfl', 'atex'), str.join(...)
                try:
                    r = getattr({"str": str, "bytes": bytes}[fn.value.id], fn.attr)(*args)
                except (TypeError, ValueError, AttributeError, UnicodeError):
                    raise _NoFold
                if r is NotImplemented:
                    raise _NoFold
                return tuple(r) if isinstance(r, list) else r
            if fn.attr in _STR_METHODS or fn.attr in _STR_DUNDERS:
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
        elif isinstance(n, ast.Attribute) and isinstance(n.ctx, (ast.Store, ast.Del)) \
                and isinstance(n.value, ast.Name):
            k = f"{n.value.id}.{n.attr}"
            count[k] = count.get(k, 0) + 1
        if isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name):
            value[n.targets[0].id] = n.value
        elif isinstance(n, ast.AnnAssign) and isinstance(n.target, ast.Name) and n.value is not None:
            value[n.target.id] = n.value
        elif (isinstance(n, ast.Assign) and len(n.targets) == 1
              and isinstance(n.targets[0], (ast.Tuple, ast.List))
              and isinstance(n.value, (ast.Tuple, ast.List))
              and len(n.targets[0].elts) == len(n.value.elts)):
            # `a, b = 'pdfl', 'atex'` (MEASURED clean in round 5)
            for t, v in zip(n.targets[0].elts, n.value.elts):
                if isinstance(t, ast.Name):
                    value[t.id] = v
        if isinstance(n, ast.ClassDef):
            # `class C: P = 'pdfl'` binds C.P (MEASURED clean in round 5)
            for st in n.body:
                if isinstance(st, ast.Assign) and len(st.targets) == 1 \
                        and isinstance(st.targets[0], ast.Name):
                    k = f"{n.name}.{st.targets[0].id}"
                    value[k] = st.value
                    count[k] = count.get(k, 0) + 1
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


_SH_HEREDOC = re.compile(r"<<-?\s*(['\"]?)([A-Za-z_][A-Za-z0-9_]*)\1")


def _sh_heredoc_python(text: str) -> list[tuple[int, str]]:
    """A here-document fed to a Python interpreter (`python3 - <<'EOF'`) is
    Python: its body is scanned as Python (MEASURED clean in round 5). A
    here-document fed to a shell is already scanned line by line as shell."""
    hits, lines, i = [], text.split("\n"), 0
    while i < len(lines):
        m = _SH_HEREDOC.search(lines[i].split("#", 1)[0])
        if m and re.fullmatch(r"python[0-9.]*", _sh_argv0(lines[i][:m.start()]) or ""):
            end = next((j for j in range(i + 1, len(lines))
                        if lines[j].strip() == m.group(2)), len(lines))
            body = "\n".join(ln.lstrip("\t") for ln in lines[i + 1:end])
            hits += [(i + 1 + n, v) for n, v in scan_python(body)]
            i = end + 1
            continue
        i += 1
    return hits


def _sh_argv0(seg: str) -> str | None:
    """The command a shell segment runs: its first word after variable
    assignments and wrapper commands (SH_WRAPPERS) with their options and
    operands (`-n 5`, `60`, `-oL`, `A=b`), path stripped."""
    words = SH_WORD.findall(seg)
    i, wrapped = 0, False
    while i < len(words):
        w = words[i].strip("\"'")
        base = w.rsplit("/", 1)[-1]
        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*\+?=.*", w):
            i += 1                         # an assignment prefix
        elif base in SH_WRAPPERS:
            i += 1
            wrapped = True
        elif wrapped and (w.startswith("-") or re.fullmatch(r"[0-9.]+[smhd]?", w)):
            i += 1                         # a wrapper's option or operand
        else:
            return base
    return None


def _sh_runs_input(seg: str) -> bool:
    return _sh_argv0(seg) in SH_RUNNERS


def _sh_substitutions(code: str) -> list[str]:
    """The commands inside `$(...)` and backquotes, outside single quotes (a
    double-quoted message still runs them: `echo "log: $(pdflatex t)"`, MEASURED
    scanning clean by the round-5 review). Nested ones are found by the
    caller scanning each result again."""
    out, i, n, sq = [], 0, len(code), False
    while i < n:
        c = code[i]
        if c == "\\" and not sq:
            i += 2
            continue
        if c == "'" and not sq and (i == 0 or code[i - 1] != "$"):
            # a single-quoted span (only outside double quotes, approximated)
            j = code.find("'", i + 1)
            if j == -1:
                break
            i = j + 1
            continue
        if code.startswith("$(", i) and not code.startswith("$((", i):
            depth, j = 1, i + 2
            while j < n and depth:
                depth += (code[j] == "(") - (code[j] == ")")
                j += 1
            out.append(code[i + 2:j - 1])
            i = j
            continue
        if c == "`":
            j = code.find("`", i + 1)
            if j == -1:
                break
            out.append(code[i + 1:j])
            i = j + 1
            continue
        i += 1
    return out


def scan_shell(text: str, allow: tuple = (), make: bool = False,
               yaml: bool = False) -> list[tuple[int, str]]:
    """A shell line starts an engine when the engine is a bare word OUTSIDE
    quotes (`pdflatex x.tex`, `PDF=pdflatex`, `cmd=(pdflatex -x)`), or when a
    quoted word IS an engine or an engine command line (`PDF="pdflatex"`,
    `sh -c 'pdflatex x.tex'`). An engine named inside a longer quoted string
    is a message or a pattern (`echo "... pdflatex failed"`, `grep 'pdftex\\|
    pdflatex'`), and `x['pdflatex']` is a subscript."""
    hits = _sh_heredoc_python(text)
    sh_vars = _sh_var_values(text)
    make_vars = _make_var_values(text) if make else {}
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
        runs_stdin = any(_sh_runs_input(sg) for sg in segs[1:])
        if make:
            code = _make_eval(code, make_vars)
            segs = _sh_commands(code)
        # A command substitution runs, wherever it stands (C-91 round 5).
        todo, subs = [code], []
        while todo and len(subs) < 64:
            for inner in _sh_substitutions(todo.pop()):
                subs.append(inner)
                todo.append(inner)
        segs = segs + [c for inner in subs for c in _sh_commands(inner)]
        for seg in segs:
            seg = SH_CASE_LABEL.sub(" ", seg, count=1)
            if ORACLE_MEASURE_CMD.match(seg):
                continue                       # the oracle's own measurement
            seg = SH_JQ_ARG.sub(" ", seg) if re.search(r"(^|[\s(`])jq\s", seg) else seg
            # A message stops being one when the pipeline runs it, when it
            # holds a command substitution, or when it is written to a FILE
            # (`echo 'pdflatex t' > run.sh; sh run.sh`, MEASURED clean in
            # round 5): a message goes to a terminal, a log stream or /dev/null.
            if (SH_MESSAGE.match(seg) and not runs_stdin
                    and "$(" not in seg and "`" not in seg
                    and not SH_REDIRECT_FILE.search(SH_QUOTED.sub('""', seg))):
                continue                       # this ONE command is a message
            if _sh_var_engine(seg, sh_vars):
                hit = True
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
# `${!n:-pdftex}` (indirect) and `${1:-pdftex}` (a positional or special
# parameter) too: MEASURED clean in round 5.
SH_PARAM_WORD = re.compile(r"\$\{[!#]?(?:[A-Za-z_][A-Za-z0-9_]*|[0-9]+|[@*#?$!-])"
                           r"(?:\[[^\]]*\])?:?[-=+?]([^{}]*)\}")
# `>`/`>>`/`&>` to a FILE (not a descriptor, /dev/null, /dev/std*, or the
# CI's own step-summary/output streams).
SH_REDIRECT_FILE = re.compile(
    r"(?<![0-9&<])(&?>>?|[0-9]>>?)\s*(?!&|/dev/(null|stderr|stdout|tty)\b|"
    r"\S*GITHUB_(STEP_SUMMARY|OUTPUT|ENV)\b)[^\s;|&]")


# SHELL VARIABLES WITH LITERAL VALUES (C-91 review round 5). The `${P}latex`
# rule caught a variable followed by the tail of an engine name; the round-5
# review MEASURED `${P}${Q}`, `${P}atex`, `${E,,}`, `${E/X/}`, `E+=...; $E`
# and `${E:1}` scanning clean. So every variable assigned a LITERAL value in
# the file (`NAME=word`, `NAME+=word`, with export/local/readonly/declare) is
# tracked with all its values, and a word that expands those variables
# (plain, case-modified, pattern-substituted, prefix/suffix-removed, sliced) is
# expanded and matched like a literal. RESIDUAL: a value that is not a literal
# (read from input, a command substitution, another variable's expansion at
# assignment time), an array element, and `eval`.
_SH_ASSIGN = re.compile(r"(?:^|[\s;&|(])(?:(?:export|local|readonly|declare"
                        r"(?:\s+-[A-Za-z]+)*)\s+)?([A-Za-z_][A-Za-z0-9_]*)(\+?)="
                        r"((?:\$'(?:[^'\\]|\\.)*'|\"(?:[^\"\\$`]|\\.)*\"|'[^']*'|"
                        r"[^\s;&|()<>$`\"'])*)(?=$|[\s;&|)])")
_SH_EXP = re.compile(r"\$\{([A-Za-z_][A-Za-z0-9_]*)([^{}]*)\}|\$([A-Za-z_][A-Za-z0-9_]*)")
_SH_VAR_MAX = 64


def _sh_dequote(w: str) -> str | None:
    import shlex
    dec = _ANSI_C.sub(lambda m: shlex.quote(_ansi_c_decode(m.group(1))), w)
    try:
        return "".join(shlex.split(dec, posix=True)) if dec else ""
    except ValueError:
        return None


def _sh_var_values(text: str) -> dict:
    vals: dict = {}
    for line in text.split("\n"):
        code = line.split("#", 1)[0] if not line.lstrip().startswith("#") else ""
        for m in _SH_ASSIGN.finditer(code):
            name, plus, raw = m.group(1), m.group(2), m.group(3)
            v = _sh_dequote(raw)
            if v is None:
                continue
            if plus:
                cur = vals.get(name) or [""]
                vals[name] = [c + v for c in cur][:_SH_VAR_MAX]
            else:
                vals.setdefault(name, [])
                if v not in vals[name] and len(vals[name]) < _SH_VAR_MAX:
                    vals[name].append(v)
    return vals


def _sh_apply_op(v: str, op: str) -> str | None:
    """bash's value of `${NAME<op>}` for a literal op; None when unmodelled."""
    import fnmatch
    if op == "":
        return v
    if op in (",,", "^^", ",", "^"):
        if op == ",,":
            return v.lower()
        if op == "^^":
            return v.upper()
        return (v[:1].lower() if op == "," else v[:1].upper()) + v[1:]
    m = re.fullmatch(r"(//?)([^/]*)(?:/(.*))?", op)
    if m:
        pat, rep_ = m.group(2), m.group(3) or ""
        if any(c in pat for c in "*?["):
            return None
        return v.replace(pat, rep_) if m.group(1) == "//" else v.replace(pat, rep_, 1)
    m = re.fullmatch(r":\s*(-?\d+)(?::\s*(-?\d+))?", op)
    if m:
        off = int(m.group(1))
        s = v[off:] if off >= 0 else v[len(v) + off:]
        if m.group(2) is not None:
            ln = int(m.group(2))
            s = s[:ln] if ln >= 0 else s[:len(s) + ln]
        return s
    m = re.fullmatch(r"(##?|%%?)(.*)", op)
    if m:
        kind, pat = m.group(1), m.group(2)
        if kind[0] == "#":
            cands = [i for i in range(len(v) + 1) if fnmatch.fnmatchcase(v[:i], pat)]
            return v[(max(cands) if kind == "##" else min(cands)):] if cands else v
        cands = [i for i in range(len(v) + 1) if fnmatch.fnmatchcase(v[i:], pat)]
        return v[:(min(cands) if kind == "%%" else max(cands))] if cands else v
    return None


def _sh_var_engine(seg: str, vals: dict) -> bool:
    """A word of `seg` that, with the file's literal variable values
    substituted, IS an engine name or a format selector."""
    if not vals:
        return False
    for raw in SH_WORD.findall(seg):
        if "$" not in raw or not any(
                (m.group(1) or m.group(3)) in vals for m in _SH_EXP.finditer(raw)):
            continue
        outs = [raw]
        for _ in range(4):
            nxt = []
            for w in outs:
                m = _SH_EXP.search(w)
                if m is None or (m.group(1) or m.group(3)) not in vals:
                    nxt.append(w)
                    continue
                for v in vals[m.group(1) or m.group(3)]:
                    r = _sh_apply_op(v, m.group(2) or "")
                    if r is not None:
                        nxt.append(w[:m.start()] + r + w[m.end():])
            outs = nxt[:_SH_VAR_MAX]
        for w in outs:
            d = _sh_dequote(w)
            if d is not None and (ENGINE_LITERAL.match(d) or FMT_SELECTOR.match(d)):
                return True
    return False
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
                      r"basename|suffix|if)[ \t]([^$(){}]*)[)}]")


# MAKE VARIABLES WITH LITERAL VALUES (C-91 review round 5): `P = pdfl` then
# `$(P)$(Q)`, `$(P)atex`, `E += atex` were MEASURED scanning clean. Every
# variable assigned at the top level of the makefile (`=`, `:=`, `::=`, `?=`,
# `+=`, `override`/`export` prefixes) is expanded in recipe lines, recursively
# (a value may reference another variable); an undefined variable expands to
# nothing, as in make. `$(if COND,THEN,ELSE)` over literal arguments is
# evaluated. RESIDUAL: target-specific and command-line variables, `define`
# blocks, `$(shell ...)`/`$(call ...)`/`$(eval ...)`/`$(foreach ...)`.
_MAKE_ASSIGN = re.compile(r"^(?:(?:override|export)\s+)*([A-Za-z_][A-Za-z0-9_.-]*)\s*"
                          r"(\+=|::?=|\?=|=)\s*(.*)$")
_MAKE_REF = re.compile(r"\$[({]([A-Za-z_][A-Za-z0-9_.-]*)[)}]|\$([A-Za-z_])")


def _make_var_values(text: str) -> dict:
    vals: dict = {}
    for line in text.split("\n"):
        if line.startswith("\t"):
            continue                       # a recipe line
        code = line.split("#", 1)[0].rstrip()
        m = _MAKE_ASSIGN.match(code)
        if not m:
            continue
        name, op, v = m.group(1), m.group(2), m.group(3).strip()
        vals[name] = (vals[name] + " " + v).strip() if op == "+=" and name in vals else v
    return vals


def _make_expand(code: str, vals: dict) -> str:
    for _ in range(8):
        new = _MAKE_REF.sub(
            lambda m: vals.get(m.group(1) or m.group(2), "")
            if (m.group(1) or m.group(2)) not in _MAKE_FN_NAMES else m.group(0), code)
        if new == code:
            break
        code = new
    return code


_MAKE_FN_NAMES = frozenset(("subst", "patsubst", "strip", "addprefix", "addsuffix",
                            "join", "firstword", "lastword", "word", "findstring",
                            "filter", "sort", "notdir", "basename", "suffix", "if",
                            "shell", "call", "eval", "foreach", "wildcard", "info",
                            "warning", "error", "value", "origin", "or", "and"))


def _make_eval(code: str, vals: dict | None = None) -> str:
    if vals is not None:
        code = _make_expand(code, vals)

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
            if fn == "if" and len(parts) in (2, 3):
                return parts[1] if parts[0].strip() else (parts[2] if len(parts) == 3 else "")
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
    """Every tracked path, VERBATIM. `-z` (C-129): without it git C-quotes a
    path holding a non-ASCII byte (`"corpora/r\\303\\251sultats.json"`), and
    a quoted name neither ends in `.json` nor names a real file, so it escaped
    the classification, the discovery and the engine-start scan alike."""
    import subprocess
    r = subprocess.run(["git", "-C", str(repo), "ls-files", "-z"],
                       capture_output=True, encoding="utf-8",
                       errors="surrogateescape")
    if r.returncode != 0:
        raise RuntimeError(f"git ls-files failed: {r.stderr.strip()}")
    return [f for f in r.stdout.split("\0") if f]


#: THE DATA FILES (C-129). A tracked file is a data file when its name,
#: LOWERCASED, ends in one of these. Every data file must be classified
#: (GRADED, ORACLE_RECORDS, PRE_BASELINE or NO_ORACLE); an unclassified one
#: fails. The JSON family is parsed (`.json.gz` decompressed) and searched for
#: oracle blocks. The others are not an oracle-record format (every producer
#: writes JSON through _oracle.py), so they may only be NO_ORACLE, and a text
#: that names a tree-fingerprint key fails. The match was case-sensitive and
#: JSON-only until review round 4: `results.JSON` escaped everything.
JSON_DATA_EXT = (".json", ".jsonl", ".json.gz")
OTHER_DATA_EXT = (".yaml", ".yml", ".csv", ".tsv")


def is_data_file(rel: str) -> bool:
    return rel.lower().endswith(JSON_DATA_EXT + OTHER_DATA_EXT)


def is_json_data(rel: str) -> bool:
    return rel.lower().endswith(JSON_DATA_EXT)


def dig(d, path):
    for k in path:
        if not isinstance(d, dict):
            return None
        d = d.get(k)
    return d


#: A dict holding ANY of these keys is discovered as a possible oracle block.
#: Broad on purpose (C-128, review round 3): the discovery used to need a
#: fingerprint, an `arch` or an image named by DIGEST, so a block naming its
#: image by tag (`texlive/texlive:latest`) and its architecture under another
#: key was not found. The known non-oracle hits are pinned in NOT_A_BLOCK or
#: sit in a PRE_BASELINE file. MEASURED 2026-10-06 over every tracked JSON
#: file: 149 hits; 39 at GRADED and ORACLE_RECORDS locations, 1 in
#: NOT_THE_ORACLE, 94 in NOT_A_BLOCK, 15 host provenance blocks in
#: PRE_BASELINE files, 0 elsewhere.
IDENTITY_KEYS = frozenset(FINGERPRINT_KEYS) | {
    "arch", "image", "engine", "engine_banner", "backend", "clock", "machine"}


def is_oracle_block(d) -> bool:
    """A dict that may record an oracle identity (any IDENTITY_KEYS key).
    This is the SECOND net: what is checked is decided by location
    (GRADED, ORACLE_RECORDS), and this finds a block at any other path."""
    return isinstance(d, dict) and not IDENTITY_KEYS.isdisjoint(d)


def oracle_blocks(doc, path=()):
    """Every (key path, block) in a parsed JSON document, list indices as
    "[]". A block's own fields are not searched further."""
    if is_oracle_block(doc):
        yield path, doc
        return
    if isinstance(doc, dict):
        for k, v in doc.items():
            yield from oracle_blocks(v, path + (k,))
    elif isinstance(doc, list):
        for v in doc:
            yield from oracle_blocks(v, path + ("[]",))


def _seg_glob(pattern: str, rel: str) -> bool:
    """`*` matches within one path segment (fnmatch's `*` crosses `/`);
    `**` matches across segments."""
    rx = "".join(".*" if t == "**" else "[^/]*" if t == "*" else re.escape(t)
                 for t in re.findall(r"\*\*|\*|[^*]+", pattern))
    return re.fullmatch(rx, rel) is not None


def identity_findings(rel: str, path: tuple, block: dict, image: str,
                      version: str, record: str, fps: dict) -> list[str]:
    """The rule every recorded oracle block obeys, GRADED or not (C-127): it
    names the pinned image and the architecture of record, and every tree
    fingerprint it records is that architecture's. A recorded version or
    engine banner names the pin; a recorded backend and clock are known
    ones."""
    where = f"{rel} [{'.'.join(path) or '<root>'}]"
    out = []
    if block.get("image") != image:
        out.append(f"{where}: graded by "
                   f"{block.get('image') or 'a host TeX Live (no image recorded)'}"
                   f", not the pinned image {image}. Re-grade it through "
                   f"scripts/tools/_oracle.py (ADR-012 decision 7).")
    if block.get("arch") != record:
        out.append(f"{where}: graded on {block.get('arch')!r}, not the "
                   f"oracle's architecture of record {record!r}. Grades are not "
                   f"compared across architectures (ADR-015 E2, C-103); "
                   f"re-grade it on {record}.")
    if "fmt_sha256" not in block:
        out.append(f"{where}: records no fmt_sha256 (the per-architecture "
                   f"format), so its tree cannot be shown to be the oracle's")
    want = fps.get(record, {})
    for k in FINGERPRINT_KEYS:
        if k in block and block[k] != want.get(k):
            out.append(f"{where}: {k} {block[k]!r} is not the pinned image's "
                       f"{record} tree fingerprint {want.get(k)!r}")
    for k in ("version", "engine_banner"):
        if k in block and version not in str(block[k]):
            out.append(f"{where}: {k} {block[k]!r} is not the pin {version!r}")
    if "backend" in block and block["backend"] not in BACKENDS:
        out.append(f"{where}: backend {block['backend']!r} is not one of "
                   f"{sorted(BACKENDS)}")
    if "clock" in block and not _oracle.is_clock(block["clock"]):
        out.append(f"{where}: clock {block['clock']!r} is neither a fixed clock "
                   f"('{_oracle.CLOCK_PREFIX}<epoch>') nor a legacy value "
                   f"{list(_oracle.LEGACY_CLOCKS)}")
    # A MEASUREMENT is never a grade or a record of one (ADR-015 E7).
    if block.get("entry") == "measure" or block.get("measurement_only"):
        out.append(f"{where}: a measurement block (entry {block.get('entry')!r}, "
                   f"measurement_only {block.get('measurement_only')!r}) at a "
                   f"grade's location; _oracle.measure never grades (ADR-015 E7)")
    return out


def tracked_json_blocks(repo: Path) -> tuple[list, list[str], dict]:
    """(rel, key path, block) for every oracle block in every tracked .json
    and .jsonl file, the findings for a tracked JSON file that cannot be
    parsed (an unparsed file could hide a block), and {rel: parsed doc}."""
    found, bad, docs = [], [], {}
    for rel in sorted(tracked_files(repo)):
        if not is_json_data(rel):
            continue
        p = repo / rel
        if not p.is_file():
            continue
        low = rel.lower()
        try:
            raw = p.read_bytes()
            if low.endswith(".gz"):
                raw = gzip.decompress(raw)
            text = raw.decode("utf-8")
            doc = ([json.loads(ln) for ln in text.split("\n") if ln.strip()]
                   if low.endswith(".jsonl") else json.loads(text))
        except (OSError, EOFError, gzip.BadGzipFile, UnicodeDecodeError,
                json.JSONDecodeError) as e:
            bad.append(f"{rel}: a tracked JSON file this gate cannot parse "
                       f"({e}); it could hide an oracle block")
            continue
        docs[rel] = doc
        found.extend((rel, path, block) for path, block in oracle_blocks(doc))
    return found, bad, docs


def grading_code_set_findings(where: str, block: dict, graders) -> list[str]:
    """`grading_code.files` must be EXACTLY the oracle core plus the
    producer's graders (C-128): a set check alone, the blob ids are checked
    by _oracle.grading_code_drift."""
    gc = block.get("grading_code")
    files = gc.get("files") if isinstance(gc, dict) else None
    if not isinstance(files, dict):
        return [f"{where}: records no grading_code, but its producer records "
                f"one naming {sorted(set(_oracle.GRADING_CODE_CORE) | set(graders))}"]
    want = set(_oracle.GRADING_CODE_CORE) | set(graders)
    if set(files) != want:
        return [f"{where}: grading_code names {sorted(files)}, not exactly the "
                f"oracle core and its grader {sorted(want)} (C-128): a grade "
                f"must name the grader that produced it"]
    return []


SHEBANG =re.compile(rb"^#!\s*(\S+)(?:\s+(\S+))?")
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


# TRACKED FILES THAT RUN COMMANDS BUT ARE NOT SCRIPTS (C-91 review round 5:
# each MEASURED scanning clean). Scanned: a composite action's `runs` steps
# (`action.yml` anywhere), `.pre-commit-config.yaml`/`.pre-commit-hooks.yaml`
# `entry:`, compose files and Kubernetes manifests (`command:`/`args:`) -- as
# YAML shell; a Dockerfile's RUN/CMD/ENTRYPOINT (`Dockerfile*`, `*.dockerfile`),
# a justfile, tox.ini, a Procfile and an .envrc -- as shell; package.json
# scripts and a latexmkrc (Perl) -- as quoted literals; a Jupyter notebook's
# code cells -- as Python, its `!`/`%%bash` lines as shell. NOT scanned,
# recorded: every other YAML/TOML/JSON/INI file is DATA in this repository
# (rule specs, governance facts, CI dashboards: they name engines as values,
# e.g. `compiler: pdflatex`), and the Rust/Cargo build is scanned as .rs.
def _command_file_kind(rel: str):
    name = rel.rsplit("/", 1)[-1]
    if name in ("action.yml", "action.yaml", ".pre-commit-config.yaml",
                ".pre-commit-hooks.yaml") or re.fullmatch(
                    r"(docker-)?compose[\w.-]*\.ya?ml", name) or (
                    rel.startswith(("infra/k8s/", ".github/")) and name.endswith((".yml", ".yaml"))):
        return lambda t: scan_shell(t, yaml=True)
    if (name.startswith("Dockerfile") or name.endswith(".dockerfile")
            or name in ("justfile", "Justfile", ".justfile", "tox.ini", "Procfile",
                        ".envrc")):
        return scan_shell
    if name in ("package.json",) or name.endswith("latexmkrc"):
        return scan_other
    if name.endswith(".ipynb"):
        return scan_notebook
    return None


def scan_notebook(text: str) -> list[tuple[int, str]]:
    """A notebook's code cells: `!cmd` lines and `%%bash`/`%%sh` cells as
    shell, the rest as Python (other `%` magics blanked). Line numbers are the
    cell's."""
    try:
        nb = json.loads(text)
    except ValueError:
        return scan_other(text)
    hits = []
    for cell in nb.get("cells", []) if isinstance(nb, dict) else []:
        if not isinstance(cell, dict) or cell.get("cell_type") != "code":
            continue
        src = cell.get("source", "")
        src = "".join(src) if isinstance(src, list) else str(src)
        lines = src.split("\n")
        if lines and re.match(r"^%%(bash|sh|script\s+(ba)?sh)\b", lines[0]):
            hits += scan_shell("\n".join(lines[1:]))
            continue
        py = []
        for ln in lines:
            m = re.match(r"^(\s*)!(.*)$", ln)
            if m:
                hits += [(0, w) for _, w in scan_shell(m.group(2))]
                py.append(m.group(1) + "pass")
            elif ln.lstrip().startswith("%"):
                py.append(ln[:len(ln) - len(ln.lstrip())] + "pass")
            else:
                py.append(ln)
        hits += scan_python("\n".join(py))
    return hits


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
    record = _oracle.ARCH_OF_RECORD
    if record not in fps or record not in ARCH_RUNNERS:
        findings.append(f"_oracle.ARCH_OF_RECORD = {record!r} has no recorded "
                        f"tree fingerprint or no CI runner in ARCH_RUNNERS")
    if set(fps) != {"aarch64", "x86_64"}:
        findings.append(f"_oracle.TREE_FINGERPRINTS covers {sorted(fps)}, "
                        f"expected both aarch64 (the architecture of record, "
                        f"local and CI) and x86_64 (measured, not an oracle: "
                        f"ADR-015 E2/E3)")
    elif fps["aarch64"]["macro_layer_sha256"] != fps["x86_64"]["macro_layer_sha256"]:
        findings.append("the arm64 and amd64 images of the pinned digest have "
                        "DIFFERENT macro layers: a local grade would not be the "
                        "CI grade")
    for arch, fp in fps.items():
        for k in FINGERPRINT_KEYS:
            if not re.fullmatch(r"[0-9a-f]{64}", str(fp.get(k, ""))):
                findings.append(f"_oracle.TREE_FINGERPRINTS[{arch}][{k}] is not a sha256")

    # 2./3. every graded artefact names the pinned image
    notes: list[str] = []
    graded_paths = {p for p, _ in GRADED}
    if len(GRADING_CODE_PENDING) != GRADING_CODE_PENDING_SIZE:
        findings.append(f"GRADING_CODE_PENDING holds {len(GRADING_CODE_PENDING)} "
                        f"entries, pinned at {GRADING_CODE_PENDING_SIZE}; "
                        f"changing it needs a ledger row and a deliberate edit")
    for rel in sorted(set(GRADING_CODE_PENDING) - graded_paths):
        findings.append(f"{rel} is in GRADING_CODE_PENDING but not in GRADED")
    for rel in sorted(set(GRADERS) - (graded_paths - set(GRADING_CODE_PENDING))):
        findings.append(f"{rel} is in GRADERS but is not a GRADED artefact "
                        f"outside GRADING_CODE_PENDING")
    # E2/E9 in CI: the grading job runs on the architecture of record; E15:
    # no workflow starts the TeX image itself.
    wf = repo / TEX_ORACLE_WORKFLOW
    wtext = wf.read_text() if wf.is_file() else ""
    runners = re.findall(r"^\s*runs-on:\s*(\S+)\s*$", wtext, re.M)
    if not runners or any(r not in ARCH_RUNNERS.get(record, ()) for r in runners):
        findings.append(f"{TEX_ORACLE_WORKFLOW}: runs-on {runners} is not a "
                        f"native {record} runner {ARCH_RUNNERS.get(record)}; "
                        f"CI would grade on another architecture (ADR-015 E2)")
    findings.extend(workflow_launch_findings(repo))
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
        if version not in str(block.get("version", "")):
            findings.append(f"{rel}: oracle version {block.get('version')!r} is not "
                            f"the pin {version!r}")
        if block.get("backend") not in BACKENDS:
            findings.append(f"{rel}: oracle backend {block.get('backend')!r} is not "
                            f"one of {sorted(BACKENDS)}")
        # The image, architecture and fingerprint rule is the one every
        # recorded oracle block obeys (identity_findings, C-127).
        findings.extend(identity_findings(rel, path, block, image, version,
                                          record, fps))
        # THE CLOCK (C-127; ADR-015 E10, OPEN-128 (3)). A published grade is
        # a PROTOCOL grade: its recorded clock is PROTOCOL_CLOCK, the fixed
        # clock; require_same_oracle compares it too. A block with no clock,
        # or with a legacy one ("real", "forced"), was graded before the
        # clock was fixed and fails until it is re-graded.
        clk = block.get("clock")
        if clk is None:
            findings.append(
                f"{rel}: records no clock; a published grade records the "
                f"protocol clock {_oracle.PROTOCOL_CLOCK!r} (OPEN-128). Re-grade it.")
        elif clk != _oracle.PROTOCOL_CLOCK:
            findings.append(f"{rel}: graded with clock {clk!r}, not the protocol "
                            f"clock {_oracle.PROTOCOL_CLOCK!r}; a published grade "
                            f"is a protocol grade (re-grade it)")
        if rel in GRADING_CODE_PENDING:
            if "grading_code" in block:
                findings.append(f"{rel} now records its grading_code but is "
                                f"still in GRADING_CODE_PENDING; remove it there")
        else:
            if rel not in GRADERS:
                findings.append(f"{rel}: records grading_code, but GRADERS "
                                f"does not name its grader (C-128)")
            findings.extend(grading_code_set_findings(
                rel, block, GRADERS.get(rel, ())))
            gc_find, gc_notes = _oracle.grading_code_drift(
                block.get("grading_code"), repo)
            findings.extend(
                f"{rel}: {f}. Re-grade it under the current code (for "
                f"real_roots: diff_real_roots.py --repass --repass-scope all "
                f"--rebaseline-oracle)" for f in gc_find)
            notes.extend(f"{rel}: {n}" for n in gc_notes)

    # EVERY tracked JSON file is CLASSIFIED BY LOCATION, every ORACLE_RECORDS
    # location is checked whatever its block records, and every block the
    # (broad) discovery finds is at a registered location (C-127, C-128).
    blocks, unparsed, docs = tracked_json_blocks(repo)
    findings.extend(unparsed)
    if len(NOT_THE_ORACLE) != NOT_THE_ORACLE_SIZE:
        findings.append(f"NOT_THE_ORACLE holds {len(NOT_THE_ORACLE)} entries, "
                        f"pinned at {NOT_THE_ORACLE_SIZE}; a new one needs a "
                        f"ledger row and a deliberate edit here")
    graded_keys = {(p, tuple(k)) for p, k in GRADED}
    # (1) classification of every tracked DATA file (is_data_file, C-129)
    data_files = sorted(r for r in tracked_files(repo)
                        if is_data_file(r) and (repo / r).is_file())
    for rel in data_files:
        classes = []
        if rel in graded_paths:
            classes.append("GRADED")
        if any(_seg_glob(r[0], rel) for r in ORACLE_RECORDS):
            classes.append("ORACLE_RECORDS")
        if rel in PRE_BASELINE:
            classes.append("PRE_BASELINE")
        if any(_seg_glob(pat, rel) for pat, _ in NO_ORACLE):
            classes.append("NO_ORACLE")
        if not classes:
            findings.append(
                f"{rel}: a tracked data file this gate does not classify. "
                f"Register it in GRADED (a grade), ORACLE_RECORDS (a record "
                f"of one), PRE_BASELINE or NO_ORACLE, with its reason (C-128, "
                f"C-129)")
        elif len(classes) > 1:
            findings.append(f"{rel}: classified twice ({classes}); a file has "
                            f"exactly one class (C-128)")
        if not is_json_data(rel):
            if classes and classes != ["NO_ORACLE"]:
                findings.append(
                    f"{rel}: classified {classes}, but an oracle record is "
                    f"JSON; a non-JSON data file may only be NO_ORACLE (C-129)")
            try:
                text = (repo / rel).read_text(encoding="utf-8",
                                              errors="replace")
            except OSError as e:
                findings.append(f"{rel}: unreadable ({e}) (C-129)")
                continue
            named = [k for k in FINGERPRINT_KEYS if k in text]
            if named:
                findings.append(
                    f"{rel}: a non-JSON data file that names the tree "
                    f"fingerprint key(s) {named}; an oracle record must be "
                    f"JSON, where this gate can check it (C-129)")
    # (2) every ORACLE_RECORDS location, by location
    record_hits = [0] * len(ORACLE_RECORDS)
    record_keys = set()
    for i, (pat, kp, want_clock, graders, why) in enumerate(ORACLE_RECORDS):
        for rel in sorted(docs):
            if not _seg_glob(pat, rel):
                continue
            record_hits[i] += 1
            record_keys.add((rel, kp))
            where = f"{rel} [{'.'.join(kp)}]"
            block = dig(docs[rel], kp)
            if not isinstance(block, dict):
                findings.append(f"{where}: no oracle block at this location, "
                                f"but every file matching {pat} holds "
                                f"{why} there (C-128)")
                continue
            findings.extend(identity_findings(rel, kp, block, image, version,
                                              record, fps))
            if want_clock is not None and block.get("clock") != want_clock:
                findings.append(f"{where}: clock {block.get('clock')!r}, but "
                                f"{why} was graded with clock {want_clock!r}")
            if graders is None:
                if "grading_code" in block:
                    findings.append(f"{where}: records grading_code, but the "
                                    f"row for {why} expects none; register "
                                    f"its grader (C-128)")
                continue
            findings.extend(grading_code_set_findings(where, block, graders))
            # A record names the code of a PAST run: its blobs must exist and
            # agree with its own hash, not equal today's code.
            gc_find, _ = _oracle.grading_code_drift(
                block.get("grading_code"), repo,
                current=block.get("grading_code"))
            findings.extend(f"{where}: {f}" for f in gc_find)
    # (3) every discovered block is at a registered location
    seen_graded, seen_exempt, seen_nab = set(), set(), set()
    n_records = 0
    for rel, path, block in blocks:
        key = (rel, path)
        if key in graded_keys:
            seen_graded.add(key)
            continue
        if key in record_keys:
            n_records += 1
            continue
        if key in NOT_THE_ORACLE:
            seen_exempt.add(key)
            if block.get("image") is not None or block.get("backend") in BACKENDS:
                findings.append(
                    f"{rel} [{'.'.join(path)}]: pinned in NOT_THE_ORACLE but "
                    f"it records image {block.get('image')!r} and backend "
                    f"{block.get('backend')!r}; only a block that declares "
                    f"itself no grade (no image, a backend outside "
                    f"{sorted(BACKENDS)}) may be exempted")
            continue
        if key in NOT_A_BLOCK:
            seen_nab.add(key)
            if set(block) != NOT_A_BLOCK[key]:
                findings.append(
                    f"{rel} [{'.'.join(path)}]: pinned in NOT_A_BLOCK with "
                    f"keys {sorted(NOT_A_BLOCK[key])}, but one holds "
                    f"{sorted(block)} (C-128)")
            continue
        if rel in PRE_BASELINE:
            continue
        findings.append(
            f"{rel} [{'.'.join(path) or '<root>'}]: may record an oracle "
            f"(keys {sorted(IDENTITY_KEYS & set(block))}) at a location this "
            f"gate does not know. Register the location in GRADED (a grade), "
            f"ORACLE_RECORDS (a record of one), NOT_THE_ORACLE (not a grade) "
            f"or NOT_A_BLOCK (not an oracle), with its reason (C-127, C-128)")
    for key in sorted(set(NOT_A_BLOCK) - seen_nab):
        findings.append(f"{key[0]} [{'.'.join(key[1])}]: pinned in NOT_A_BLOCK "
                        f"but no such dict exists; prune it")
    for (rel, path) in sorted(graded_keys - seen_graded):
        if (repo / rel).is_file():
            findings.append(f"{rel}: GRADED names an oracle block at "
                            f"{'.'.join(path)} that the discovery did not find")
    for key in sorted(set(NOT_THE_ORACLE) - seen_exempt):
        findings.append(f"{key[0]} [{'.'.join(key[1])}]: pinned in "
                        f"NOT_THE_ORACLE but no such block exists; prune it")
    for (pat, kp, _, _, why), n in zip(ORACLE_RECORDS, record_hits):
        if n == 0:
            findings.append(f"ORACLE_RECORDS row {pat} [{'.'.join(kp)}] "
                            f"({why}) matches no file; prune it")
    for pat, why in NO_ORACLE:
        if not any(_seg_glob(pat, rel) for rel in data_files):
            findings.append(f"NO_ORACLE row {pat} ({why}) matches no tracked "
                            f"data file; prune it")
    for rel in sorted(PRE_BASELINE):
        f = repo / rel
        if not f.is_file():
            findings.append(f"{rel}: listed in PRE_BASELINE but missing")
            continue
        # PARSED, not a JSON literal (C-129): `"image":"<pin>"` with other
        # spacing, or the image in any nested block, is found too.
        pdoc = docs.get(rel)
        if pdoc is None:
            findings.append(f"{rel}: listed in PRE_BASELINE but not a parsed "
                            f"tracked JSON file")
            continue

        def _images(d):
            if isinstance(d, dict):
                for k, v in d.items():
                    if k == "image" and isinstance(v, str):
                        yield v
                    yield from _images(v)
            elif isinstance(d, list):
                for v in d:
                    yield from _images(v)
        if image in set(_images(pdoc)):
            findings.append(f"{rel} now records the pinned image but is still in "
                            f"PRE_BASELINE; move it to GRADED")

    # 4. nothing else starts a TeX engine
    scanned = 0
    for rel in sorted(tracked_files(repo)):
        if not rel or rel in ORACLE_FILES or rel in SCANNER_FILES:
            continue
        p = repo / rel
        name = p.name
        # Extensions are matched LOWERCASED (C-129): `x.SH` runs as well.
        low = rel.lower()
        if low.endswith(".py"):
            scan = scan_python
        elif low.endswith(".mk") or name in ("Makefile", "GNUmakefile", "makefile"):
            scan = (lambda t: scan_shell(t, make=True))
        elif low.endswith((".sh", ".bash", ".zsh", ".ksh", ".command")):
            scan = scan_shell
        elif low.endswith(OTHER_CODE_EXT):
            scan = scan_other
        elif low.endswith(".ml"):
            scan = scan_ocaml
        elif rel.startswith(".github/workflows/") and low.endswith((".yml", ".yaml")):
            allow = WORKFLOW_ALLOW.get(rel, ())
            scan = (lambda t, a=allow: scan_shell(t, a, yaml=True))
        elif _command_file_kind(rel) is not None:
            scan = _command_file_kind(rel)
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

    for n in notes:
        print(f"[oracle-pin] NOTE: {n}", file=sys.stderr)
    if findings:
        print("[oracle-pin] FAIL:", file=sys.stderr)
        for f in findings:
            print(f"  - {f}", file=sys.stderr)
        return 1
    print(f"[oracle-pin] OK: {len(blocks)} oracle blocks in tracked JSON "
          f"files, every one at a registered location ({len(seen_graded)} "
          f"GRADED, {n_records} ORACLE_RECORDS, {len(seen_exempt)} not the "
          f"oracle, {len(blocks) - len(seen_graded) - n_records - len(seen_exempt)} "
          f"not oracle blocks); {len(data_files)} tracked data files classified ({len(docs)} JSON); "
          f"{sum(record_hits)} ORACLE_RECORDS locations checked by location; {len(GRADED)} graded artefacts name {image} with "
          f"its tree fingerprints, all on {record}; "
          f"{len(GRADED) - len(GRADING_CODE_PENDING)} name their current "
          f"grading code, {len(GRADING_CODE_PENDING)} pending (OPEN-126); "
          f"{len(PRE_BASELINE)} pre-baseline artefacts "
          f"pinned; {scanned} tracked code files start no TeX engine directly")
    return 0


if __name__ == "__main__":
    sys.exit(main())
