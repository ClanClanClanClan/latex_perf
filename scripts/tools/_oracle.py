#!/usr/bin/env python3
"""The ONE pdflatex oracle of this project (ADR-012 decision 7).

WHY THIS FILE EXISTS.

Until 2026-09-27 every grading tool in `scripts/tools/` ran whatever `pdflatex`
was first on PATH, and checked only its `--version` banner against the pin
`pdfTeX 3.141592653-2.6-1.40.29`. The banner pins the ENGINE BINARY and nothing
else: the macro layer (LaTeX kernel, every package, every font map) is whatever
the local TeX Live tree holds. On the maintainer's laptop that tree had seen 37
`tlmgr update` sessions since March, a failed restore, and orphaned
pdfmanagement files, while still printing the pinned banner. So two machines
that both "passed the pin check" could grade the same paper differently, and
the project's published numbers were graded by the laptop.

The owner's decision (ADR-012, decision 7): the oracle is CI's digest-pinned
TeX Live image, `TEX_IMAGE` in `.github/workflows/tex-oracle.yml` (the
workflow is the source of truth; this module reads it from there), run locally
through a container. The laptop TeX Live is not the oracle.

WHAT THIS MODULE GUARANTEES.

* One entry point. Every grading tool calls `get_oracle()` and runs pdflatex
  through it; nothing else in the repo may shell out to `pdflatex` directly
  (`check_oracle_pin.py` enforces that).
* Two backends, chosen POSITIVELY, never by fallback:
    - `container`: a long-lived container of the pinned image, reached with
      `docker exec`. The work directory must lie under the oracle work root,
      which is mounted into the container at the SAME absolute path (colima
      mounts only the user's home, so `/private/tmp` is invisible inside it;
      this is checked by a nonce round-trip, not assumed).
    - `native`: used ONLY when this process already runs inside the pinned
      image (CI's tex-oracle job). It is selected by `LP_ORACLE_IN_IMAGE`,
      which tex-oracle.yml sets to the image reference, AND it is then
      verified: the TeX tree's fingerprint must equal the one recorded below
      for this architecture. Setting the variable on a laptop fails loudly.
  If neither is available the oracle raises `OracleUnavailable`. There is no
  path on which a laptop pdflatex grades anything.
* The digest pins an INDEX, not an image: it names one arm64 and one amd64
  image. CI grades on amd64; a Mac grades on arm64. Their TeX trees are
  compared by `macro_layer_sha256` (every non-binary TeX Live package with its
  revision), recorded below for both architectures; `tlpdb_sha256` differs by
  construction because the tlpdb lists the architecture's binary packages.
* Every artefact records `provenance()`: image, architecture, banner, the tree
  fingerprints and the backend. `check_oracle_pin.py` refuses a graded artefact
  whose recorded image is not the workflow's.

THE PROTOCOL (unchanged from the recorded one; STRICT_TIER_DESIGN.md §B.4).

`pdflatex -interaction=nonstopmode -halt-on-error <toplevel>`, the stock
restricted shell-escape (no `-shell-escape`, no `-no-shell-escape`, OPEN-053;
since review round 5 the graded argv is an allow-list, `check_engine_argv`),
up to 3 passes: run to the first rc 0, then ONE confirming pass whose rc is
authoritative (the `fr_toc_second_pass` lesson). The result also records
whether a PDF was produced; `compiles` requires rc 0 AND a PDF (§B.4 E0).

Usage as a tool:
  _oracle.py info                 print the oracle's provenance (starts it;
                                  runs the container's full state scan)
  _oracle.py fingerprint          fingerprint the TeX tree this process sees
  _oracle.py assert-native        inside the image: verify, exit 0/2
  _oracle.py workroot             print the work root (for shell callers)
  _oracle.py pdflatex [--timeout S] ARGS...
                                  run ONE pdflatex in the current directory
                                  through the oracle; exit with its rc (124 on
                                  timeout, INFRA_RC=125 when the oracle itself
                                  failed). The shim the shell graders use, on
                                  both backends; its run gets the protocol's
                                  environment (graded_env), never the host's.
  _oracle.py vet --dir D [--output F -- ARGS...]
                                  shell graders: refuse (INFRA_RC) a run when
                                  D is short of space or F shows pdfTeX failing
                                  to write its own output; exit 0 otherwise
  _oracle.py rm FILES...          delete work files through the oracle (see
                                  ContainerOracle.remove); exit 0, or 2
  _oracle.py stop                 remove the long-lived container
"""
from __future__ import annotations

import hashlib
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import time
import uuid
from dataclasses import dataclass
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
WORKFLOW = REPO / ".github/workflows/tex-oracle.yml"

PROTOCOL = ("-interaction=nonstopmode -halt-on-error, restricted shell-escape "
            "(the pdflatex default, OPEN-053), up to 3 passes: run to the first "
            "rc 0, then ONE confirming pass whose rc is authoritative; PDF "
            "recorded (compiles = rc 0 AND a PDF, STRICT_TIER_DESIGN.md B.4 E0)")
MAX_PASSES = 3

# THE LONG-LIVED CONTAINER REAPS AND IS BOUNDED (C-97). Its PID 1 was
# `sleep infinity`, which reaps nothing: every run killed by the protocol's
# timeout left its orphans as zombies (3 per killed EPS conversion: sh, perl,
# gs; 106 in the shared container after two days), and the reviewer MEASURED
# (with a stand-in --pids-limit 14) a compiling EPS document graded rc 1 with
# no OracleError once they filled the limit: the fork inside restricted
# \write18 failed silently. Now: `--init` (PID 1 = docker-init, which reaps),
# a pids limit far above measured need so one runaway job cannot exhaust the
# VM that every oracle container shares, and a per-run check, in the same
# exec as the run, that no process was left behind: an orphan of PID 1 other
# than the container's own `sleep infinity`, or a zombie, older than 2 s and still
# there 1 s later. Refused (OracleError), never graded.
PIDS_LIMIT = 4096
LEAK_CHECK_SH = (
    'lp_leak_list() { ps -eo pid=,ppid=,stat=,etimes=,args= | '
    'awk \'($2 == 1 && !($5 == "sleep" && $6 == "infinity" && NF == 6) && $4 >= 2) '
    '|| ($3 ~ /^Z/ && $4 >= 2) '
    '{print $1 ":" $5 ":" $3}\' | head -5 | tr "\\n" " "; }; '
    'lp_leak() { l=$(lp_leak_list); [ -z "$l" ] && return 0; sleep 1; '
    'l=$(lp_leak_list); [ -z "$l" ] && return 0; '
    'printf "\\n%s_LEAK=%s\\n" "$1" "$l" >&2; return 1; }; ')

# The shim's exit code when the ORACLE failed (docker unreachable, container
# gone, a refused environment), as opposed to pdflatex failing. It used to be 2,
# which the shell graders could not tell from a pdflatex error exit, so an
# infrastructure failure was graded as "does not compile" (C-70's rule broken:
# unmeasured is not a failure). 125 is what `docker exec` and `timeout` use for
# "the wrapper failed"; pdflatex itself never exits with it. Every shell grader
# treats 124-127 as NOT GRADED.
INFRA_RC = 125
# The shim's subcommand (`_oracle.py pdflatex ARGS...`), named once so a caller
# (check_oracle_infra_grading.py) need not spell an engine name itself.
SHIM_COMMAND = "pdflatex"

# MEASURED 2026-09-27 from the two platform images of the pinned index
# (arm64 manifest sha256:010653c0bb13..., amd64 manifest sha256:c268e1c3611a...),
# by `_oracle.py fingerprint` run inside each. A re-pin of TEX_IMAGE must
# re-measure both; check_oracle_pin.py fails when the workflow's digest is not
# the one these were measured for.
FINGERPRINTED_IMAGE = ("texlive/texlive@sha256:"
                       "4984977ccf5afe883cb382d0163f267de0d029d140bb7a9e8f4c19f0b781d57b")
TREE_FINGERPRINTS = {
    "aarch64": {
        "tlpdb_sha256": "541f1efbfba579ff2db5db5781e9bbd6511dcebfe883cbac82d2f8c9ff272dfe",
        "macro_layer_sha256": "27089de69500214440bb78910236f788be89a4692c989bdc217ca93e5ba91c10",
        "fmt_sha256": "a476533c0d6e64f08b47de9c109cc4e9a04874f5bc7a897ad5b622ef9faa54d3",
    },
    "x86_64": {
        "tlpdb_sha256": "48e01be17878c251ee82c881bb0d94d83120956da8339b52defcee2d5cd7e677",
        "macro_layer_sha256": "27089de69500214440bb78910236f788be89a4692c989bdc217ca93e5ba91c10",
        "fmt_sha256": "5a9dfc4e27b5c67c737d9bb2bd7d623c6470a4fd9740ff0376d4b871e3a9afc2",
    },
}
# fmt_sha256 is per-architecture (a dumped format is a memory image), MEASURED
# 2026-09-27 as `sha256sum $(kpsewhich -engine=pdftex pdflatex.fmt)` in
# `docker run --platform linux/{arm64,amd64}` of the pinned digest. It is
# compared so that a container mutated by an `fmtutil`/`tlmgr` run inside it
# cannot keep grading: the base image is pinned by digest, a live container is
# not.

# Environment variables that shape a pdflatex run and are forwarded into the
# container. Nothing else from the host crosses: in particular not PATH, HOME
# or any TEXMF* tree pointing at the host's TeX Live.
_ENV_FORWARD = re.compile(
    r"^(TEXMFHOME|TEXMFVAR|TEXMFCONFIG|openin_any|openout_any|"
    r"SOURCE_DATE_EPOCH|FORCE_SOURCE_DATE|max_print_line|error_line|"
    r"half_error_line|TEXINPUTS|BIBINPUTS|BSTINPUTS|L0_VALIDATORS|"
    r"TMPDIR|TMP|TEMP|JAVA_TOOL_OPTIONS)$")
# Search-path variables. A host value would change a grade silently: without an
# empty component it REPLACES the image's own search path (every document then
# fails), and an absolute component outside the work root points at a
# directory the container cannot see or, worse, one it can. So each absolute
# component must lie inside the work root, and the value must keep an empty
# component (`:` at either end, or `::`) so the image's default path stays.
_SEARCH_PATHS = ("TEXINPUTS", "BIBINPUTS", "BSTINPUTS")

# THE ORACLE'S TeX ENVIRONMENT: the ONE definition. Every grader (through
# `tex_env()` / `oracle_tex_env()`) and the contract generator
# (gen_contract.py, through `oracle_tex_vars()`) import it; nobody restates it.
# Before this existed the values were spelled out in eight graders and, a
# third time, in gen_contract.py, whose parser gate then checked the copy
# against the graders' SOURCE TEXT -- and broke (three false FAILs) the day
# #617 moved the graders' copy here, without anything having changed.
# check_gen_contract_parsers.py asserts that no other tool restates it.
#   openin_any/openout_any=p   paranoid file access (no parent or absolute
#                              writes, no dot files)
#   SOURCE_DATE_EPOCH=0        a fixed \pdfcreationdate/ID. It does NOT fix
#                              \year/\month/\day/\time: those follow the real
#                              clock unless FORCE_SOURCE_DATE=1, which the
#                              graders do not set (gen_contract.py sets it on
#                              its name-set runs, as a documented override).
ORACLE_TEX_VARS = {"openin_any": "p", "openout_any": "p", "SOURCE_DATE_EPOCH": "0"}


def private_texmf_vars(td) -> dict:
    """A private TEXMFHOME/TEXMFVAR/TEXMFCONFIG below the work directory `td`,
    so no state (fonts made by mktexpk, caches, configuration) crosses from
    one run to the next. These are EVERY writable tree of kpathsea's TEXMF in
    the pinned image (MEASURED 2026-09-28, `kpsewhich -var-value=TEXMF` with
    HOME=/tmp: {TEXMFCONFIG,TEXMFVAR,TEXMFHOME,!!TEXMFLOCAL,!!TEXMFSYSCONFIG,
    !!TEXMFSYSVAR,!!TEXMFDIST}; the four `!!` trees belong to the image and
    are checked by ContainerOracle.check_state). TEXMFCONFIG was missing
    until review round 5: kpathsea searches it FIRST, it defaulted to the
    long-lived container's /tmp/.texlive2026/texmf-config, and a .sty
    written there by one run (through a shell escape the argv then allowed)
    turned another document's grade from rc 1 to rc 0 (MEASURED, C-91)."""
    td = Path(td)
    return {"TEXMFHOME": str(td / "th"), "TEXMFVAR": str(td / "tv"),
            "TEXMFCONFIG": str(td / "tc")}


# A PRIVATE TEMPORARY DIRECTORY PER RUN (C-93, OPEN-118 known limit (i)).
# Restricted \write18 (the protocol's default) runs the programs of the
# image's shell_escape_commands, and kpathsea runs mktex* for a missing font;
# those write temporary files, and with the image's defaults they wrote them
# in the LONG-LIVED container's /tmp. MEASURED 2026-09-29 in a fresh container
# of the pinned digest, each command driven from a document and the
# container's root filesystem diffed (find / -xdev -newerct) around the run:
#   repstopdf -> gs      /tmp/gs_XXXXXX scratch files: removed on a normal
#                        exit, LEFT (3 per conversion, 0 bytes) when the
#                        protocol's timeout kills the run. That is how the
#                        shared container got its six /tmp/gs_* (two timed-out
#                        EPS conversions, 2026-09-28 21:48) and #622's
#                        check_state then refused every later session.
#                        gs honours TMPDIR (measured: the files land in it).
#   mktextfm/mktexpk/    /tmp/mt$$.tmp, or $TMPDIR/mt$$.tmp (mktex.opt);
#   mktexmf              removed by its trap on TERM, left on KILL.
#   texosquery-jre8      java: /tmp/hsperfdata_root/<pid>, a FIXED path that
#                        ignores TMPDIR and java.io.tmpdir; the directory's
#                        ctime moves on EVERY run, which check_state refuses.
#                        -XX:-UsePerfData (JAVA_TOOL_OPTIONS) stops it
#                        (measured: nothing under /tmp changes).
#   latexminted, memoize-extract.py/.pl, bibtex, bibtex8, makeindex,
#   extractbb, gregorio, l3sys-query, kpsewhich, r-mpost: no path outside the
#                        run directory changed (measured). Python's tempfile
#                        reads TMPDIR/TEMP/TMP, Perl's File::Temp TMPDIR.
# So every graded run gets TMPDIR=TMP=TEMP=<td>/lp-tmp and a JAVA_TOOL_OPTIONS
# naming it, and the oracle creates the directory before the run (a missing
# TMPDIR makes gs and mktex.opt fail, which WOULD change a grade). Same rc and
# byte-identical PDF with and without, for every command above (measured).
# The state check stays strict: a /tmp file is never a graded run's now.
PRIVATE_TMP_NAME = "lp-tmp"
# What a TMPDIR may not hold: whitespace (JAVA_TOOL_OPTIONS is split on it),
# control characters, and what kpathsea or a shell would expand.
_PLAIN_PATH_BAD = re.compile(r"[\s\x00-\x1f\x7f~$!{}:,;'\"\\`*?]")
_GRADING_TMP =("TMPDIR", "TMP", "TEMP", "JAVA_TOOL_OPTIONS")


def java_tool_options(tmpdir: str) -> str:
    return f"-XX:-UsePerfData -Djava.io.tmpdir={tmpdir}"


def private_tmp_vars(td) -> dict:
    """TMPDIR/TMP/TEMP (and java's) in a private directory below `td`."""
    t = str(Path(td) / PRIVATE_TMP_NAME)
    return {"TMPDIR": t, "TMP": t, "TEMP": t,
            "JAVA_TOOL_OPTIONS": java_tool_options(t)}


def check_private_tmp(env: dict, inside=None) -> str | None:
    """Refuse (OracleError) temporary-directory variables that are not ONE
    plain absolute path (inside the work root when `inside` is given), with
    TMP/TEMP/JAVA_TOOL_OPTIONS exactly derived from TMPDIR. Returns TMPDIR
    (None when the run has none: run_engine may, a graded run may not)."""
    tmp = env.get("TMPDIR")
    if tmp is None:
        extra = [k for k in _GRADING_TMP if k in env]
        if extra:
            raise OracleError(f"{extra} without TMPDIR")
        return None
    if (not os.path.isabs(tmp) or _PLAIN_PATH_BAD.search(tmp)
            or ".." in Path(tmp).parts or (inside is not None and not inside(Path(tmp)))):
        raise OracleError(f"TMPDIR={tmp} is not one plain absolute path"
                          + (" inside the oracle work root" if inside else ""))
    want = {"TMP": tmp, "TEMP": tmp, "JAVA_TOOL_OPTIONS": java_tool_options(tmp)}
    bad = [k for k, v in want.items() if env.get(k) != v]
    if bad:
        raise OracleError(f"{bad} are not derived from TMPDIR={tmp}")
    return tmp


def make_private_tmp(env: dict, inside=None) -> None:
    """Create the run's TMPDIR (checked first) before the engine starts."""
    tmp = check_private_tmp(env, inside)
    if tmp is not None:
        Path(tmp).mkdir(parents=True, exist_ok=True)


def oracle_tex_vars(td) -> dict:
    """ONLY the variables that shape a graded run (no host environment)."""
    return {**private_texmf_vars(td), **private_tmp_vars(td), **ORACLE_TEX_VARS}


def oracle_tex_env(td) -> dict:
    """The per-run environment a Python grader passes: the host environment
    with `oracle_tex_vars(td)` on top. Only its `_ENV_FORWARD` variables reach
    an engine, on either backend (engine_env); the rest is ignored."""
    return dict(os.environ, **oracle_tex_vars(td))


# ONE GRADING PROTOCOL, IMPOSED BY THE ORACLE, NOT CHOSEN BY THE CALLER
# (OPEN-118 known limit (b), C-91). Until 2026-09-28 ORACLE_TEX_VARS reached a
# graded run only when the CALLER put it there: the Python graders did (through
# tex_env), but the `_oracle.py pdflatex` shim passed the host environment, so
# false_ready_oracle.sh and diff_compile_check.sh graded with pdfTeX's defaults
# (openin_any/openout_any unset, no SOURCE_DATE_EPOCH) or with whatever the
# host exported; on the native backend (CI) they ran `pdflatex` bare; and
# check_apply_fixes_roundtrip passed `dict(os.environ)`, with neither the
# variables nor a private TEXMFVAR. So `graded_env` is applied INSIDE
# run_pdflatex, the one path every graded run takes (run_once,
# run_to_fixpoint, the shim), and a graded run's TeX-shaping variables are
# exactly:
#   * ORACLE_TEX_VARS, imposed over any value the caller's dict held (a host
#     `SOURCE_DATE_EPOCH=1700000000` or `openout_any=a` is overridden, not
#     forwarded);
#   * the private TEXMFHOME/TEXMFVAR the caller names, which are REQUIRED (a
#     run without them would share the container's persistent TEXMFVAR);
#   * the private TMPDIR beside them, REQUIRED (C-93), with TMP, TEMP and
#     JAVA_TOOL_OPTIONS derived from it (see private_tmp_vars);
#   * nothing else: every other `_ENV_FORWARD` variable (FORCE_SOURCE_DATE,
#     max_print_line, error_line, half_error_line, TEXINPUTS, BIBINPUTS,
#     BSTINPUTS) is DROPPED. No grader sets one, so one in the dict came from
#     the host, and it would change a grade (FORCE_SOURCE_DATE=1 makes \today
#     follow SOURCE_DATE_EPOCH) or the log's line breaks.
# Override, not refuse: the shell graders discard the shim's stderr, so a
# refusal would reach the user as an unexplained "not graded" for an
# environment variable they may not know they export (SOURCE_DATE_EPOCH is
# common in reproducible-build shells). The shim reports what it overrode on
# stderr. run_engine (gen_contract.py, not a grader) is unaffected: its
# environment is EXACTLY what the caller passes, with documented overrides.
_GRADING_TEXMF = ("TEXMFHOME", "TEXMFVAR", "TEXMFCONFIG")


def graded_env(env: dict | None) -> dict:
    """The TeX variables of a GRADED pdflatex run built from `env`: its
    private TEXMFHOME/TEXMFVAR/TEXMFCONFIG (required), its private TMPDIR
    beside them (required; TMP/TEMP/JAVA_TOOL_OPTIONS derived from it, C-93),
    ORACLE_TEX_VARS imposed, every other
    `_ENV_FORWARD` variable dropped. See the block above. Non-TeX keys of `env`
    are kept here but never reach the engine: each backend passes only
    `engine_env` (the image's environment plus `_ENV_FORWARD` variables)."""
    env = dict(env or {})
    missing = [k for k in _GRADING_TEXMF if not env.get(k)]
    if missing:
        raise OracleError(
            f"a graded run needs a private {'/'.join(missing)} (oracle_tex_vars "
            f"or tex_env): without one the container's persistent TEXMFVAR "
            f"carries state from run to run")
    # C-93: the run's temporary files live with its private trees. TMPDIR is
    # REQUIRED and must be the private one beside TEXMFVAR (a host TMPDIR --
    # /tmp, /var/folders/... -- is refused, not forwarded); TMP, TEMP and
    # JAVA_TOOL_OPTIONS are derived from it, never taken from `env`.
    tmp = env.get("TMPDIR")
    want_tmp = (private_tmp_vars(Path(env["TEXMFVAR"]).parent)["TMPDIR"]
                if env.get("TEXMFVAR") else tmp)  # TEXMFVAR: required above
    if not tmp or tmp != want_tmp:
        raise OracleError(
            f"a graded run needs its private TMPDIR={want_tmp} (oracle_tex_vars "
            f"or tex_env), got {tmp!r}: without it restricted \\write18 "
            f"(repstopdf -> gs, mktex*) leaves temporary files in the "
            f"long-lived container's /tmp (C-93)")
    out = {k: v for k, v in env.items() if not _ENV_FORWARD.match(k)}
    out.update({k: env[k] for k in _GRADING_TEXMF if k in env})
    if tmp:  # always, unless the check above is gone
        out.update(private_tmp_vars(Path(tmp).parent))
    out.update(ORACLE_TEX_VARS)
    return out


# THE ENGINE'S WHOLE ENVIRONMENT IS AN ALLOW-LIST, ON BOTH BACKENDS (C-91,
# review round 4). graded_env removes the `_ENV_FORWARD` names and keeps every
# other variable of the caller's dict, and until this block the NATIVE backend
# (CI's tex-oracle job) handed that whole dict to pdflatex. A blocklist cannot
# be complete here, because kpathsea reads ANY variable named after a
# configuration key: `VAR_progname` and `VAR.progname` before `VAR`
# (`openout_any_pdflatex`, `shell_escape`, `TEXMFCNF`, `TEXFORMATS`, ...).
# MEASURED by the round-4 review in the pinned image through the native shim:
# a host `openout_any_pdflatex=a` flipped a grade (rc 1 -> rc 0, the \openout
# to /tmp written) while the engine's own `openout_any` still read `p`, and a
# host `shell_escape=t` turned unrestricted \write18 on (\pdfshellescape 2 ->
# 1); the container backend, which forwards `_ENV_FORWARD` names only, was
# unaffected. So an engine now sees EXACTLY what `docker exec` gives it in the
# container: the image's own environment (below) plus the forwarded
# `_ENV_FORWARD` variables, and nothing of the host. The container backend
# checks that its container really has this environment (a container started
# with an extra `-e` under the oracle's name would otherwise leak one).
# IMAGE_ENV is `docker inspect --format '{{json .Config.Env}}'` of the pinned
# digest (MEASURED 2026-09-28, identical inside the running oracle container
# apart from HOSTNAME) with HOME=/tmp, which the container is started with.
IMAGE_ENV = {
    "HOME": "/tmp",
    "PATH": "/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin",
    "LANG": "C.UTF-8",
    "LC_ALL": "C.UTF-8",
    "TEXLIVE_INSTALL_NO_CONTEXT_CACHE": "1",
    "NOPERLDOC": "1",
    "DEBIAN_FRONTEND": "noninteractive",
}
# Variables of the container's environment that are not the image's and do
# not reach TeX's configuration: docker sets HOSTNAME per container.
_CONTAINER_ONLY_ENV = frozenset(("HOSTNAME",))


def engine_env(tex_vars: dict | None, base: dict = IMAGE_ENV) -> dict:
    """The COMPLETE environment of an engine run: `base` (the image's) plus the
    `_ENV_FORWARD` variables of `tex_vars`. Every other key of `tex_vars` (a
    caller's copy of the host environment) is dropped, whatever its name."""
    out = dict(base)
    out.update({k: v for k, v in (tex_vars or {}).items() if _ENV_FORWARD.match(k)})
    return out


def check_container_env(env: dict, where: str) -> None:
    """The container's own environment must be IMAGE_ENV (plus HOSTNAME)."""
    got = {k: v for k, v in env.items() if k not in _CONTAINER_ONLY_ENV}
    if got != IMAGE_ENV:
        extra = sorted(set(got) - set(IMAGE_ENV))
        diff = sorted(k for k in IMAGE_ENV if got.get(k) != IMAGE_ENV[k])
        raise OracleError(
            f"{where}: the container's environment is not the pinned image's "
            f"(extra {extra[:6]}, different {diff[:6]}); every exec would give "
            f"pdflatex those variables. Remove the container (`_oracle.py stop`) "
            f"so the oracle starts a clean one.")


# The host variables the shim names in its note: every name kpathsea or TeX
# could read (the configuration keys and their `_progname`/`.progname` forms,
# the search paths). None of them reaches an engine on either backend; the
# note only tells a user who exports one that it had no effect.
_HOST_TEX_NOTE = re.compile(
    r"^(TEXMF\w*|TEX\w*|KPSE\w*|\w*INPUTS(\W\w*)?|\w*FONTS(\W\w*)?|"
    r"(openin_any|openout_any|shell_escape\w*|SOURCE_DATE_EPOCH|"
    r"FORCE_SOURCE_DATE|max_print_line|error_line|half_error_line|"
    r"max_strings|main_memory|extra_mem_\w+|save_size|buf_size|"
    r"hash_extra|pool_size|string_vacancies|MKTEX\w*|MISSFONT_LOG|"
    r"texmf_casefold_search|guess_input_kanji_encoding|command_line_encoding)"
    r"([._]\w+)?)$")


def host_tex_overrides(environ=None) -> list[str]:
    """The host TeX-shaping variables a graded run does NOT inherit (overridden
    or dropped), as `NAME=value` strings, for the shim's note."""
    environ = os.environ if environ is None else environ
    return sorted(f"{k}={v}" for k, v in environ.items()
                  if (_ENV_FORWARD.match(k) or _HOST_TEX_NOTE.match(k))
                  and k != "L0_VALIDATORS"
                  # a host TMPDIR is ubiquitous (macOS sets one) and shapes no
                  # grade; the run's own private one replaces it (C-93)
                  and k not in ("TMPDIR", "TMP", "TEMP")
                  and not (k in ORACLE_TEX_VARS and v == ORACLE_TEX_VARS[k])
                  and not (k in IMAGE_ENV and v == IMAGE_ENV[k]))


# The TeX engines the oracle runs. `pdflatex` is the grading engine; `pdftex`
# is the same binary without a format, which gen_contract.py runs as INITEX
# (`pdftex -ini`) to enumerate the engine's primitives and trace the kernel.
ENGINE_PDFLATEX = "pdflatex"
ENGINE_PDFTEX = "pdftex"
ENGINES = (ENGINE_PDFLATEX, ENGINE_PDFTEX)
# THE ONE VOCABULARY OF TeX ENGINE NAMES (C-91 review round 4): image_command
# refuses every one of them and check_oracle_pin.py scans for every one of
# them, so the two cannot disagree (the round-4 review MEASURED the gate's own
# 11-name list missing `pdflatex-dev`, `mllatex`, `pdfjadetex`, `lualatex-dev`
# while this table held 30). MEASURED 2026-09-28 in the pinned image by
# listing bin/<arch>/: every engine binary, every link to one (a link's name
# selects its format: `mllatex`, `pdfxmltex`, `latex-dev` and `jadetex` each
# load a LaTeX format), and every shipped front end that runs an engine on a
# document; plus the names of earlier releases and other distributions the
# old table held (`virtex`, `lamed`, `tectonic`, `texi2dvi`, `rubber`, ...).
_TEX_ENGINE_CORE = (
    "tex", "initex", "virtex", "etex", "pdftex", "pdfetex", "luatex",
    "luahbtex", "luajittex", "luajithbtex", "luametatex", "xetex", "ptex",
    "eptex", "euptex", "uptex", "aleph", "lamed", "hitex", "tectonic")
_TEX_ENGINE_LINKS = (   # format-named links (bin/<arch>/NAME -> an engine)
    "amstex", "csplain", "pdfcsplain", "luacsplain", "eplain", "latex",
    "latex-dev", "pdflatex", "pdflatex-dev", "lualatex", "lualatex-dev",
    "dvilualatex", "dvilualatex-dev", "dviluatex", "xelatex", "xelatex-dev",
    "platex", "platex-dev", "uplatex", "uplatex-dev", "hilatex", "jadetex",
    "pdfjadetex", "xmltex", "pdfxmltex", "mllatex", "mltex", "mex", "pdfmex",
    "utf8mex", "texsis", "lollipop", "optex", "texlua", "texluac", "texluajit",
    "texluajitc", "context", "mtxrun")
_TEX_ENGINE_DRIVERS = (  # front ends that start an engine on a document
    "latexmk", "arara", "llmk", "cluttex", "cllualatex", "clxelatex",
    "ptex2pdf", "texexec", "texfot", "pdftex-quiet", "simpdftex",
    "xelatex-unsafe", "xetex-unsafe", "runtexfile", "runtexshebang", "lwarpmk",
    "l3build", "make4ht", "htlatex", "htxelatex", "htxetex", "httex", "httexi",
    "htmex", "xhlatex", "mk4ht", "tex4ebook", "latexdiff-vc", "pdfjam",
    "pdfxup", "texliveonfly", "ps4pdf", "pst2pdf", "ltximg", "mkjobtexmf",
    "mptopdf", "fmtutil", "fmtutil-sys", "fmtutil-user", "mktexfmt",
    "bg5latex", "bg5pdflatex", "bg5+latex", "bg5+pdflatex", "gbklatex",
    "gbkpdflatex", "cef5latex", "cef5pdflatex", "ceflatex", "cefpdflatex",
    "cefslatex", "cefspdflatex", "sjislatex", "sjispdflatex", "texi2dvi",
    "texi2pdf", "rubber", "latexrun")
TEX_ENGINE_BINARIES = frozenset(_TEX_ENGINE_CORE + _TEX_ENGINE_LINKS
                                + _TEX_ENGINE_DRIVERS)
# A FORMAT SELECTOR picks a TeX engine's personality whatever the binary is
# called: `&pdflatex` (TeX's own syntax), `-fmt=`/`--fmt`, and `-progname=`
# (MEASURED 2026-09-28 by the round-4 review: `mllatex`, `latex`, `pdfxmltex`
# and `jadetex` with `-progname=pdflatex` each load format=pdflatex and write
# a PDF with rc 0).
FMT_SELECTOR = re.compile(r"^(&[A-Za-z][\w.-]*|-{1,2}(fmt|progname)(=\S*)?)$")
# argv[0] values image_command refuses because they run arbitrary commands
# (`sh -c 'pdftex ...'`): a shell or interpreter would hide the engine from
# the argument check above.
_IMAGE_SHELLS = frozenset(("sh", "bash", "dash", "zsh", "ksh", "busybox", "env",
                           "python", "python3", "perl", "lua", "texlua",
                           "timeout", "nice", "nohup", "stdbuf", "setsid"))

_DOCKER_CANDIDATES = ("docker", "/opt/homebrew/bin/docker", "/usr/local/bin/docker")


class OracleError(RuntimeError):
    """The oracle cannot give a trustworthy answer. Never caught to fall back."""


# THE ENGINE'S ARGV IS AN ALLOW-LIST TOO (C-91, review round 5). graded_env and
# engine_env fix the ENVIRONMENT, but pdfTeX also reads its configuration from
# the COMMAND LINE, and until round 5 run_pdflatex, run_once, run_to_fixpoint
# and the `_oracle.py pdflatex` shim passed argv through unchecked (only
# image_command looked at it). MEASURED by the round-5 review through the shim,
# on both backends: `-cnf-line=openout_any=a` gave rc 0 with an \openout to
# /tmp written; `-cnf-line=shell_escape=t` and `-shell-escape` gave
# \pdfshellescape=1; and with shell escape a \write18 put a .sty into the
# container's persistent TEXMFCONFIG, after which a CLEAN graded run of another
# document that \usepackage'd it went from rc 1 to rc 0. A blocklist of
# options cannot be complete (web2c takes any `-cnf-line`, `-output-directory`,
# `-translate-file`, `-mktex`, `-kpathsea-debug`, a format selector, `-ini`, a
# first line that is TeX code), so a GRADED run accepts exactly the options a
# grader uses, and exactly one file argument:
#   -interaction=<batchmode|nonstopmode|scrollmode|errorstopmode>
#   -halt-on-error  -file-line-error  -recorder  -draftmode
#   (each also with `--`); `-jobname` is refused: no grader passes it (grep:
#   run_once/the shell graders pass the interaction flags and the file only).
# The file argument: one, not starting (after blanks) with `-`, `&` (a format
# selector), `\` (TeX code as the first line) or `*` (INITEX's eTeX switch);
# no whitespace or control character (web2c joins argv with spaces into TeX's
# first line, so `a.tex \x` would run `\x`); no `..` component; and an
# absolute path only inside the run directory. Anything else is OracleError
# (the shim: INFRA_RC), never a grade. run_engine (gen_contract.py, not a
# grader) has its own, wider allow-list: RUN_ENGINE_OPTIONS below.
_INTERACTION_MODES = frozenset(("batchmode", "nonstopmode", "scrollmode",
                                "errorstopmode"))
GRADED_FLAGS = frozenset(("halt-on-error", "file-line-error", "recorder",
                          "draftmode"))
# run_engine's options: GRADED_FLAGS plus the INITEX jobs of gen_contract.py.
# A `-jobname=`/`-progname=`/`-translate-file=` VALUE must match exactly.
RUN_ENGINE_FLAGS = GRADED_FLAGS | {"ini", "etex"}
RUN_ENGINE_VALUED = {
    "jobname": re.compile(r"[A-Za-z0-9_-]{1,64}"),
    "progname": re.compile(r"pdflatex"),
    "translate-file": re.compile(r"cp227\.tcx"),
}
_UNSAFE_ARG_CHARS = re.compile(r"[\s\x00-\x1f\x7f]")


def _option(a: str):
    """(name, value) of `-name[=value]`/`--name[=value]`, else None."""
    if not a.startswith("-"):
        return None
    body = a[2:] if a.startswith("--") else a[1:]
    name, eq, value = body.partition("=")
    return name, (value if eq else None)


def check_engine_argv(args, cwd, *, graded: bool) -> None:
    """Refuse (OracleError) any argv that is not on the allow-list above."""
    if not isinstance(args, (list, tuple)) or not all(isinstance(a, str) for a in args):
        raise OracleError(f"engine argv must be a list of str, got {args!r:.200}")
    flags = GRADED_FLAGS if graded else RUN_ENGINE_FLAGS
    valued = {} if graded else RUN_ENGINE_VALUED
    what = "a graded pdflatex run" if graded else "run_engine"
    positional = []
    for a in args:
        opt = _option(a)
        if opt is None:
            positional.append(a)
            continue
        name, value = opt
        if value is None and name in flags:
            continue
        if name == "interaction" and value in _INTERACTION_MODES:
            continue
        if name in valued and value is not None and valued[name].fullmatch(value):
            continue
        raise OracleError(
            f"{what} takes no option {a!r}: the argv is an allow-list "
            f"(-interaction=MODE, {', '.join('-' + f for f in sorted(flags))}"
            + (f", {', '.join('-' + k + '=' for k in sorted(valued))}" if valued else "")
            + "); anything else could change the protocol (e.g. -cnf-line, "
              "-shell-escape, -output-directory, a format selector)")
    if len(positional) != 1:
        raise OracleError(f"{what} takes exactly one file argument, got {positional!r:.200}")
    p = positional[0]
    head = p.lstrip(" \t")
    if not head or head[0] in "-&*" or (graded and head[0] == "\\"):
        raise OracleError(f"{what}: file argument {p!r:.100} starts with -, &, * "
                          f"or \\ (an option, a format selector, INITEX's "
                          f"switch or TeX code)")
    if not graded:
        return  # run_engine's argument is TeX code (INITEX's `\\dump`)
    if _UNSAFE_ARG_CHARS.search(p):
        raise OracleError(f"{what}: file argument {p!r:.100} holds whitespace or "
                          f"a control character (web2c joins argv into TeX's "
                          f"first line, so the rest would run as TeX code)")
    if ".." in Path(p).parts:
        raise OracleError(f"{what}: file argument {p!r:.100} climbs out of the "
                          f"run directory with '..'")
    if os.path.isabs(p):
        try:
            Path(p).resolve().relative_to(Path(cwd).resolve())
        except ValueError:
            raise OracleError(f"{what}: file argument {p!r:.100} is an absolute "
                              f"path outside the run directory {cwd}")


# POSITIVE PROOF THAT pdfTeX RAN (OPEN-118 review round 2). An exit code counts
# as a grade only when the run carries evidence that pdfTeX itself produced it.
# Recognising oracle failures by their rc/stderr shape ("Error response from
# daemon", rc 125-127) was a blacklist, and it missed one realistic shape:
# MEASURED 2026-09-27 with a docker wrapper that points `docker exec` at a dead
# socket (colima restarting, the VM gone), the CLI prints "failed to connect to
# the docker API ..." and exits 1 -- which passed through as pdflatex's own rc 1
# and was graded "fails" by every Python grader. So the rule is now a whitelist:
#   * pdfTeX's banner "This is pdfTeX" must be in the run's stdout. Every
#     grader runs `-interaction=nonstopmode`, where pdfTeX prints it before it
#     reads a byte of the document, so no document can suppress it;
#   * (container) the rc is the one a shell INSIDE the container reports on a
#     per-run nonce line after pdflatex exits, not the docker client's rc. A lost
#     daemon, a dead VM or an exec that never started leave no nonce line.
# Anything else raises OracleError: unmeasured, never a grade (C-70).
# NECESSARY, NOT SUFFICIENT: see the round-3 block below (a full disk passes it).
PDFTEX_BANNER = b"This is pdfTeX"


def _require_pdftex_ran(rc: int, out: bytes, what: str) -> None:
    if PDFTEX_BANNER not in out:
        raise OracleError(
            f"{what}: exit {rc} but the run's output carries no pdfTeX banner "
            f"({PDFTEX_BANNER.decode()!r}), so pdfTeX did not run; this rc is "
            f"not a grade. Output starts: {out[:300]!r}")


# PROOF pdfTeX RAN IS NOT PROOF ITS rc IS A PROPERTY OF THE DOCUMENT (OPEN-118
# review round 3, C-75 restated). MEASURED 2026-09-27 with an 8 MB disk image as
# the work root, filled to leave 0-12 KB free, compiling a document that DOES
# compile: pdfTeX printed its banner, then failed on its OWN output ("! I can't
# write on file `t.log'." / "!pdfTeX error: pdflatex (file t.pdf): fwrite()
# failed"), exited 1 inside the container, and every Python grader graded
# FAILS; at 14 KB free the shell graders did too. So two further checks, both
# raising OracleError (unmeasured, never a grade):
#   * free space in the work directory is at least MIN_FREE_BYTES, checked
#     BEFORE and AFTER every run (`_require_free_space`);
#   * the run's output carries no failure of pdfTeX to write its OWN output
#     (`_require_output_written`): "fwrite() failed", an OS "No space left on
#     device"/"Disk quota exceeded", or "I can't write on file `<jobname>.<ext>'"
#     keyed on THIS run's job name. A document's own \openout refused under
#     openout_any=p names a different file (a parent/absolute/dot path), so it
#     is still graded.
# Neither closes the class: an environment can still alter an rc in ways no
# output shows (OOM-kill inside the VM reads as rc 137 = timeout; see OPEN-118's
# KNOWN LIMITS for the list).
MIN_FREE_MB_DEFAULT = 256
_OWN_WRITE_FAIL = re.compile(rb"fwrite\(\) failed|No space left on device|"
                             rb"Disk quota exceeded")
_CANT_WRITE = b"I can't write on file `"


def min_free_bytes() -> int:
    """The floor, in bytes. LP_ORACLE_MIN_FREE_MB overrides the default (the
    kill-tests raise it to force a refusal); it cannot be set below 1 MB."""
    raw = os.environ.get("LP_ORACLE_MIN_FREE_MB", str(MIN_FREE_MB_DEFAULT))
    try:
        mb = int(raw)
    except ValueError:
        raise OracleError(f"LP_ORACLE_MIN_FREE_MB={raw!r} is not an integer")
    return max(mb, 1) * 1024 * 1024


def _free_bytes(d: Path) -> int:
    return shutil.disk_usage(d).free


def _require_free_space(d: Path, when: str) -> None:
    try:
        free = _free_bytes(Path(d))
    except OSError as e:
        raise OracleError(f"cannot measure free space in {d} ({when} the run): {e}")
    floor = min_free_bytes()
    if free < floor:
        raise OracleError(
            f"only {free // 1024} KB free in the oracle work directory {d} "
            f"{when} the run (floor {floor // (1024 * 1024)} MB). A full disk "
            f"makes pdfTeX fail on its own output with rc 1, which reads as "
            f"'the document does not compile'; this run is not a grade.")


def jobname_of(args: list[str]) -> str | None:
    """The job name pdflatex uses for ARGS: `-jobname=X`, else the stem of the
    last non-option argument. None when it cannot be derived (a `\\input`-style
    first line)."""
    job = None
    for a in args:
        for pre in ("-jobname=", "--jobname="):
            if a.startswith(pre):
                return a[len(pre):].strip('"')
    pos = [a for a in args if not a.startswith("-") and not a.startswith("&")]
    if pos and not pos[-1].startswith("\\"):
        job = Path(pos[-1]).name
        if job.endswith(".tex"):
            job = job[:-4]
    return job or None


def _require_output_written(out: bytes, args: list[str], what: str) -> None:
    m = _OWN_WRITE_FAIL.search(out)
    if m:
        raise OracleError(
            f"{what}: pdfTeX could not write its own output "
            f"({m.group(0).decode()!r}); the work root is full or failing, so "
            f"this rc is not a property of the document")
    job = jobname_of(args)
    i = out.find(_CANT_WRITE)
    while i != -1:
        # TeX hard-wraps terminal lines at max_print_line (79); concatenation,
        # not a space, is the inverse of the wrap.
        seg = out[i + len(_CANT_WRITE):i + len(_CANT_WRITE) + 800]
        name = seg.replace(b"\n", b"").split(b"'", 1)[0].strip(b'"').decode(
            errors="replace")
        stem, dot, ext = name.rpartition(".")
        own = (stem == job and dot and ext.isalnum()) if job else (
            ext in ("log", "pdf", "aux") and "/" not in name)
        if own:
            raise OracleError(
                f"{what}: pdfTeX could not write its own file {name!r} (job "
                f"{job!r}); that is the environment, not the document")
        i = out.find(_CANT_WRITE, i + 1)


class OracleUnavailable(OracleError):
    """No pinned-image backend is reachable from this process."""


def workflow_pin() -> tuple[str, str]:
    """(TEX_IMAGE, TEX_EXPECT_VERSION) as tex-oracle.yml declares them."""
    text = WORKFLOW.read_text()
    img = re.search(r"^\s*TEX_IMAGE:\s*(\S+)\s*$", text, re.M)
    ver = re.search(r"^\s*TEX_EXPECT_VERSION:\s*(\S+)\s*$", text, re.M)
    if not img or not ver:
        raise OracleError(f"cannot read TEX_IMAGE/TEX_EXPECT_VERSION from {WORKFLOW}")
    return img.group(1), ver.group(1)


IMAGE, EXPECT_VERSION = workflow_pin()


def tree_fingerprint(texmfroot: str | None = None) -> dict:
    """Fingerprint the TeX Live tree visible to THIS process.

    tlpdb_sha256        the whole package database (architecture-specific: it
                        lists the installed binary packages).
    macro_layer_sha256  sha256 over the sorted `name revision` pairs of every
                        package that is not a per-architecture binary package
                        (`<pkg>.<arch>`) and not the installation record. Equal
                        values mean the same kernel, packages and fonts at the
                        same TeX Live revisions, whatever the CPU.
    fmt_sha256          the built pdflatex.fmt.
    """
    if texmfroot is None:
        texmfroot = subprocess.run(["kpsewhich", "-var-value", "TEXMFROOT"],
                                   capture_output=True, text=True).stdout.strip()
    tlpdb = Path(texmfroot) / "tlpkg" / "texlive.tlpdb"
    raw = tlpdb.read_bytes()
    # `<pkg>.<arch>` binary packages (e.g. `pdftex.aarch64-linux`); a plain
    # dot is NOT enough (`texlive.infra` is a macro-layer package).
    import re as _re
    arch_suffix = _re.compile(r"\.(aarch64|x86_64|amd64|i386|armhf|universal)-"
                              r"[a-z0-9]+$|\.windows$|\.win64$")
    pairs = []
    name = None
    for line in raw.decode("utf-8", "replace").split("\n"):
        if line.startswith("name "):
            name = line[5:].strip()
        elif line.startswith("revision ") and name is not None:
            if (not arch_suffix.search(name)
                    and name != "00texlive.installation"):
                pairs.append(f"{name} {line[9:].strip()}")
            name = None
    fmt = subprocess.run(["kpsewhich", "-engine=pdftex", "pdflatex.fmt"],
                         capture_output=True, text=True).stdout.strip()
    banner = subprocess.run(["pdflatex", "--version"], capture_output=True,
                            text=True).stdout.split("\n")[0].strip()
    return {
        "arch": platform.machine(),
        "texmfroot": texmfroot,
        "banner": banner,
        "tlpdb_sha256": hashlib.sha256(raw).hexdigest(),
        "macro_layer_sha256": hashlib.sha256(
            "\n".join(sorted(pairs)).encode()).hexdigest(),
        "macro_layer_packages": len(pairs),
        "fmt_sha256": (hashlib.sha256(Path(fmt).read_bytes()).hexdigest()
                       if fmt and Path(fmt).is_file() else None),
    }


def _check_search_path(k: str, v: str, inside) -> None:
    comps = v.split(":")
    if "" not in comps:
        raise OracleError(f"{k}={v!r} has no empty component, so it would replace "
                          f"the pinned image's own search path; refusing to grade")
    for c in comps:
        # kpathsea expands `~` to the container's HOME (/tmp, which persists
        # across runs in the long-lived container) and `$VAR`/`{a,b}` to
        # anything; `!!` forces an ls-R lookup in an arbitrary tree; a relative
        # `..` climbs out of the work directory into the image tree or another
        # run's directory. None can be checked against the work root, so all
        # are refused (OPEN-118 review round 2, defect 4).
        if c and (c.lstrip("!").startswith("~") or c.startswith("!!")
                  or "$" in c or "{" in c
                  or ".." in Path(c.rstrip("/") or "/").parts):
            raise OracleError(f"{k} component {c!r} uses ~, !!, $, {{}} or '..'; "
                              f"only plain paths inside the work root (or "
                              f"relative ones below the run directory) may "
                              f"shape a grade")
        if c and os.path.isabs(c) and not inside(Path(c.rstrip("/") or "/")):
            raise OracleError(f"{k} component {c!r} is outside the oracle work "
                              f"root; a host path must not shape a grade")


def _check_fingerprint(fp: dict, where: str) -> None:
    if IMAGE != FINGERPRINTED_IMAGE:
        raise OracleError(
            f"tex-oracle.yml pins {IMAGE} but the tree fingerprints in "
            f"_oracle.py were measured for {FINGERPRINTED_IMAGE}. A re-pin must "
            f"re-measure them (`_oracle.py fingerprint` inside each platform "
            f"image) in the same PR.")
    want = TREE_FINGERPRINTS.get(fp["arch"])
    if want is None:
        raise OracleError(f"{where}: no recorded fingerprint for arch {fp['arch']!r}")
    if EXPECT_VERSION not in fp["banner"]:
        raise OracleError(f"{where}: banner {fp['banner']!r} is not the pin "
                          f"{EXPECT_VERSION!r}")
    for k in ("tlpdb_sha256", "macro_layer_sha256", "fmt_sha256"):
        if fp[k] != want[k]:
            raise OracleError(
                f"{where}: {k} = {fp[k]} but the pinned image's {fp['arch']} tree "
                f"is {want[k]}. This TeX tree is NOT the oracle; refusing to grade.")


@dataclass
class OracleRun:
    rc: int            # -1 on timeout
    passes: int
    pdf: bool
    timed_out: bool

    @property
    def compiles(self) -> bool:
        return self.rc == 0 and self.pdf


class _Base:
    backend = "?"

    def __init__(self):
        self._fp = None
        # The non-TeX part of every engine run's environment (see IMAGE_ENV).
        self.engine_base = dict(IMAGE_ENV)

    # -- provenance -------------------------------------------------------
    def fingerprint(self) -> dict:
        raise NotImplementedError

    def provenance(self) -> dict:
        fp = self.fingerprint()
        return {
            "engine": "pdflatex",
            "distribution": "TeX Live 2026",
            "version": fp["banner"],
            "image": IMAGE,
            "arch": fp["arch"],
            "tlpdb_sha256": fp["tlpdb_sha256"],
            "macro_layer_sha256": fp["macro_layer_sha256"],
            "fmt_sha256": fp["fmt_sha256"],
            "backend": self.backend,
            "protocol": PROTOCOL,
        }

    @property
    def banner(self) -> str:
        return self.fingerprint()["banner"]

    # -- work directories -------------------------------------------------
    def tempdir(self, prefix: str = "lp-oracle-"):
        return tempfile.TemporaryDirectory(prefix=prefix)

    def tex_env(self, td) -> dict:
        """The recorded per-run environment: private TEXMFHOME/TEXMFVAR,
        paranoid file access, a fixed SOURCE_DATE_EPOCH (ORACLE_TEX_VARS)."""
        return oracle_tex_env(td)

    def remove(self, paths) -> None:
        """Delete files in a work directory that pdflatex will write again.
        See ContainerOracle.remove for why this must go through the oracle."""
        for p in paths:
            Path(p).unlink(missing_ok=True)

    def mkdtemp(self, prefix: str = "lp-oracle-") -> Path:
        """A work directory the oracle can run in that outlives a `with`
        block (the caller removes it). Container: under the work root."""
        return Path(tempfile.mkdtemp(prefix=prefix))

    # -- running ----------------------------------------------------------
    def run_pdflatex(self, cwd: Path, args: list[str], env: dict | None,
                     timeout: int) -> tuple[int, bytes, bool]:
        """ONE graded pdflatex run, in the protocol's environment
        (`graded_env(env)`: ORACLE_TEX_VARS imposed, `env`'s private
        TEXMFHOME/TEXMFVAR/TEXMFCONFIG required, no other TeX variable) and
        with an argv on the graded allow-list (`check_engine_argv`, C-91
        round 5). Returns (rc, combined output, timed_out)."""
        args = list(args)
        check_engine_argv(args, cwd, graded=True)
        env = graded_env(env)
        self.clear_outputs(Path(cwd), args)
        return self._exec(Path(cwd), ENGINE_PDFLATEX, args, env, timeout)

    # EACH RUN'S EVIDENCE IS ITS OWN (C-95). pdfTeX creates its PDF at the
    # first shipout, so a run with "No pages of output." leaves an EARLIER
    # run's PDF in place, and every reader of "a PDF" (compiles = rc 0 AND a
    # PDF), of the log (the first error; gen_contract's "no log = the oracle
    # failed") or of the recorder's .fls read that stale file as this run's.
    # MEASURED: an aux-oscillating document (a page on pass 1, none on the
    # confirming pass) graded compiles through run_to_fixpoint, through
    # false_ready_oracle.sh's two shim passes and gen_contract's fixpoint --
    # three copies of the pass loop, one defect. So the deletion is not in any
    # loop: it is in the ONE primitive every engine run takes (run_pdflatex,
    # which run_once/run_to_fixpoint and the shim use, and run_engine;
    # check_oracle_pin proves no tracked file starts an engine any other way).
    # The job's outputs a caller reads are removed, through the oracle, before
    # the engine starts; .aux/.toc/... stay (carrying them IS the protocol).
    RUN_OUTPUTS = (".pdf", ".log", ".fls", ".fmt")

    def clear_outputs(self, cwd: Path, args: list[str]) -> None:
        job = jobname_of(args)
        if job is None:  # INITEX's `\dump`-only argv names no file
            return
        stale = [cwd / (job + e) for e in self.RUN_OUTPUTS]
        stale = [q for q in stale if q.exists() or q.is_symlink()]
        if stale:
            self.remove(stale)

    def _exec(self, cwd: Path, engine: str, args: list[str], env: dict | None,
              timeout: int) -> tuple[int, bytes, bool]:
        raise NotImplementedError

    def run_engine(self, cwd: Path, engine: str, args: list[str], tex_vars: dict,
                   timeout: int) -> tuple[int, bytes, bool]:
        """ONE run of a TeX `engine` (one of ENGINES) with argv `args` in
        `cwd`, for a client that is not a document grader: gen_contract.py's
        pdflatex jobs and its INITEX (`pdftex -ini`) kernel jobs.

        Same guarantees as run_pdflatex -- the pinned image, a verified tree,
        the rc read inside the container, positive proof pdfTeX ran (its
        banner, which INITEX prints too), the free-space floor before and
        after, pdfTeX's own write failures refused (OracleError: not a
        result) -- with ONE difference: the environment is EXACTLY
        `tex_vars`, on both backends. No host variable shapes the run (the
        native backend keeps the host's non-TeX variables, e.g. PATH, and
        drops every `_ENV_FORWARD` one the caller did not pass), and a key
        that is not a TeX-shaping variable is refused rather than ignored.
        Start from `oracle_tex_vars(td)` and state any override explicitly.
        Returns (rc, combined output, timed_out)."""
        if engine not in ENGINES:
            raise OracleError(f"engine {engine!r} is not one of {ENGINES}")
        check_engine_argv(list(args), cwd, graded=False)
        bad = sorted(k for k in tex_vars if not _ENV_FORWARD.match(k))
        if bad:
            raise OracleError(f"run_engine: {bad} are not TeX-shaping variables "
                              f"the oracle forwards (_ENV_FORWARD)")
        self.clear_outputs(Path(cwd), list(args))
        return self._exec(Path(cwd), engine, list(args), dict(tex_vars), timeout,
                          exact_env=True)

    def image_command(self, argv: list[str], cwd: Path | None = None,
                      timeout: int = 300) -> tuple[int, bytes, bytes]:
        """Run a NON-TeX command of the pinned image (kpsewhich, sha256sum,
        cp, tar) to read the image's own files: gen_contract.py hashes the
        files a configuration read and copies the shipped format. Never a
        grade and never a TeX job (an engine is refused: use run_engine).
        Returns (rc, stdout, stderr); a caller must treat a non-zero rc as a
        failure of the oracle, never as data."""
        if not argv or Path(str(argv[0])).name in _IMAGE_SHELLS:
            raise OracleError(f"image_command runs no shell or interpreter "
                              f"({argv[:1]}): it could start a TeX engine this "
                              f"check cannot see; use run_engine")
        eng = [a for a in map(str, argv) if Path(a).name in TEX_ENGINE_BINARIES
               or a.startswith("&") or FMT_SELECTOR.match(a)]
        if eng:
            raise OracleError(f"image_command runs no TeX engine and takes no "
                              f"format selector: {eng[:3]}; use run_engine")
        return self._image_command(list(argv), cwd, timeout)

    def _image_command(self, argv, cwd, timeout):
        raise NotImplementedError

    def run_once(self, work: Path, toplevel: str, env: dict | None, timeout: int,
                 halt: bool = True) -> tuple[int, bool]:
        args = ["-interaction=nonstopmode"] + (["-halt-on-error"] if halt else []) + [toplevel]
        rc, _, to = self.run_pdflatex(Path(work), args, env, timeout)
        return (-1 if to else rc), to

    def run_to_fixpoint(self, work: Path, toplevel: str, env: dict | None,
                        timeout: int, max_passes: int = MAX_PASSES) -> OracleRun:
        """The recorded protocol; see diff_real_roots.run_to_fixpoint's
        docstring for why each step exists."""
        work = Path(work)
        pdf_path = work / (Path(toplevel).stem + ".pdf")
        # Each pass's PDF/log is its own: run_pdflatex clears them (C-95).

        def one_pass():
            return self.run_once(work, toplevel, env, timeout)

        rc, passes = -1, 0
        for _ in range(max_passes):
            rc, to = one_pass()
            passes += 1
            if to:
                return OracleRun(-1, passes, pdf_path.is_file(), True)
            if rc == 0:
                break
        if rc != 0:
            return OracleRun(rc, passes, pdf_path.is_file(), False)
        rc, to = one_pass()
        passes += 1
        if to:
            return OracleRun(-1, passes, pdf_path.is_file(), True)
        return OracleRun(rc, passes, pdf_path.is_file(), False)


class NativeOracle(_Base):
    """Only inside the pinned image. Verified, never assumed."""
    backend = "native"

    def __init__(self):
        super().__init__()
        # The same equality check on EVERY native path (get_oracle() and the
        # shell graders' `assert-native`), not only the Python one.
        got = os.environ.get("LP_ORACLE_IN_IMAGE", "")
        if got != IMAGE:
            raise OracleError(f"LP_ORACLE_IN_IMAGE={got!r} but tex-oracle.yml "
                              f"pins {IMAGE!r}")
        self.fingerprint()  # verify eagerly: a wrong tree fails at construction

    def fingerprint(self) -> dict:
        if self._fp is None:
            # In a child with the engine's environment, as the container
            # backend does: kpsewhich in THIS process would read the host's
            # TEXMFCNF/TEXMF* and could fingerprint a different tree.
            p = subprocess.run([sys.executable, "-c", _FINGERPRINT_SNIPPET],
                               env=engine_env({}, self.engine_base),
                               capture_output=True, timeout=120)
            if p.returncode != 0:
                raise OracleError("native fingerprint failed: "
                                  + p.stderr.decode(errors="replace")[:400])
            fp = json.loads(p.stdout)
            _check_fingerprint(fp, "LP_ORACLE_IN_IMAGE is set, but")
            self._fp = fp
        return self._fp

    def _exec(self, cwd, engine, args, env, timeout, exact_env=False):
        # An ALLOW-LIST, as the container backend's (see IMAGE_ENV): the
        # image's environment plus the forwarded TeX variables of `env`, and
        # nothing else of the caller's dict or the host's. graded_env and
        # run_engine have already chosen those TeX variables.
        make_private_tmp(env or {})  # C-93: checked, then created
        env = engine_env(env, self.engine_base)
        _require_free_space(cwd, "before")
        try:
            p = subprocess.run([engine, *args], cwd=cwd, env=env,
                               capture_output=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            _require_free_space(cwd, "after")
            return 124, b"", True
        except OSError as e:  # no engine at all: infrastructure, not a grade
            raise OracleError(f"cannot execute {engine}: {e}") from e
        _require_pdftex_ran(p.returncode, p.stdout, f"native {engine}")
        _require_output_written(p.stdout + p.stderr, args, f"native {engine}")
        _require_free_space(cwd, "after")
        return p.returncode, p.stdout + p.stderr, False

    def _image_command(self, argv, cwd, timeout):
        try:
            p = subprocess.run(argv, cwd=cwd, capture_output=True, timeout=timeout,
                               env=engine_env({}, self.engine_base))
        except (subprocess.TimeoutExpired, OSError) as e:
            raise OracleError(f"image command {argv[:1]} failed: {e}") from e
        return p.returncode, p.stdout, p.stderr


class HostDiagnostic(NativeOracle):
    """The host's own TeX Live, for DIAGNOSIS ONLY: attributing an
    oracle-baseline diff to the host tree (ADR-012 decision 7 asks for each
    changed cell to be classified). It is NOT the oracle: `get_oracle()` never
    returns it, it verifies nothing, and its provenance says so, so a grade it
    produces cannot be mistaken for one. Callers: oracle_baseline_classify.py."""
    backend = "host-diagnostic-NOT-THE-ORACLE"

    def __init__(self):
        _Base.__init__(self)
        # The host's TeX Live: its PATH and HOME, still no host TeX variable.
        self.engine_base.update({k: os.environ[k] for k in ("PATH", "HOME")
                                 if k in os.environ})

    def fingerprint(self) -> dict:
        if self._fp is None:
            self._fp = tree_fingerprint()
        return self._fp

    def provenance(self) -> dict:
        d = super().provenance()
        d["image"] = None
        return d


def host_diagnostic() -> HostDiagnostic:
    return HostDiagnostic()


def _docker() -> str | None:
    if os.environ.get("LP_ORACLE_DOCKER"):  # explicit override (and for tests)
        c = os.environ["LP_ORACLE_DOCKER"]
        return c if os.access(c, os.X_OK) else None
    for c in _DOCKER_CANDIDATES:
        p = shutil.which(c) or (c if os.path.isabs(c) and os.access(c, os.X_OK) else None)
        if p:
            return p
    return None


def default_workroot() -> Path:
    return Path(os.environ.get("LP_ORACLE_WORKROOT")
                or Path.home() / ".cache" / "lp-oracle" / "work")


class ContainerOracle(_Base):
    """A long-lived container of the pinned image, reached by `docker exec`."""
    backend = "container"

    def __init__(self, workroot: Path | None = None):
        super().__init__()
        self.docker = _docker()
        if self.docker is None:
            raise OracleUnavailable(
                "no docker CLI found. The oracle is the pinned TeX Live image "
                f"{IMAGE}; start it with `colima start --cpu 4 --memory 6` (or "
                "any docker) and `docker pull` the image. A local pdflatex is "
                "NOT a substitute (ADR-012 decision 7).")
        self.workroot = (workroot or default_workroot()).expanduser().resolve()
        wr = str(self.workroot)
        if "Dropbox" in wr or "CloudStorage" in wr:
            raise OracleError(f"oracle work root {wr} is inside a synced folder; "
                              "the container must never write there")
        self.workroot.mkdir(parents=True, exist_ok=True)
        self.name = ("lp-oracle-" + IMAGE.split("sha256:")[-1][:12] + "-"
                     + hashlib.sha256(wr.encode()).hexdigest()[:8])
        self._ensure_container()
        # Verify the tree EAGERLY, as NativeOracle does. Lazily (only when a
        # caller asked for provenance) meant graders that never did --
        # check_apply_fixes_roundtrip, ablate_fix_classes, regrade_sample --
        # graded in a long-lived container whose tree was never checked.
        self.fingerprint()

    def _dk(self, *args, timeout=120, check=False, input=None):
        try:
            p = subprocess.run([self.docker, *args], capture_output=True,
                               timeout=timeout, input=input)
        except subprocess.TimeoutExpired as e:
            raise OracleError(f"docker {' '.join(args[:2])} timed out") from e
        if check and p.returncode != 0:
            raise OracleError(f"docker {' '.join(args[:3])} failed rc={p.returncode}: "
                              f"{p.stderr.decode(errors='replace').strip()[:400]}")
        return p

    def _ensure_container(self):
        v = self._dk("version", "--format", "{{.Server.Version}}", timeout=30)
        if v.returncode != 0:
            raise OracleUnavailable(
                "the docker daemon is not reachable ("
                + v.stderr.decode(errors="replace").strip()[:200]
                + "). Start it (`colima start --cpu 4 --memory 6`). A local "
                  "pdflatex is NOT a substitute (ADR-012 decision 7).")
        if self._dk("image", "inspect", IMAGE, timeout=60).returncode != 0:
            raise OracleUnavailable(f"the pinned image is not present: run "
                                    f"`docker pull {IMAGE}`")
        ins = self._dk("inspect", "--format",
                       "{{.State.Running}} {{.Config.Image}} {{.HostConfig.Init}} "
                       "{{.HostConfig.PidsLimit}}", self.name)
        if ins.returncode == 0:
            running, img, init, pids = (ins.stdout.decode().split() + ["", "", ""])[:4]
            if img != IMAGE or init != "true" or pids != str(PIDS_LIMIT):
                # A container of an older oracle (no reaping PID 1, no pids
                # limit, C-97) or of another image: replaced, never graded in.
                print(f"[oracle] replacing container {self.name} (image "
                      f"{img == IMAGE}, init {init}, pids-limit {pids}): the "
                      f"oracle needs --init --pids-limit {PIDS_LIMIT} (C-97)",
                      file=sys.stderr)
                self._dk("rm", "-f", self.name)
            elif running != "true":
                self._dk("start", self.name, check=True)
        if self._dk("inspect", self.name).returncode != 0:
            p = self._dk("run", "-d", "--name", self.name,
                         "--label", "lp-oracle=1", "--init",
                         "--pids-limit", str(PIDS_LIMIT),
                         "-v", f"{self.workroot}:{self.workroot}",
                         "-e", "HOME=/tmp", "--entrypoint", "sleep",
                         IMAGE, "infinity", timeout=300)
            if p.returncode != 0 and b"already in use" not in p.stderr:
                raise OracleError("cannot start the oracle container: "
                                  + p.stderr.decode(errors="replace")[:400])
            for _ in range(50):
                ins = self._dk("inspect", "--format", "{{.State.Running}}", self.name)
                if ins.stdout.strip() == b"true":
                    break
                time.sleep(0.2)
        ins = self._dk("inspect", "--format", "{{.HostConfig.Init}} "
                       "{{.HostConfig.PidsLimit}}", self.name)
        if ins.stdout.decode().split() != ["true", str(PIDS_LIMIT)]:
            raise OracleError(
                f"container {self.name} runs without --init/--pids-limit "
                f"{PIDS_LIMIT} ({ins.stdout.decode().strip()!r}): its PID 1 would "
                f"reap nothing, and leaked processes can make a \\write18 fork "
                f"fail silently, i.e. change a grade (C-97). `_oracle.py stop`.")
        # Positive proof the work root is the SAME directory inside: a nonce
        # written on the host must be read back through the container.
        nonce = uuid.uuid4().hex
        probe = self.workroot / f".mount-probe-{os.getpid()}-{nonce[:8]}"
        probe.write_text(nonce)
        try:
            got = self._dk("exec", self.name, "cat", str(probe), timeout=60)
        finally:
            probe.unlink(missing_ok=True)
        if got.stdout.decode().strip() != nonce:
            raise OracleError(
                f"the work root {self.workroot} is not visible inside the "
                f"container (colima mounts only $HOME by default). Choose a "
                f"work root under $HOME via LP_ORACLE_WORKROOT.")

    def fingerprint(self) -> dict:
        if self._fp is None:
            p = self._dk("exec", self.name, "python3", "-c",
                         _FINGERPRINT_SNIPPET, timeout=120, check=True)
            fp = json.loads(p.stdout)
            _check_fingerprint(fp, f"container {self.name}")
            e = self._dk("exec", self.name, "env", "-0", timeout=60, check=True)
            check_container_env(dict(x.split("=", 1) for x in
                                     e.stdout.decode(errors="replace").split("\0")
                                     if "=" in x), f"container {self.name}")
            self.check_texmf_trees()
            self._fp = fp
        return self._fp

    # THE LONG-LIVED CONTAINER MUST STILL BE THE IMAGE (C-91, review round 5).
    # The base image is pinned by digest; a live container is not, and every
    # grade of every grader runs in the same one for days. The round-5 review
    # MEASURED a .sty planted in its /tmp/.texlive2026/texmf-config flipping a
    # later CLEAN graded run (rc 1 -> rc 0) while `_oracle.py info` still
    # passed: the fingerprint hashes the tlpdb and the format, not the trees
    # kpathsea searches. Graded runs now search a private TEXMFHOME/TEXMFVAR/
    # TEXMFCONFIG only (private_texmf_vars), and two checks refuse a container
    # that has changed:
    #   * check_texmf_trees, on EVERY construction (the shim's too): the
    #     container's own default TEXMFHOME/TEXMFVAR/TEXMFCONFIG (as its
    #     kpsewhich reports them) hold no file. Cheap (one exec).
    #   * check_state, once per grading SESSION (get_oracle() for the Python
    #     graders, `_oracle.py version`/`info` for the shell graders and a
    #     user): no path of the container's root filesystem has a ctime
    #     after the container was created, other than STATE_ALLOWED. ctime,
    #     not mtime: a writer can set mtime back (touch -d), not ctime. About
    #     6 s under load (a full `find / -xdev`), MEASURED; `docker diff` took
    #     13-16 s, too slow even per session.
    # RESIDUAL (OPEN-118 (h)): a change made AFTER the session's check, by
    # something other than a graded run (a `docker exec` of one's own), is
    # seen by the next session only.
    STATE_ALLOWED = frozenset((
        "/", "/etc", "/sys", "/proc", "/dev", "/tmp", "/var", "/var/cache",
        "/var/cache/fontconfig", "/tmp/.texlive2026", "/.dockerenv",
        "/etc/resolv.conf", "/etc/hostname", "/etc/hosts", "/etc/mtab"))
    # fontconfig's caches (pdfTeX does not read them; written once, 682 files
    # at 06:53:53 on 2026-09-27, 14 min after this container was created).
    # `docker run --init` bind-mounts docker-init at /sbin/docker-init (=
    # /usr/sbin on this merged-/usr image) about 0.35 s after Created, which
    # touches these two DIRECTORIES' ctime. MEASURED 2026-09-29 in a fresh
    # --init container: nothing else changes; the file itself is another
    # filesystem (-xdev). Their contents are NOT allowed.
    STATE_ALLOWED_DIRS = frozenset(("/usr", "/usr/sbin"))
    _STATE_ALLOWED_RX = re.compile(
        r"^/var/cache/fontconfig/([0-9a-f]{32}-le64\.cache-\d+|CACHEDIR\.TAG)$")
    _TEXMF_TREES_SH = (
        'for v in TEXMFHOME TEXMFVAR TEXMFCONFIG; do '
        'd=$(kpsewhich -var-value="$v") && [ -n "$d" ] || exit 3; '
        'echo "D $d"; if [ -e "$d" ]; then find "$d" ! -type d -print; fi; '
        'done')

    def check_texmf_trees(self) -> None:
        p = self._dk("exec", "-e", "HOME=/tmp", self.name, "sh", "-c",
                     self._TEXMF_TREES_SH, timeout=60)
        out = p.stdout.decode(errors="replace").splitlines()
        trees = [x[2:] for x in out if x.startswith("D ")]
        files = [x for x in out if x and not x.startswith("D ")]
        if p.returncode != 0 or len(trees) != 3:
            raise OracleError(f"container {self.name}: cannot list its default "
                              f"TEXMFHOME/TEXMFVAR/TEXMFCONFIG (rc {p.returncode}: "
                              f"{p.stderr.decode(errors='replace')[:200]})")
        if files:
            raise OracleError(
                f"container {self.name}: its persistent TeX trees {trees} hold "
                f"{len(files)} file(s), e.g. {files[:5]}. kpathsea would search "
                f"them for any run without private trees, and something wrote "
                f"them; refusing to grade. Inspect them, then `_oracle.py stop`.")

    def check_state(self) -> None:
        ins = self._dk("inspect", "--format", "{{.Created}}", self.name,
                       timeout=60, check=True)
        created = ins.stdout.decode().strip()
        import datetime
        try:
            t = int(datetime.datetime.strptime(created[:19], "%Y-%m-%dT%H:%M:%S")
                    .replace(tzinfo=datetime.timezone.utc).timestamp())
        except ValueError:
            raise OracleError(f"container {self.name}: unreadable Created {created!r}")
        p = self._dk("exec", self.name, "find", "/", "-xdev", "-newerct", f"@{t}",
                     "-printf", "%y %p\n", timeout=600)
        if p.returncode != 0:
            raise OracleError(f"container {self.name}: the state scan failed "
                              f"(rc {p.returncode}): "
                              f"{p.stderr.decode(errors='replace')[:300]}")
        allowed = set(self.STATE_ALLOWED)
        for a in [self.workroot, *self.workroot.parents]:
            allowed.add(str(a))
        bad = []
        for line in p.stdout.decode(errors="replace").splitlines():
            typ, _, path = line.partition(" ")
            if path in allowed or self._STATE_ALLOWED_RX.match(path):
                continue
            if typ == "d" and path in self.STATE_ALLOWED_DIRS:
                continue
            if typ == "d" and path.startswith("/tmp/.texlive2026/"):
                continue  # an empty tree's directories; files: check_texmf_trees
            bad.append(path)
        if bad:
            # WHEN each changed (its ctime), so the run that left it can be
            # found in a grader's log: a graded run's temporary files live in
            # its own work directory since C-93, so a /tmp/gs_* or
            # /tmp/mt*.tmp here was left by a run killed mid-conversion under
            # an older oracle, or by an exec outside the protocol.
            st = self._dk("exec", self.name, "stat", "--format=%z %n", "--",
                          *bad[:6], timeout=60)
            when = st.stdout.decode(errors="replace").strip().splitlines()
            raise OracleError(
                f"container {self.name}: {len(bad)} path(s) changed since it was "
                f"created ({created}), e.g. {bad[:6]}"
                + (f" (ctime: {'; '.join(when)})" if when else "")
                + f". The container is no longer the pinned image; refusing to "
                f"grade. Inspect them (`docker exec {self.name} ls -la "
                f"--time-style=full-iso PATH`), then `_oracle.py stop` so the "
                f"oracle starts a clean one. A graded run keeps its temporary "
                f"files in its own work directory (TMPDIR, C-93): a leftover "
                f"/tmp/gs_* (Ghostscript under repstopdf) or /tmp/mt*.tmp "
                f"(mktex*) comes from a run killed mid-conversion by an older "
                f"oracle or from something outside the protocol.")

    def tempdir(self, prefix: str = "lp-oracle-"):
        return tempfile.TemporaryDirectory(prefix=prefix, dir=self.workroot)

    def _inside(self, p: Path) -> bool:
        try:
            Path(p).resolve().relative_to(self.workroot)
            return True
        except ValueError:
            return False

    def remove(self, paths) -> None:
        """Delete files INSIDE the container, then on the host.

        MEASURED 2026-09-27 (colima 'default', docker runtime, virtiofs): a file
        the container created and the HOST then deleted cannot be re-created
        by the container for about a second -- `echo two > f.log` fails with
        "Directory nonexistent" -- because the guest's dentry cache is stale.
        pdflatex then cannot open its log, exits 1 and leaves no log.
        false_ready_oracle.sh deletes the halt run's .pdf/.log between its two
        protocols, so it hit this on most fixtures (57 of 85 "no pdfTeX log
        produced", reproduced with the pre-fix script too). A deletion made
        through the container keeps the guest cache coherent (measured)."""
        paths = [Path(p).resolve() for p in paths]
        outside = [str(p) for p in paths if not self._inside(p)]
        if outside:
            raise OracleError(f"refusing to delete outside the work root: {outside[:3]}")
        for i in range(0, len(paths), 200):
            self._dk("exec", self.name, "rm", "-f", "--",
                     *[str(p) for p in paths[i:i + 200]], check=True)
        for p in paths:
            p.unlink(missing_ok=True)

    def mkdtemp(self, prefix: str = "lp-oracle-") -> Path:
        return Path(tempfile.mkdtemp(prefix=prefix, dir=self.workroot))

    def _image_command(self, argv, cwd, timeout):
        cmd = ["exec", "-e", "HOME=/tmp"]
        if cwd is not None:
            if not self._inside(Path(cwd)):
                raise OracleError(f"{cwd} is outside the oracle work root")
            cmd += ["-w", str(Path(cwd).resolve())]
        try:
            p = subprocess.run([self.docker, *cmd, self.name, *argv],
                               capture_output=True, timeout=timeout)
        except subprocess.TimeoutExpired as e:
            raise OracleError(f"image command {argv[:1]} timed out") from e
        return p.returncode, p.stdout, p.stderr

    def _exec(self, cwd, engine, args, env, timeout, exact_env=False):
        # exact_env (run_engine) needs nothing more here: only _ENV_FORWARD
        # variables ever cross into the container, and run_engine passes no
        # others.
        cwd = Path(cwd).resolve()
        if not self._inside(cwd):
            raise OracleError(
                f"{cwd} is outside the oracle work root {self.workroot}, so the "
                f"container cannot see it. Create work directories with "
                f"oracle.tempdir().")
        # C-93: the run's private TMPDIR, checked (one plain absolute path
        # inside the work root, TMP/TEMP/JAVA_TOOL_OPTIONS derived from it)
        # and created on the host, where the container sees it.
        make_private_tmp(env or {}, self._inside)
        _require_free_space(cwd, "before")
        cmd = ["exec", "-w", str(cwd), "-e", "HOME=/tmp"]
        for k, v in sorted((env or {}).items()):
            if _ENV_FORWARD.match(k):
                if k.startswith("TEXMF") and (
                        not os.path.isabs(v) or any(ch in v for ch in "~$!{:,")
                        or not self._inside(Path(v))):
                    # Absolute, a single plain path, inside the work root:
                    # kpathsea would expand ~ (the container's persistent
                    # HOME), $VAR, {a,b} and !! itself.
                    raise OracleError(f"{k}={v} is not one plain absolute path "
                                      f"inside the oracle work root")
                if k in _SEARCH_PATHS:
                    _check_search_path(k, v, self._inside)
                cmd += ["-e", f"{k}={v}"]
        # The timeout runs INSIDE the container: killing the docker client on
        # the host would leave pdflatex running in the container. A shell
        # inside the container reports pdflatex's rc on a line tagged with a
        # per-run nonce; that line, not the docker CLI's exit code, is the rc
        # (see PDFTEX_BANNER above for why).
        nonce = "LP_ORACLE_RC_" + uuid.uuid4().hex
        script = LEAK_CHECK_SH + (
            'n=$1; t=$2; e=$3; shift 3; lp_leak "$n" || exit 0; '
            'timeout -k 10 "$t" "$e" "$@"; '
            'rc=$?; printf "\\n%s=%d\\n" "$n" "$rc" >&2')
        cmd += [self.name, "sh", "-c", script, "sh", nonce, str(int(timeout)), engine,
                *args]
        try:
            p = subprocess.run([self.docker, *cmd], capture_output=True,
                               timeout=timeout + 90)
        except subprocess.TimeoutExpired:
            # The docker client hung past the inner timeout's own kill: the
            # oracle did not answer. Unmeasured, not a pdflatex timeout.
            raise OracleError(f"docker exec did not return within {timeout + 90}s")
        leak = re.search(rb"^" + nonce.encode() + rb"_LEAK=(.*)$", p.stderr, re.M)
        if leak is not None:
            raise OracleError(
                f"container {self.name}: processes left by earlier runs "
                f"({leak.group(1).decode(errors='replace')[:300]}); a leak can "
                f"make a \\write18 fork fail silently and change a grade, so "
                f"no run starts (C-97). Inspect (`docker exec {self.name} ps "
                f"-ef`), then `_oracle.py stop`.")
        m = re.search(rb"^" + nonce.encode() + rb"=(\d+)$", p.stderr, re.M)
        if m is None:
            raise OracleError(
                f"docker exec exited {p.returncode} without the in-container rc "
                f"line, so pdflatex's exit status is unknown (daemon lost, VM "
                f"gone, or exec never started); this is not a grade: "
                + p.stderr.decode(errors="replace").strip()[:400])
        rc = int(m.group(1))
        err = p.stderr[:m.start()] + p.stderr[m.end():]
        if rc in (124, 137):
            _require_free_space(cwd, "after")
            return rc, p.stdout + err, True
        if rc in (125, 126, 127):  # timeout(1) itself failed / engine missing
            raise OracleError(f"in-container timeout/{engine} failed rc={rc}: "
                              + err.decode(errors="replace")[:400])
        _require_pdftex_ran(rc, p.stdout, f"container {self.name}")
        _require_output_written(p.stdout + err, args, f"container {self.name}")
        _require_free_space(cwd, "after")
        return rc, p.stdout + err, False

    def stop(self):
        self._dk("rm", "-f", self.name)


def _fingerprint_source() -> str:
    """The fingerprint function's own source, run inside the container, so the
    container and native paths cannot compute different things."""
    import inspect
    return ("import hashlib, json, platform, subprocess\nfrom pathlib import Path\n"
            + inspect.getsource(tree_fingerprint)
            + "\nprint(json.dumps(tree_fingerprint()))\n")


_FINGERPRINT_SNIPPET = _fingerprint_source()

_ORACLE = None
_STATE_CHECKED = False


def in_image() -> bool:
    return bool(os.environ.get("LP_ORACLE_IN_IMAGE"))


def get_oracle(full_state: bool = True) -> _Base:
    """The oracle for this process. Raises OracleUnavailable/OracleError; never
    returns a host-pdflatex backend. `full_state` (the default: a grading
    session) also runs the container's full state scan once per process
    (ContainerOracle.check_state); the per-run shim passes False and relies on
    the session's scan plus the per-construction check_texmf_trees."""
    global _ORACLE, _STATE_CHECKED
    if _ORACLE is None:
        if in_image():
            if os.environ["LP_ORACLE_IN_IMAGE"] != IMAGE:
                raise OracleError(f"LP_ORACLE_IN_IMAGE={os.environ['LP_ORACLE_IN_IMAGE']!r} "
                                  f"but tex-oracle.yml pins {IMAGE!r}")
            _ORACLE = NativeOracle()
        else:
            _ORACLE = ContainerOracle()
    if full_state and not _STATE_CHECKED and isinstance(_ORACLE, ContainerOracle):
        _ORACLE.check_state()
        _STATE_CHECKED = True
    return _ORACLE


def availability() -> tuple[bool, str]:
    """(available, reason) without raising: for callers that may legitimately
    SKIP in an environment with no TeX at all (CI's pure jobs)."""
    try:
        get_oracle()
        return True, "ok"
    except OracleError as e:
        return False, str(e)


def host_has_pdflatex() -> bool:
    return shutil.which("pdflatex") is not None


def first_error_block(log: Path, lines: int = 4) -> str:
    """The first `!` line of a pdflatex log joined with its wrapped
    continuation (TeX hard-wraps at ~79 columns; concatenation, not a space,
    is the inverse of the wrap)."""
    if not Path(log).is_file():
        return ""
    ll = Path(log).read_text(errors="replace").split("\n")
    for i, line in enumerate(ll):
        if line.startswith("!"):
            return "".join(ll[i:i + lines])
    return ""


def main(argv: list[str]) -> int:
    if not argv:
        print(__doc__)
        return 2
    cmd, rest = argv[0], argv[1:]
    try:
        if cmd == "fingerprint":
            print(json.dumps(tree_fingerprint(), indent=1))
            return 0
        if cmd == "assert-native":
            NativeOracle()  # checks LP_ORACLE_IN_IMAGE == IMAGE, then the tree
            print(f"[oracle] native backend verified: {IMAGE}")
            return 0
        if cmd == "vet":
            # The shell graders' form of the checks run_pdflatex applies:
            #   vet --dir D                          free space only (BEFORE)
            #   vet --dir D --output F -- ARGS...    free space AND F (the run's
            #                                        stdout) for pdfTeX failing
            #                                        to write its own output
            # Exit 0 = gradeable; INFRA_RC = not a grade (message on stderr).
            args = rest[rest.index("--") + 1:] if "--" in rest else []
            opts = rest[:rest.index("--")] if "--" in rest else rest
            d = Path(opts[opts.index("--dir") + 1])
            outf = (Path(opts[opts.index("--output") + 1])
                    if "--output" in opts else None)
            try:
                if outf is not None:
                    _require_output_written(outf.read_bytes(), args, f"vet {d}")
                _require_free_space(d, "after" if outf is not None else "before")
            except (OracleError, OSError, ValueError) as e:
                print(f"[oracle] NOT GRADED: {e}", file=sys.stderr)
                return INFRA_RC
            return 0
        if cmd == "workroot":
            print(default_workroot().expanduser().resolve())
            return 0
        if cmd == "stop":
            ContainerOracle().stop()
            return 0
        # The per-run commands (the shim, rm) skip the full state scan; the
        # session commands (`version`, which oracle_setup runs once per shell
        # grader, and `info`) run it.
        o = get_oracle(full_state=cmd not in (SHIM_COMMAND, "rm"))
        if cmd == "info":
            print(json.dumps(o.provenance(), indent=1))
            return 0
        if cmd == "version":
            print(o.banner)
            return 0
        if cmd == "rm":
            o.remove([Path.cwd() / a for a in rest])
            return 0
        if cmd == SHIM_COMMAND:
            timeout = 120
            if rest[:1] == ["--timeout"]:
                timeout, rest = int(rest[1]), rest[2:]
            # The shell graders' runs get EXACTLY the Python graders'
            # environment (C-91): a private TEXMFHOME/TEXMFVAR/TEXMFCONFIG
            # per run (else the container's defaults under /tmp/.texlive2026
            # with HOME=/tmp would carry state such as mktexpk fonts, or a
            # planted .sty, from one run and one grader to the next) and
            # ORACLE_TEX_VARS. Host values of any TeX-shaping variable are
            # overridden or dropped, never forwarded (run_pdflatex applies
            # graded_env); say which. The ARGV is run_pdflatex's allow-list
            # (check_engine_argv, round 5): an override refuses (INFRA_RC).
            dropped = host_tex_overrides()
            if dropped:
                print(f"[oracle] note: the graded run does not inherit the "
                      f"host's {', '.join(dropped)} (protocol: "
                      f"{ORACLE_TEX_VARS})", file=sys.stderr)
            with o.tempdir(prefix="lp-oracle-shim-") as td:
                rc, out, to = o.run_pdflatex(Path.cwd(), rest, o.tex_env(td), timeout)
            sys.stdout.buffer.write(out)
            return 124 if to else rc
    except BaseException as e:  # noqa: BLE001 -- every exception, see below
        if isinstance(e, SystemExit) and e.code in (0, None):
            raise
        print(f"[oracle] FATAL: {type(e).__name__}: {e}", file=sys.stderr)
        # The pdflatex shim must not exit with a code a pdflatex failure could
        # have produced: the shell graders would grade it (see INFRA_RC). That
        # holds for EVERY exception, not only OracleError: an uncaught
        # ValueError/KeyboardInterrupt used to exit 1, i.e. "pdflatex failed".
        return INFRA_RC if cmd == SHIM_COMMAND else 2
    print(f"[oracle] unknown command {cmd!r}", file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
