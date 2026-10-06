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
* ONE LAUNCH DEFINITION (ADR-015 E15, owner 2026-10-06; OPEN-128 (4)). Every
  engine run, locally and in CI, is a FRESH container of the pinned image
  started by `ContainerOracle.launch_argv` and nothing else: `docker run --rm
  --init --read-only --tmpfs /tmp --network none --hostname lp-oracle
  --memory ... --user <uid:gid> --platform linux/<arch>`, the run directory
  bind-mounted at the fixed path RUN_DIR (/lp/run). CI runs the same Python
  graders on its arm64 runner host, which has docker; it no longer starts the
  image itself to grade inside it (check_oracle_pin refuses a workflow step
  that does). The claim is ONE CONFIGURATION BY CONSTRUCTION, not one
  platform: what still differs between a laptop's VM and the CI runner (the
  work root's file system, the kernel, CPU speed against the timeout) is
  enumerated and measured in OPEN-128 (8),
  corpora/oracle_baseline/platform_residuals.json.
  The native backend (grading inside the image, selected by
  LP_ORACLE_IN_IMAGE) is RETIRED: `get_oracle()` refuses that variable, and
  NativeOracle survives only as the base of HostDiagnostic, which grades
  nothing. If docker or the image is unavailable the oracle raises
  `OracleUnavailable`. There is no path on which a laptop pdflatex grades
  anything.
* EVERY RUN-DEPENDENT INPUT IS FIXED (ADR-015 E10; OPEN-128 (1)-(3); the
  census is corpora/oracle_baseline/clock_census.json). A graded run sees:
  the CLOCK fixed at PROTOCOL_EPOCH (SOURCE_DATE_EPOCH + FORCE_SOURCE_DATE
  for \\year/\\month/\\day/\\time and the PDF dates, and the LD_PRELOAD shim
  scripts/tools/oracle_shim/lpshim.c for gettimeofday -- \\pdfrandomseed,
  \\pdfelapsedtime -- time(2), clock_gettime(REALTIME) and every file time
  -- \\pdffilemoddate); the same PATHS (its directory at /lp/run, its private
  TeX trees and TMPDIR on a fresh tmpfs at /tmp/lp); the same host name, no
  network, a fresh pid namespace; an environment that is an exact
  allow-list; and, for every TeX Live program, a FILE-SYSTEM VIEW limited to
  the run directory, the fresh /tmp and the TeX tree (the shim refuses
  /proc, /sys, /dev and docker's per-container files, which a document read
  before: /proc/uptime is the real clock). The clock is part of the
  oracle's identity (IDENTITY_KEYS).
* THE MEASUREMENT ENTRY POINT (ADR-015 E7; `measure`, `_oracle.py measure`):
  terminal input, an explicit architecture and an explicit clock (the
  spike's gettimeofday readings, or a fixed epoch), through the same launch
  definition, pin, argv and environment discipline. Its result is never a
  grade: its provenance says `"entry": "measure"`, a run on an architecture
  other than ARCH_OF_RECORD is tagged `measurement_only`, and every grading
  and carry-forward path (require_same_oracle, check_oracle_pin) refuses
  both.
* The digest pins an INDEX, not an image: it names one arm64 and one amd64
  image. The project grades on arm64 only (ADR-015 E2/E9): CI's tex-oracle
  job runs on GitHub's native arm64 runner and a Mac grades on arm64. The
  amd64 image's fingerprints stay recorded for measurement (E3) only.
  Their TeX trees are compared by `macro_layer_sha256` (every non-binary
  TeX Live package with its revision), recorded below for both
  architectures; `tlpdb_sha256` differs by construction because the tlpdb
  lists the architecture's binary packages.
* Every artefact records `provenance()`: image, architecture, banner, the tree
  fingerprints, the backend and the clock. `check_oracle_pin.py` refuses a
  graded artefact whose recorded image is not the workflow's.

THE PROTOCOL (unchanged from the recorded one; STRICT_TIER_DESIGN.md §B.4).

`pdflatex -interaction=nonstopmode -halt-on-error <toplevel>`, the stock
restricted shell-escape (no `-shell-escape`, no `-no-shell-escape`, OPEN-053;
since review round 5 the graded argv is an allow-list, `check_engine_argv`),
up to 3 passes: run to the first rc 0, then ONE confirming pass whose rc is
authoritative (the `fr_toc_second_pass` lesson). The result also records
whether a PDF was produced; `compiles` requires rc 0 AND a PDF (§B.4 E0).

Usage as a tool:
  _oracle.py info                 print the oracle's provenance (starts one
                                  probe container)
  _oracle.py fingerprint          fingerprint the TeX tree this process sees
  _oracle.py workroot             print the work root (for shell callers)
  _oracle.py pdflatex [--timeout S] ARGS...
                                  run ONE pdflatex in the current directory
                                  through the oracle; exit with its rc (124 on
                                  timeout, INFRA_RC=125 when the oracle itself
                                  failed). The shim the shell graders use; its
                                  run gets the protocol's environment
                                  (graded_env), never the host's.
  _oracle.py measure [OPTIONS] --work DIR -- ENGINE ARGS...
                                  the measurement entry point (ADR-015 E7); see
                                  measure_main. Never a grade.
  _oracle.py grading-code FILE... print the grading_code block (the git blob
                                  ids of _oracle.py and FILE...) as JSON, for
                                  a shell producer to record (OPEN-128 (8))
  _oracle.py vet --dir D [--output F -- ARGS...]
                                  shell graders: refuse (INFRA_RC) a run when
                                  D is short of space or F shows pdfTeX failing
                                  to write its own output; exit 0 otherwise
  _oracle.py check-recorded FILE KEY
                                  exit 0 iff the oracle block at KEY (dotted)
                                  of the JSON FILE is this oracle: same image,
                                  architecture, tree and clock (ADR-015 E2,
                                  E10); else INFRA_RC. The shell graders'
                                  comparison guard
  _oracle.py rm FILES...          delete work files through the oracle (see
                                  ContainerOracle.remove); exit 0, or 2
  _oracle.py stop                 remove leftover run containers of this
                                  oracle (label lp-oracle-run)
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

# EVERY RUN IS A FRESH CONTAINER (OPEN-128 (1), (4); ADR-015 E15). Until
# OPEN-128 every engine run was a `docker exec` into ONE long-lived container
# per work root, and that design could not fix the run-dependent inputs: the
# run directory was a random temporary path under the work root, which a
# document reads back (`l3sys-query pwd`, `kpsewhich -var-value=TMPDIR` in
# restricted \write18, the absolute paths of a .synctex), the container's
# pids grew from run to run, its /tmp and process table were shared by every
# run (C-97's zombies, C-93's /tmp/gs_*, C-91's planted .sty, each guarded
# after the fact by check_state, check_texmf_trees and a per-run leak scan).
# Now `ContainerOracle.launch_argv` starts a FRESH container per run: the run
# directory is mounted at the fixed RUN_DIR, the private TeX trees and TMPDIR
# live on the run's own fresh tmpfs at fixed paths (FIXED_RUN_VARS), its pid
# namespace, /tmp and process table are its own and die with it (`--rm`), and
# the image's root file system is read-only. MEASURED 2026-10-06 on colima:
# `docker run --rm` of the pinned image costs 0.14-0.19 s, `docker exec`
# 0.04-0.05 s, per pass. The guards of the shared container are therefore
# gone, not weakened: nothing outlives a run to be scanned.
# `--init` (PID 1 = docker-init, which reaps) and the pids limit stay: one
# runaway \write18 job cannot exhaust the VM that every run shares (C-97).
PIDS_LIMIT = 4096
# THE FIXED LAYOUT OF A RUN (OPEN-128 (1)). The run directory (the grader's
# work directory, bind-mounted read-write), the oracle's LD_PRELOAD shim
# (read-only), a measurement's terminal input (read-only).
RUN_DIR = "/lp/run"
SHIM_DIR = "/lp/shim"
IN_DIR = "/lp/in"
# The run's private trees, TMPDIR and the shim's bookkeeping, on the run's
# own tmpfs /tmp (fresh per run, so no state crosses from one run to the
# next: C-91, C-93).
PRIVATE_ROOT = "/tmp/lp"
SHIM_MARK_DIR = PRIVATE_ROOT + "/.shim"
FS_LOG = PRIVATE_ROOT + "/.fs-denied"
CLOCK_LOG = PRIVATE_ROOT + "/.clock"
# The container's host name (docker writes it to /etc/hostname, which the
# shim refuses to TeX programs, and children may still ask the kernel).
ORACLE_HOSTNAME = "lp-oracle"
# A memory ceiling equal on every platform (OPEN-128 (8)): the laptop's VM
# and the CI runner have different memory, so without it a run that
# exhausts memory could be killed on one and not on the other. A kill reads
# as rc 137, a timeout: never a grade.
MEMORY_LIMIT = "2g"
# The architectures the pinned index holds, as docker names them.
PLATFORMS = {"aarch64": "linux/arm64", "x86_64": "linux/amd64"}

# THE TeX TREE IS READ-ONLY, AND NO RUN IS ROOT (OPEN-126; stock-take
# 2026-09-30 §3f). Spike H.1 SAW a crashed mktex helper write into
# texmf-dist and rewrite its ls-R inside a live oracle container that ran as
# root over a writable image filesystem. Every run's container is started
# with `--read-only` (its root filesystem, the TeX tree included, cannot be
# written), `--tmpfs /tmp:TMPFS_OPTIONS` (HOME=/tmp; the run's private trees
# and TMPDIR live there), and `--user` = the host user, so the engine is not
# root either (the bind-mounted run directory stays writable to it: on
# colima's virtiofs a container uid equal to the host's owns the host's
# files). The session probe (ContainerOracle.session_probe) VERIFIES it in a
# container started by the same launch definition (check_readonly): a
# writable TeX tree or a root engine is refused, never graded.
# CORRECTION (C-121, OPEN-128 (5)): this block used to say that CI's
# in-image runs were "started the same way" -- they were not (tex-oracle.yml
# mounted /tmp as rw,nosuid,nodev,size=4g, without noexec) -- and that the
# read-only container was "MEASURED before adoption" -- it was measured
# AFTER fde1bf2b adopted it (OPEN-126 (c)). Since OPEN-128 there is one launch
# definition, so CI's runs ARE started the same way, by construction.
TMPFS_OPTIONS = "rw,nosuid,nodev,noexec,size=256m"
_READONLY_PROBE = (
    "import json, os, subprocess\n"
    "r = subprocess.run(['kpsewhich', '-var-value', 'TEXMFROOT'], "
    "capture_output=True, text=True).stdout.strip()\n"
    "def ro(p):\n"
    "    try:\n"
    "        return bool(os.statvfs(p).f_flag & os.ST_RDONLY)\n"
    "    except OSError:\n"
    "        return None\n"
    "print(json.dumps({'euid': os.geteuid(), 'texmfroot': r, "
    "'root_ro': ro('/'), 'tree_ro': ro(r) if r else None}))\n")


def check_readonly(probe: dict, where: str) -> None:
    """Refuse (OracleError) an oracle whose TeX tree is writable or whose
    engine would run as root (see the block above)."""
    if probe.get("tree_ro") is not True or probe.get("root_ro") is not True:
        raise OracleError(
            f"{where}: the TeX tree ({probe.get('texmfroot')!r}) or the root "
            f"filesystem is writable (read-only: tree {probe.get('tree_ro')}, "
            f"root {probe.get('root_ro')}); the oracle's tree must be "
            f"read-only (docker run --read-only, OPEN-126).")
    if probe.get("euid") in (0, None):
        raise OracleError(
            f"{where}: the engine would run as root (euid {probe.get('euid')}); "
            f"the oracle runs as an unprivileged user (--user, OPEN-126)")


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
# THE ARCHITECTURE IS PART OF THE ORACLE'S IDENTITY (ADR-015 decision E2,
# C-103, OPEN-126). The digest above names an INDEX of two images, and the
# pinned pdfTeX gives DIFFERENT VERDICTS on them for some documents: C-103
# MEASURED `\pdfsnapy 0pt` exiting 0 on aarch64 and 136 (SIGFPE) on x86_64, a
# valid 40000x8 px JPEG with no resolution rc 1 vs rc 0, and `\divide` of
# INT_MIN by INT_MIN -1 vs 1 -- C constructs the two ISAs and compilers
# resolve differently. So a grade is a grade FOR ONE ARCHITECTURE, and the
# owner decided (E2) that graders must not compare grades across
# architectures. The project grades on ONE: ARCH_OF_RECORD. Every published
# artefact was graded on it (check_oracle_pin.py refuses one that was not),
# and the oracle refuses to grade on any other (_check_fingerprint), so a
# live grade and a recorded one are of the same architecture by
# construction; the comparers check it again on the recorded side
# (require_same_oracle). CI's tex-oracle job runs on a native arm64 runner
# for the same reason. The x86_64 fingerprints stay recorded: they are
# measured facts about the pinned index (the macro layers agree), and the
# native-amd64 confirmation of E3 needs them; they do not make x86_64 an
# oracle.
ARCH_OF_RECORD = "aarch64"
# fmt_sha256 is per-architecture (a dumped format is a memory image), MEASURED
# 2026-09-27 as `sha256sum $(kpsewhich -engine=pdftex pdflatex.fmt)` in
# `docker run --platform linux/{arm64,amd64}` of the pinned digest. It is
# compared so that a container mutated by an `fmtutil`/`tlmgr` run inside it
# cannot keep grading: the base image is pinned by digest, a live container is
# not.

# The environment variables an engine run may receive (on top of the image's
# own, IMAGE_ENV). Nothing else from the host or the caller crosses: in
# particular not PATH, HOME or any TEXMF* tree pointing at the host's TeX
# Live. The oracle sets every one of them itself (FIXED_RUN_VARS, the clock,
# ORACLE_TEX_VARS); a caller may add only RUN_ENGINE_OVERRIDES (run_engine)
# or MEASURE_ENV (measure).
_ENV_FORWARD = re.compile(
    r"^(TEXMFHOME|TEXMFVAR|TEXMFCONFIG|openin_any|openout_any|"
    r"SOURCE_DATE_EPOCH|FORCE_SOURCE_DATE|max_print_line|error_line|"
    r"half_error_line|TMPDIR|TMP|TEMP|JAVA_TOOL_OPTIONS|PYTHONHASHSEED|"
    r"PERL_HASH_SEED|PERL_PERTURB_KEYS|LP_CLOCK_EPOCH|LP_CLOCK|LP_CLOCK_LOG|"
    r"LP_FS_ROOTS|LP_FS_EXE|LP_FS_LOG|LP_SHIM_MARK)$")

# THE ORACLE'S TeX ENVIRONMENT: the ONE definition. Every grader (through
# `graded_env`) and the contract generator (gen_contract.py, through
# `run_engine`) get it from here; nobody restates it.
# check_gen_contract_parsers.py asserts that no other tool restates it.
#   openin_any/openout_any=p   paranoid file access (no parent or absolute
#                              writes, no dot files). It does NOT stop a READ
#                              of an absolute path (MEASURED 2026-10-06:
#                              \openin of /etc/hostname opened); the shim's
#                              file-system view does (FIXED_RUN_VARS).
# The clock variables (SOURCE_DATE_EPOCH, FORCE_SOURCE_DATE) are the CLOCK's
# (clock_vars), not this table's: until OPEN-128 this table held
# SOURCE_DATE_EPOCH=0, which fixed \pdfcreationdate and the PDF /ID only.
ORACLE_TEX_VARS = {"openin_any": "p", "openout_any": "p"}

# THE CLOCK OF A RUN (ADR-015 E10, OPEN-128 (2)/(3)). A clock is a string:
#   "fixed:E"   every wall-clock input the run can observe is fixed at the
#               epoch E: SOURCE_DATE_EPOCH=E with FORCE_SOURCE_DATE=1
#               (\year, \month, \day, \time, \pdfcreationdate, the PDF /ID:
#               texmfmp.c reads them), and LP_CLOCK_EPOCH=E for the shim
#               (gettimeofday: \pdfrandomseed's seed, \pdfelapsedtime;
#               time(2), clock_gettime(REALTIME) and every file time:
#               \pdffilemoddate and any date a \write18 child prints).
# The PROTOCOL's clock is fixed at PROTOCOL_EPOCH = 1785024000 =
# 2026-07-26T00:00:00Z, the date of the pinned TeX Live image (tex-oracle.yml:
# "texlive/texlive:latest-medium as of 2026-07-26"): a date the image's own
# packages were current at. gen_contract.py finds date-dependent names by
# running under a SECOND fixed clock (OPEN-128 (6)), never the real one.
# LEGACY_CLOCKS are the values recorded before OPEN-128 ("real": the grading
# machine's clock; "forced": FORCE_SOURCE_DATE=1 with SOURCE_DATE_EPOCH=0, the
# O-5 experiment): they are known to the gates as historical record, and no
# run can use them.
PROTOCOL_EPOCH = 1785024000
CLOCK_PREFIX = "fixed:"
PROTOCOL_CLOCK = f"{CLOCK_PREFIX}{PROTOCOL_EPOCH}"
LEGACY_CLOCKS = ("real", "forced")


def clock_epoch(clock: str) -> int:
    """The epoch of a fixed clock "fixed:E"; OracleError for anything else
    (the real clock is not a clock any run may use since OPEN-128)."""
    if not isinstance(clock, str) or not clock.startswith(CLOCK_PREFIX):
        raise OracleError(f"unknown clock {clock!r}: a run's clock is "
                          f"'{CLOCK_PREFIX}<epoch>' (protocol {PROTOCOL_CLOCK!r})")
    e = clock[len(CLOCK_PREFIX):]
    if not re.fullmatch(r"[0-9]{1,11}", e):
        raise OracleError(f"clock {clock!r}: the epoch is not a non-negative integer")
    return int(e)


def is_clock(clock) -> bool:
    """A clock a recorded block may name: a fixed clock, or a legacy value."""
    if clock in LEGACY_CLOCKS:
        return True
    try:
        clock_epoch(clock)
        return True
    except OracleError:
        return False


def clock_vars(clock: str) -> dict:
    """The environment that fixes the run's clock at `clock` (see above)."""
    e = str(clock_epoch(clock))
    return {"SOURCE_DATE_EPOCH": e, "FORCE_SOURCE_DATE": "1", "LP_CLOCK_EPOCH": e}


# THE FIXED RUN VARIABLES (OPEN-128 (1)): the same values in every run, on
# every platform, because the paths are the container's, not the host's.
#   TEXMFHOME/TEXMFVAR/TEXMFCONFIG  EVERY writable tree of kpathsea's TEXMF
#       in the pinned image (MEASURED 2026-09-28, `kpsewhich -var-value=TEXMF`
#       with HOME=/tmp: {TEXMFCONFIG,TEXMFVAR,TEXMFHOME,!!TEXMFLOCAL,
#       !!TEXMFSYSCONFIG,!!TEXMFSYSVAR,!!TEXMFDIST}; the four `!!` trees are
#       the image's and read-only), private to the run on its fresh tmpfs.
#       TEXMFCONFIG was missing until review round 5: kpathsea searches it
#       FIRST, and a .sty written there by one run turned another document's
#       grade from rc 1 to rc 0 (MEASURED, C-91).
#   TMPDIR/TMP/TEMP and java's tmpdir  (C-93): restricted \write18 runs the
#       image's shell_escape_commands and kpathsea runs mktex* for a missing
#       font; they write temporary files (gs under repstopdf: /tmp/gs_*,
#       LEFT when a timeout kills the run; mktex*: $TMPDIR/mt$$.tmp;
#       texosquery-jre8: /tmp/hsperfdata_<user>, which -XX:-UsePerfData stops;
#       MEASURED 2026-09-29 command by command). Python's tempfile reads
#       TMPDIR/TEMP/TMP, Perl's File::Temp TMPDIR.
#   PYTHONHASHSEED/PERL_HASH_SEED/PERL_PERTURB_KEYS  the hash randomisation
#       of the Python (latexminted, memoize-extract.py) and Perl (repstopdf,
#       memoize-extract.pl) programs a restricted \write18 starts: a run-
#       dependent input of their output order (OPEN-128 (1), census row
#       "hash seeds").
#   LP_FS_ROOTS/LP_FS_EXE  the shim's file-system view: a TeX Live program
#       (its executable under LP_FS_EXE) reads, writes and lists only the run
#       directory, the run's /tmp and the TeX tree (and /dev/null); see
#       lpshim.c. LP_SHIM_MARK: proof the shim loaded (the supervisor's
#       check). LP_FS_LOG: the paths it refused, reported per run.
TEXMF_ROOT = "/usr/local/texlive"
FIXED_TREES = {"TEXMFHOME": PRIVATE_ROOT + "/texmf-home",
               "TEXMFVAR": PRIVATE_ROOT + "/texmf-var",
               "TEXMFCONFIG": PRIVATE_ROOT + "/texmf-config"}
FIXED_TMP = PRIVATE_ROOT + "/tmp"
FS_ROOTS = (RUN_DIR, "/tmp", TEXMF_ROOT)


def java_tool_options(tmpdir: str) -> str:
    return f"-XX:-UsePerfData -Djava.io.tmpdir={tmpdir}"


FIXED_RUN_VARS = {
    **FIXED_TREES,
    "TMPDIR": FIXED_TMP, "TMP": FIXED_TMP, "TEMP": FIXED_TMP,
    "JAVA_TOOL_OPTIONS": java_tool_options(FIXED_TMP),
    "PYTHONHASHSEED": "0", "PERL_HASH_SEED": "0", "PERL_PERTURB_KEYS": "0",
    "LP_FS_ROOTS": ":".join(FS_ROOTS), "LP_FS_EXE": TEXMF_ROOT + "/",
    "LP_SHIM_MARK": SHIM_MARK_DIR, "LP_FS_LOG": FS_LOG,
}
# The directories a run's supervisor creates on the fresh tmpfs before the
# engine starts (a missing TMPDIR makes gs and mktex.opt fail, which WOULD
# change a grade: C-93).
FIXED_RUN_DIRS = (*FIXED_TREES.values(), FIXED_TMP, SHIM_MARK_DIR)
# What a TMPDIR may not hold: whitespace (JAVA_TOOL_OPTIONS is split on it),
# control characters, and what kpathsea or a shell would expand.
_PLAIN_PATH_BAD = re.compile(r"[\s\x00-\x1f\x7f~$!{}:,;'\"\\`*?]")


def oracle_tex_vars(td=None) -> dict:
    """The TeX-shaping variables of a graded run under the protocol clock:
    ORACLE_TEX_VARS, the fixed run variables and the clock. `td` is accepted
    for the callers written before OPEN-128 and IGNORED: the private trees
    are the run container's, at fixed paths, not the caller's."""
    return {**FIXED_RUN_VARS, **ORACLE_TEX_VARS, **clock_vars(PROTOCOL_CLOCK)}


def oracle_tex_env(td=None) -> dict:
    """The per-run environment a Python grader passes: the host environment
    with `oracle_tex_vars()` on top. Only `_ENV_FORWARD` variables ever reach
    an engine (engine_env), and graded_env imposes every one of them."""
    return dict(os.environ, **oracle_tex_vars(td))


# ONE GRADING PROTOCOL, IMPOSED BY THE ORACLE, NOT CHOSEN BY THE CALLER
# (OPEN-118 known limit (b), C-91). Until 2026-09-28 ORACLE_TEX_VARS reached a
# graded run only when the CALLER put it there: the Python graders did, but
# the `_oracle.py pdflatex` shim passed the host environment, so
# false_ready_oracle.sh and diff_compile_check.sh graded with pdfTeX's
# defaults; and check_apply_fixes_roundtrip passed `dict(os.environ)`. So
# `graded_env` is applied INSIDE run_pdflatex, the one path every graded run
# takes (run_once, run_to_fixpoint, the shim), and a graded run's TeX-shaping
# variables are EXACTLY: ORACLE_TEX_VARS, FIXED_RUN_VARS and the clock's,
# imposed over anything the caller's dict held. Every other `_ENV_FORWARD`
# variable of the caller (a host SOURCE_DATE_EPOCH, FORCE_SOURCE_DATE,
# max_print_line, a TEXMFVAR or TMPDIR of its own) is DROPPED. Since OPEN-128
# a caller no longer supplies the private trees: they are the run
# container's, at fixed paths (before, graded_env REQUIRED the caller's
# private TEXMFHOME/TEXMFVAR/TEXMFCONFIG and TMPDIR, which is what the paths
# a document could read back were).
# Override, not refuse: the shell graders discard the shim's stderr, so a
# refusal would reach the user as an unexplained "not graded" for an
# environment variable they may not know they export. The shim reports what
# it overrode on stderr.


def graded_env(env: dict | None, clock: str = PROTOCOL_CLOCK) -> dict:
    """The variables of a GRADED pdflatex run built from `env`: every
    `_ENV_FORWARD` variable of `env` dropped, then ORACLE_TEX_VARS, the fixed
    run variables and `clock`'s imposed. Non-TeX keys of `env` are kept here
    but never reach the engine (engine_env)."""
    out = {k: v for k, v in (env or {}).items() if not _ENV_FORWARD.match(k)}
    out.update(FIXED_RUN_VARS)
    out.update(ORACLE_TEX_VARS)
    out.update(clock_vars(clock))
    return out


# run_engine's callers (gen_contract.py, the L_S0 generators) may change
# only the log's line width; every other TeX-shaping variable they pass must
# be the protocol's own value (oracle_tex_vars), and the clock is a parameter.
RUN_ENGINE_OVERRIDES = frozenset(("max_print_line", "error_line", "half_error_line"))


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
# unaffected. So an engine sees EXACTLY the image's own environment (below)
# plus the `_ENV_FORWARD` variables the oracle chose, and nothing of the host:
# since OPEN-128 the run supervisor starts the engine with that dictionary,
# passed to it verbatim (not inherited from docker or the shell, so not even
# docker's HOSTNAME reaches the engine), and the session probe checks that a
# container of the launch definition has the image's environment.
# IMAGE_ENV is `docker inspect --format '{{json .Config.Env}}'` of the pinned
# digest (MEASURED 2026-09-28) with HOME=/tmp, which every run is started with.
IMAGE_ENV = {
    "HOME": "/tmp",
    "PATH": "/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin",
    "LANG": "C.UTF-8",
    "LC_ALL": "C.UTF-8",
    "TEXLIVE_INSTALL_NO_CONTEXT_CACHE": "1",
    "NOPERLDOC": "1",
    "DEBIAN_FRONTEND": "noninteractive",
}
# Variables of a container's environment that are not the image's: docker
# sets HOSTNAME (the launch definition fixes it to ORACLE_HOSTNAME). The
# engine does not get it (the supervisor passes engine_env verbatim).
_CONTAINER_ONLY_ENV = {"HOSTNAME": ORACLE_HOSTNAME}


def engine_env(tex_vars: dict | None, base: dict = IMAGE_ENV,
               extra=frozenset()) -> dict:
    """The COMPLETE environment of an engine run: `base` (the image's) plus the
    `_ENV_FORWARD` variables of `tex_vars` (and, for a measurement, its
    MEASURE_ENV names, `extra`). Every other key of `tex_vars` (a caller's
    copy of the host environment) is dropped, whatever its name."""
    out = dict(base)
    out.update({k: v for k, v in (tex_vars or {}).items()
                if _ENV_FORWARD.match(k) or k in extra})
    return out


def check_container_env(env: dict, where: str) -> None:
    """A container's own environment must be IMAGE_ENV plus docker's HOSTNAME,
    which the launch definition fixes."""
    if env.get("HOSTNAME") != ORACLE_HOSTNAME:
        raise OracleError(f"{where}: the container's HOSTNAME is "
                          f"{env.get('HOSTNAME')!r}, not {ORACLE_HOSTNAME!r} "
                          f"(--hostname of the launch definition)")
    got = {k: v for k, v in env.items() if k not in _CONTAINER_ONLY_ENV}
    if got != IMAGE_ENV:
        extra = sorted(set(got) - set(IMAGE_ENV))
        diff = sorted(k for k in IMAGE_ENV if got.get(k) != IMAGE_ENV[k])
        raise OracleError(
            f"{where}: the container's environment is not the pinned image's "
            f"(extra {extra[:6]}, different {diff[:6]}): the image or the "
            f"launch definition is not the pinned one")


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
                  and not (k in FIXED_RUN_VARS and v == FIXED_RUN_VARS[k])
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


def check_engine_argv(args, cwd, *, graded: bool, measure: bool = False) -> None:
    """Refuse (OracleError) any argv that is not on the allow-list above.
    `measure` (the measurement entry point, never a grade): run_engine's
    allow-list, and the file argument may be absent (the run reads its
    terminal input, as spike H.2's `pdftex -ini` does)."""
    if not isinstance(args, (list, tuple)) or not all(isinstance(a, str) for a in args):
        raise OracleError(f"engine argv must be a list of str, got {args!r:.200}")
    flags = GRADED_FLAGS if graded else RUN_ENGINE_FLAGS
    valued = {} if graded else RUN_ENGINE_VALUED
    what = ("a graded pdflatex run" if graded
            else "measure" if measure else "run_engine")
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
    if measure and not graded and not positional:
        return
    if len(positional) != 1:
        raise OracleError(f"{what} takes exactly one file argument, got {positional!r:.200}")
    p = positional[0]
    head = p.lstrip(" \t")
    if not head or head[0] in "-&*" or (graded and head[0] == "\\"):
        raise OracleError(f"{what}: file argument {p!r:.100} starts with -, &, * "
                          f"or \\ (an option, a format selector, INITEX's "
                          f"switch or TeX code)")
    if not graded and head[0] == "\\":
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
    check_file_argument(p, cwd, what)


# THE FILE ARGUMENT IS ONE THE ORACLE CAN NAME EXACTLY (C-95, review round 3,
# M1/L1). pdftex_jobname models pdfTeX's job name from the argument's TEXT,
# but pdfTeX derives it from the file kpathsea FINDS: for `a.b` it tries
# `a.b.tex` first and, if that exists, the job is `a.b`, not `a` (MEASURED);
# `a%b.tex` and `a~b.tex` make the job `texput` and read nothing (rc 1);
# `doc.tex/` is not a file. Rather than model kpathsea's lookup, the oracle
# REFUSES every argument whose outputs it cannot name with certainty (fail
# closed, OracleError, never a grade): each path component is plain
# ([A-Za-z0-9_+,=@-], then also `.`; no leading `.`, no empty component), the
# file ends in a known TeX extension (.tex or .ltx, any case: the corpus has
# .tex x 2828 and .TEX x 3, MEASURED over its 2,831 toplevels), it EXISTS in
# the run directory as a regular file (not a symlink), and when the name does
# not end in `.tex` there is no `<name>.tex` beside it (which kpathsea would
# read instead).
_ARG_COMPONENT = re.compile(r"[A-Za-z0-9_+,=@-][A-Za-z0-9_.+,=@-]*")
TEX_EXTENSIONS = (".tex", ".ltx")


def check_file_argument(p: str, cwd, what: str = "a graded pdflatex run") -> None:
    rel = p
    if os.path.isabs(p):
        rel = str(Path(p).resolve().relative_to(Path(cwd).resolve()))
    parts = rel.split("/")
    bad = [c for c in parts if not _ARG_COMPONENT.fullmatch(c)]
    if bad:
        raise OracleError(f"{what}: file argument {p!r:.100} has a component "
                          f"{bad[0]!r:.60} that is not a plain name (the oracle "
                          f"cannot name its outputs as pdfTeX would)")
    base = parts[-1]
    if "." not in base or "." + base.rpartition(".")[2].lower() not in TEX_EXTENSIONS:
        raise OracleError(f"{what}: file argument {p!r:.100} does not end in a "
                          f"known TeX extension {TEX_EXTENSIONS}")
    f = Path(cwd) / rel
    if f.is_symlink() or not f.is_file():
        raise OracleError(f"{what}: file argument {p!r:.100} is not a regular "
                          f"file in {cwd}")
    if not base.endswith(".tex") and (Path(cwd) / (rel + ".tex")).exists():
        raise OracleError(f"{what}: {rel}.tex exists beside {p!r:.100}; kpathsea "
                          f"would read it instead, so the job name is ambiguous")


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


def pdftex_jobname(args) -> str:
    """THE job name pdfTeX gives a run with argv `args` (a list, or one file
    argument as a str) -- the ONE source of every output name the oracle
    clears or reads (C-95, review round 2). MEASURED 2026-09-29 in the pinned
    image (web2c pdfTeX 1.40.29): `-jobname=X` wins; otherwise the file
    argument, with every `"` removed and its directory dropped, loses its LAST
    `.` and everything after it, whatever the case or the extension:
    a.b.tex -> a.b, doc.ltx / doc.TEX / Doc.TeX -> doc / Doc, doc. -> doc,
    doc.tex. -> doc.tex, a.b (a file) -> a, doc -> doc, d/in.tex -> in,
    .tex -> "" (outputs .log/.pdf), "doc.tex" -> doc; a first argument that
    is TeX code (`\\dump`) gives `texput`. Stripping only a lowercase `.tex`
    (the function this replaces) named doc.TEX's outputs doc.TEX.pdf, so the
    stale doc.pdf survived and graded compiles."""
    if isinstance(args, (str, Path)):
        args = [str(args)]
    for a in args:
        for pre in ("-jobname=", "--jobname="):
            if a.startswith(pre):
                return a[len(pre):].replace('"', "")
    pos = [a for a in args if not a.startswith("-")]
    if not pos or pos[-1].lstrip(" \t").startswith(("\\", "&", "*")):
        return "texput"
    name = pos[-1].replace('"', "").rsplit("/", 1)[-1]
    return name.rpartition(".")[0] if "." in name else name


class EngineRun(tuple):
    """(rc, combined output, timed_out), unpackable as before, plus `stdout`:
    pdfTeX's TERMINAL stream alone, the channel a document cannot write after
    pdfTeX's final report (C-99)."""

    def __new__(cls, rc, out, timed_out, stdout=b""):
        t = super().__new__(cls, (rc, out, timed_out))
        t.stdout = stdout
        return t


# THE DOCUMENT MUST NOT WRITE ANY FILE THE ORACLE READS AS EVIDENCE (C-99,
# review round 3, H1). MEASURED by the review: under openout_any=p a document
# may `\immediate\openout` its OWN \jobname.log while pdfTeX holds it open,
# write past the log's real end and finish it with a forged
# "Output written on \jobname.pdf (1 page, ...)", and with a .pdf it wrote
# itself the oracle graded compiles although the same run's terminal ended
# with pdfTeX's genuine "No pages of output.". Text evidence alone cannot be
# made safe: a document can forge any log text, and it can print a forged
# report on the terminal and then switch to \batchmode, which silences
# pdfTeX's genuine one. So every engine run is SUPERVISED: a small process
# (below) starts the engine in the run directory with stdin /dev/null, and
# counts with inotify the IN_CLOSE_WRITE events of the job's evidence files
# (<job>.log/.pdf/.fls/.fmt). pdfTeX opens each for writing exactly once
# (MEASURED: 1 each, also with -recorder); a document that opens one of them
# for writing -- by its name or through a symlink, which inotify reports
# under the target's name (MEASURED) -- makes a second close-write, and the
# run is REFUSED (OracleError: such a document is ungradable, never graded).
# An inotify failure or a queue overflow is refused too (fail closed).
# ONE FILE, MANY NAMES (C-99 amended, review round 4). A name is not a file:
# the container's work root is virtiofs over the Mac's APFS, which is case-
# AND Unicode-normalisation-insensitive (MEASURED in the pinned container:
# doc.log, DOC.log and Doc.LOG stat to one inode; so do NFC and NFD été.log,
# and straße.log / STRASSE.log / strasse.log), and inotify reports the name
# the WRITER used. A document that wrote DOc.log and DOc.pdf (a different
# variant each pass) graded compiles although pdfTeX shipped no page
# (MEASURED end to end at 20718e42). So the supervisor identifies evidence by
# the FILE: after the run it stats every name that was close-written or
# renamed into the run directory, and a name that is not byte-equal to an
# evidence name but is the same (st_dev, st_ino), or equal to one under
# canonical caseless matching NFD(casefold(NFD(.))), is an ALIAS: the run is
# refused. The folding test also covers an alias whose file is gone; on a
# case-sensitive work root (CI's Linux) it refuses a document that writes
# DOC.log beside doc.log, which is over-refusal of a document nobody writes,
# never a grade. A document cannot delete or rename a file (TeX has no such
# primitive); a RENAME inside the run directory carries the close-writes of
# the old name to the new one (IN_MOVED_FROM/TO, paired by cookie), so a file
# written elsewhere and renamed onto <job>.pdf still counts. pdfTeX itself
# renames: -recorder writes pdflatex<pid>.fls and renames it to <job>.fls
# while it is still open (MEASURED in the pinned image; counting the rename
# as a write, my first version, refused every -recorder run, i.e. every
# gen_contract job).
# The watch includes IN_MODIFY although only close-writes are counted: the
# kernel MERGES an event identical to the unread event at the queue's tail,
# and MEASURED in the pinned image, `echo x > t.log; echo y >> t.log` under
# an IN_CLOSE_WRITE-only watch counted ONE close-write. With IN_MODIFY
# watched, a document's close-write of the log cannot sit next to pdfTeX's
# own: pdfTeX writes its final report to the log (an IN_MODIFY) after
# closing the document's \write streams and before closing the log.
# THE SUPERVISOR ALSO STARTS THE RUN (OPEN-128). Since every run is a fresh
# container, the supervisor prepares it before the engine starts: it creates
# the run's private trees and TMPDIR on the fresh tmpfs (FIXED_RUN_DIRS),
# deletes the job's stale evidence files INSIDE the container (a host-side
# delete leaves the VM's view of the directory stale for about a second, and
# pdfTeX then cannot create its log: ContainerOracle.remove), and starts the
# engine with EXACTLY the environment the oracle chose (`env`, verbatim, plus
# LD_PRELOAD of the shim). After the run it reports, on its evidence line:
# the sha256 of the shim file it preloaded, the shim's mark for the ENGINE
# process ("restricted": loaded, with the TeX file-system view; absent: the
# dynamic loader ignored the preload, and the run had the real clock), the
# paths the shim refused (a diagnostic), and for a measurement the clock
# readings the run used.
_SUPERVISOR_SRC = r"""
import ctypes, hashlib, json, os, select, struct, subprocess, sys, unicodedata
nonce, cfg, cmd = sys.argv[1], json.loads(sys.argv[2]), sys.argv[3:]
names = cfg["names"]
def fold(n):
    n = unicodedata.normalize("NFD", n)
    return unicodedata.normalize("NFD", n.casefold())
ev = {"cw": {}, "alias": [], "overflow": 0, "err": ""}
try:
    for d in cfg.get("mkdirs", []):
        os.makedirs(d, exist_ok=True)
    for f in cfg.get("remove", []):
        try:
            os.unlink(f)
        except FileNotFoundError:
            pass
except OSError as e:
    sys.stderr.write("lp-supervisor: cannot prepare the run: %r\n" % (e,)); sys.exit(127)
env = dict(cfg["env"])
shim = cfg.get("shim")
if shim:
    try:
        with open(shim, "rb") as fh:
            ev["shim_sha256"] = hashlib.sha256(fh.read()).hexdigest()
    except OSError as e:
        ev["shim_sha256"] = "unreadable: %r" % (e,)
    env["LD_PRELOAD"] = shim
seen, moves = {}, {}
fd = -1
try:
    libc = ctypes.CDLL(None, use_errno=True)
    fd = libc.inotify_init1(0o4000)
    if fd < 0 or libc.inotify_add_watch(fd, b".", 0x8 | 0x2 | 0x40 | 0x80) < 0:
        raise OSError(ctypes.get_errno(), "inotify")
except Exception as e:
    ev["err"] = repr(e)[:200]
def drain():
    while fd >= 0:
        try:
            buf = os.read(fd, 65536)
        except BlockingIOError:
            return
        off = 0
        while off + 16 <= len(buf):
            _, mask, cookie, ln = struct.unpack_from("iIII", buf, off)
            name = buf[off + 16:off + 16 + ln].split(b"\0", 1)[0]
            off += 16 + ln
            if mask & 0x4000:
                ev["overflow"] += 1
            if mask & 0x40:
                moves[cookie] = name
            if mask & 0x80 and cookie in moves:
                src = moves.pop(cookie)
                seen[name] = seen.get(name, 0) + seen.pop(src, 0)
            if mask & 0x8 and name:
                seen[name] = seen.get(name, 0) + 1
try:
    stdin = open(cfg["stdin"], "rb") if cfg.get("stdin") else subprocess.DEVNULL
    child = subprocess.Popen(cmd, stdin=stdin, env=env)
except OSError as e:
    sys.stderr.write("%s\n" % e); sys.exit(127)
while child.poll() is None:
    if fd >= 0:
        select.select([fd], [], [], 0.2)
        drain()
    else:
        child.wait()
drain()
def ident(n):
    try:
        st = os.stat(n)
    except OSError:
        return None
    return (st.st_dev, st.st_ino)
evid = {}
for e in names:
    i = ident(os.fsencode(e))
    if i is not None:
        evid[i] = e
folds = {fold(e): e for e in names}
for n, c in seen.items():
    s = os.fsdecode(n)
    if s in names:
        ev["cw"][s] = ev["cw"].get(s, 0) + c
        continue
    hit = evid.get(ident(n)) or folds.get(fold(s))
    if hit is not None:
        ev["alias"].append([s[:120], hit])
        ev["cw"][hit] = ev["cw"].get(hit, 0) + c
ev["alias"] = ev["alias"][:20]
ev["engine_pid"] = child.pid
if cfg.get("mark"):
    try:
        with open(os.path.join(cfg["mark"], str(child.pid))) as fh:
            ev["shim_mode"] = fh.read().strip()
    except OSError:
        ev["shim_mode"] = None
if cfg.get("fs_log"):
    try:
        with open(cfg["fs_log"], errors="replace") as fh:
            lines = sorted(set(fh.read().splitlines()))
        ev["fs_denied"] = [len(lines)] + lines[:20]
    except OSError:
        ev["fs_denied"] = [0]
if cfg.get("clock_log"):
    try:
        with open(cfg["clock_log"], errors="replace") as fh:
            ev["clock_log"] = fh.read()[:1000000]
    except OSError:
        ev["clock_log"] = ""
sys.stderr.write("\n%s_EVID=%s\n" % (nonce, json.dumps(ev, sort_keys=True)))
sys.stderr.flush()
rc = child.returncode
sys.exit(rc if rc >= 0 else 128 - rc)
"""


def evidence_names(args) -> list[str]:
    """The evidence files of a run (the supervisor's `names`)."""
    job = pdftex_jobname(args)
    return [job + e for e in _Base.RUN_OUTPUTS]


def check_evidence(stderr: bytes, nonce: str, args, what: str,
                   shim_sha256: str | None = None) -> tuple[bytes, dict]:
    """Refuse a run whose supervisor saw the document write an evidence file
    (or saw nothing), or, when `shim_sha256` is given, whose engine did not
    run under that shim with the TeX file-system view (OPEN-128). Returns
    stderr without the evidence line, and the evidence record."""
    m = re.search(rb"^" + re.escape(nonce.encode()) + rb"_EVID=(.*)$", stderr, re.M)
    if m is None:
        raise OracleError(f"{what}: the run's supervisor reported no evidence "
                          f"line, so whether the document wrote pdfTeX's own "
                          f"output files is unknown; not a grade")
    try:
        ev = json.loads(m.group(1))
    except ValueError:
        raise OracleError(f"{what}: unreadable evidence line {m.group(1)[:200]!r}")
    if ev.get("err") or ev.get("overflow"):
        raise OracleError(f"{what}: the supervisor could not watch the run "
                          f"directory ({ev.get('err') or 'inotify queue overflow'}); "
                          f"not a grade (C-99)")
    alias = ev.get("alias")
    if not isinstance(alias, list):
        raise OracleError(f"{what}: the supervisor's evidence line has no alias "
                          f"list; not a grade (C-99)")
    if alias:
        raise OracleError(
            f"{what}: the document wrote pdfTeX's own evidence file under "
            f"another name ({alias[:3]}: the same file by inode, or by the "
            f"case/Unicode folding of a case-insensitive work root): the "
            f"evidence of the run is the document's, so it is ungradable -- "
            f"refused, never graded (C-99 amended)")
    twice = sorted(n for n, c in ev.get("cw", {}).items() if c > 1)
    if twice:
        raise OracleError(
            f"{what}: the document opened pdfTeX's own {twice} for writing "
            f"(written {[ev['cw'][n] for n in twice]} times; pdfTeX writes each "
            f"once): the evidence of the run is the document's, so it is "
            f"ungradable -- refused, never graded (C-99)")
    if shim_sha256 is not None:
        if ev.get("shim_sha256") != shim_sha256:
            raise OracleError(
                f"{what}: the run preloaded a shim with sha256 "
                f"{ev.get('shim_sha256')!r}, not the pinned {shim_sha256} "
                f"(SHIM_SHA256); its clock and file-system view are not the "
                f"protocol's; not a grade (OPEN-128)")
        if ev.get("shim_mode") != "restricted":
            raise OracleError(
                f"{what}: the engine process carries no mark of the shim "
                f"({ev.get('shim_mode')!r}): the dynamic loader did not "
                f"preload it, so the run read the real clock and the whole "
                f"file system; not a grade (OPEN-128)")
    return stderr[:m.start()] + stderr[m.end():], ev


def job_output(cwd, args, ext: str) -> Path:
    """cwd/<pdfTeX's job name><ext>: where pdfTeX writes the run's `ext` file."""
    return Path(cwd) / (pdftex_jobname(args) + ext)


# THE PDF VERDICT (C-97 forge, review rounds 2 and 3; C-99). `compiles` = rc
# 0 AND a PDF PDFTEX WROTE IN THIS RUN. A file named <job>.pdf is not
# evidence (a document can \openout one, MEASURED), and neither is text a
# document could have written. The verdict is pdfTeX's own FINAL REPORT --
# "Output written on <job>.pdf (N page(s), M bytes).", "No pages of output."
# or "!  ==> Fatal error occurred, no output PDF file produced!" -- read from
# TWO channels:
#   * the run's LOG, which the supervisor proves only pdfTeX wrote (C-99
#     block above): the LAST report, followed only by pdfTeX's
#     "PDF statistics:" block;
#   * the run's TERMINAL (stdout), which a document cannot write after
#     pdfTeX's final report (/dev/stdout and every absolute path are refused
#     under openout_any=p): the LAST report, followed only by
#     "Transcript written on <job>.log.". A document in \batchmode at the
#     end silences the terminal's report (MEASURED: no report at all); then
#     the log alone decides.
# When both channels carry a report they must AGREE, else OracleError (a
# document printed a forged report and silenced the real one: ungradable).
# TeX wraps both streams at 79 bytes, and a line of exactly 79 bytes may be
# a wrap OR a line followed by a print_nl (MEASURED: "...cmr10.pfb>" of 79
# bytes then "Output written ..."), so the report is searched for anywhere in
# the un-wrapped text, not only at a line start.
_REPORT = re.compile(
    rb"Output written on (?P<name>[^\n]+?)\.pdf \((?P<n>\d+) pages?, \d+ bytes\)\."
    rb"|No pages of output\.|!  ==> Fatal error occurred, no output PDF file produced!")


def _unwrap_log(data: bytes) -> list[bytes]:
    """TeX hard-wraps log lines at max_print_line (79 bytes); a line of
    exactly 79 continues on the next (concatenation is the inverse)."""
    out, cur = [], b""
    for line in data.split(b"\n"):
        cur += line
        if len(line) != 79:
            out.append(cur)
            cur = b""
    if cur:
        out.append(cur)
    return out


def terminal_tails(job: str) -> set[bytes]:
    """Every text pdfTeX itself prints on the terminal after its final report
    (lines joined, so TeX's 79-byte wrap and SyncTeX's unwrapped printf
    need no line model): nothing; "Transcript written on <job>.log."; and,
    with \\synctex set, "SyncTeX written on <job>.synctex.gz." (or
    .synctex.) before it. MEASURED in the pinned image, review round 4: 9
    frame papers set \\synctex=1, and pdfTeX prints the SyncTeX line on the
    terminal only (the log's tail is unchanged). Only pdfTeX writes the
    terminal after its report, so admitting its own SyncTeX line adds no
    forgery; a forged report followed by these lines still meets the log,
    which must agree (pdf_written)."""
    j = job.encode()
    t = b"Transcript written on " + j + b".log."
    out = {b"", t}
    for ext in (b".synctex.gz", b".synctex"):
        sy = b"SyncTeX written on " + j + ext + b"."
        out |= {sy, sy + t}
    return out


def final_report(data: bytes, job: str, channel: str):
    """pdfTeX's final report in `data` (a log or a terminal stream):
    ("pdf", pages), ("none", 0), or None when there is none (a terminal
    silenced by \batchmode; a log of a killed run). Raises OracleError when
    text follows the report that pdfTeX never prints after it."""
    flat = b"\n".join(_unwrap_log(data))
    last = None
    for m in _REPORT.finditer(flat):
        last = m
    if last is None:
        return None
    tail = [ln for ln in flat[last.end():].split(b"\n") if ln.strip()]
    if channel == "log":
        ok = all(ln == b"PDF statistics:" or ln.startswith(b" ") for ln in tail)
    else:
        ok = b"".join(tail) in terminal_tails(job)
    if not ok:
        raise OracleError(f"text follows pdfTeX's final report in the run's "
                          f"{channel} ({tail[:2]!r:.200}); pdfTeX prints nothing "
                          f"there, so the report cannot be trusted (C-99)")
    if last.group("name") is None:
        return ("none", 0)
    if last.group("name") != job.encode():
        return ("none", 0)
    return ("pdf", int(last.group("n")))


def pdf_written(cwd, args, stdout: bytes) -> bool:
    """Did pdfTeX itself write <job>.pdf, with pages, in the run whose log is
    <job>.log and whose terminal output is `stdout`? See the block above."""
    if stdout is None:
        raise OracleError("pdf_written needs the run's terminal output (C-99)")
    job = pdftex_jobname(args)
    log, pdf = job_output(cwd, args, ".log"), job_output(cwd, args, ".pdf")
    log_r = final_report(log.read_bytes(), job, "log") if log.is_file() else None
    term_r = final_report(stdout, job, "terminal")
    if term_r is not None and log_r is not None and term_r[0] != log_r[0]:
        raise OracleError(
            f"the run's terminal says {term_r[0]!r} and its log says "
            f"{log_r[0]!r}: a document printed a forged final report and "
            f"silenced pdfTeX's (\\batchmode); ungradable, never graded (C-99)")
    if term_r is not None and log_r is None:
        raise OracleError("the terminal carries a final report and the log none; "
                          "not a grade (C-99)")
    return (log_r is not None and log_r[0] == "pdf" and log_r[1] >= 1
            and pdf.is_file() and not pdf.is_symlink())


def _require_output_written(out: bytes, args: list[str], what: str) -> None:
    m = _OWN_WRITE_FAIL.search(out)
    if m:
        raise OracleError(
            f"{what}: pdfTeX could not write its own output "
            f"({m.group(0).decode()!r}); the work root is full or failing, so "
            f"this rc is not a property of the document")
    job = pdftex_jobname(args)
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


def _check_fingerprint(fp: dict, where: str, measurement: bool = False) -> None:
    """Refuse a TeX tree that is not the pinned image's for its architecture,
    and (unless `measurement`: the measurement entry point, never a grade) an
    architecture other than ARCH_OF_RECORD."""
    if IMAGE != FINGERPRINTED_IMAGE:
        raise OracleError(
            f"tex-oracle.yml pins {IMAGE} but the tree fingerprints in "
            f"_oracle.py were measured for {FINGERPRINTED_IMAGE}. A re-pin must "
            f"re-measure them (`_oracle.py fingerprint` inside each platform "
            f"image) in the same PR.")
    want = TREE_FINGERPRINTS.get(fp["arch"])
    if want is None:
        raise OracleError(f"{where}: no recorded fingerprint for arch {fp['arch']!r}")
    if fp["arch"] != ARCH_OF_RECORD and not measurement:
        raise OracleError(
            f"{where}: this oracle runs on {fp['arch']}, but the oracle's "
            f"architecture of record is {ARCH_OF_RECORD} (ADR-015 E2). The "
            f"pinned pdfTeX gives different verdicts on the two architectures "
            f"for some documents (C-103: `\\pdfsnapy 0pt` exits 0 on aarch64 "
            f"and 136 on x86_64), so a grade taken here is not comparable to "
            f"any recorded one; refusing to grade.")
    if EXPECT_VERSION not in fp["banner"]:
        raise OracleError(f"{where}: banner {fp['banner']!r} is not the pin "
                          f"{EXPECT_VERSION!r}")
    for k in ("tlpdb_sha256", "macro_layer_sha256", "fmt_sha256"):
        if fp[k] != want[k]:
            raise OracleError(
                f"{where}: {k} = {fp[k]} but the pinned image's {fp['arch']} tree "
                f"is {want[k]}. This TeX tree is NOT the oracle; refusing to grade.")


# THE ORACLE'S IDENTITY, AND THE ONE COMPARISON OF TWO ORACLE BLOCKS (ADR-015
# E2, E10; OPEN-126, OPEN-128 (3)). Two grades are comparable only when they
# were taken by the same image, on the same architecture, over the same TeX
# tree, under the same CLOCK (a grade under another fixed clock, or one
# recorded before the clock was fixed, may differ in any document that
# reads it). The grading code is checked separately by
# require_same_grading_code because its remedy differs (re-grade, not
# re-pin). The backend is not part of it: since OPEN-128 there is one
# (the container, ADR-015 E15).
IDENTITY_KEYS = ("image", "arch", "tlpdb_sha256", "macro_layer_sha256",
                 "fmt_sha256", "clock")


def identity_mismatch(a: dict | None, b: dict | None) -> list[str]:
    """The IDENTITY_KEYS on which two oracle blocks differ (a missing key
    differs from everything, including another missing key)."""
    a, b = a or {}, b or {}
    return [k for k in IDENTITY_KEYS
            if a.get(k) is None or b.get(k) is None or a.get(k) != b.get(k)]


def require_same_oracle(recorded: dict | None, live: dict | None,
                        what: str) -> None:
    """Refuse (OracleError) to compare a grade recorded under `recorded` with
    one taken under `live` unless they are the same oracle. A block that
    names no architecture or no clock is refused too: it cannot be shown
    comparable. A MEASUREMENT block (`measure`: never a grade, and on a
    non-record architecture tagged measurement_only) is refused on either
    side (ADR-015 E7)."""
    for side, blk in (("recorded", recorded), ("live", live)):
        if isinstance(blk, dict) and (blk.get("entry") == "measure"
                                      or blk.get("measurement_only")):
            raise OracleError(
                f"{what}: the {side} oracle block is a MEASUREMENT "
                f"(entry {blk.get('entry')!r}, measurement_only "
                f"{blk.get('measurement_only')!r}, arch {blk.get('arch')!r}); "
                f"a measurement is never a grade and is never compared with "
                f"one (ADR-015 E7)")
    bad = identity_mismatch(recorded, live)
    if not bad:
        return
    r, l = recorded or {}, live or {}
    if "arch" in bad:
        raise OracleError(
            f"{what}: the recorded grades were taken on "
            f"{r.get('arch') or 'an unrecorded architecture'} and this "
            f"oracle runs on {l.get('arch') or 'an unrecorded architecture'}. "
            f"Grades are not compared across architectures (ADR-015 E2, "
            f"C-103: the same image gives different exit codes on aarch64 "
            f"and x86_64); re-grade on {ARCH_OF_RECORD}.")
    if "clock" in bad:
        raise OracleError(
            f"{what}: the recorded grades were taken under clock "
            f"{r.get('clock')!r} and this oracle grades under {l.get('clock')!r}. "
            f"A document can read the clock (\\year, \\pdfrandomseed, "
            f"\\pdffilemoddate, ...), so grades under two clocks are not "
            f"compared (ADR-015 E10, OPEN-128); re-grade under "
            f"{PROTOCOL_CLOCK!r}.")
    raise OracleError(
        f"{what}: the recorded grades are of another oracle ({', '.join(bad)} "
        f"differ: recorded {[r.get(k) for k in bad]}, live "
        f"{[l.get(k) for k in bad]}); a grade is compared only with one of "
        f"the same image and tree.")


# THE GRADING CODE IS PART OF A GRADE'S PROVENANCE (OPEN-126, stock-take
# 2026-09-30 §3b). The image pins the engine and its tree; what the oracle
# DOES with them -- the pass protocol, the PDF verdict, the evidence
# supervisor, the environment -- is this module and the grader that calls it,
# and they changed under the recorded grades five times in review rounds of
# #626 while the artefacts kept naming only the image. So every artefact a
# grader writes records the git blob id of each file of its grading code
# (`grading_code(grader)`), and a comparison of a recorded grade with a live
# one, and the pure gate, refuse a grade whose code is not the current code
# (`grading_code_drift`). A blob id, not a hash of our own: it is
# content-addressed, so a squash merge keeps it, and the gate can fetch the
# RECORDED version from git to tell a comment-only edit (the same Python AST
# without docstrings, compared by ONE interpreter, so independent of its
# version) from a change of behaviour. The CLI's version is not here: it is
# `src_tree_sha` (C-64), and a re-grade of the oracle side never moves it.
GRADING_CODE_CORE = ("scripts/tools/_oracle.py",)


def _git_out(repo: Path, *args: str) -> subprocess.CompletedProcess:
    return subprocess.run(["git", "--no-optional-locks", *args], cwd=repo,
                          capture_output=True)


def grading_code(graders, repo: Path = REPO) -> dict:
    """{"files": {path: git blob id at HEAD}, "sha256": ...} of the grading
    code: GRADING_CODE_CORE plus `graders` (repo-relative paths). Refuses
    (OracleError) a file that is untracked or differs from HEAD: a grade must
    name code that exists in the history, or nothing can check it later."""
    files = sorted(set(GRADING_CODE_CORE) | set(graders))
    blobs = {}
    for f in files:
        if _git_out(repo, "diff", "--quiet", "HEAD", "--", f).returncode != 0:
            raise OracleError(f"grading code {f} differs from HEAD (or HEAD "
                              f"does not have it): commit it before grading, "
                              f"so the artefact can name it (OPEN-126)")
        p = _git_out(repo, "rev-parse", f"HEAD:{f}")
        if p.returncode != 0:
            raise OracleError(f"grading code {f} is not tracked at HEAD")
        blobs[f] = p.stdout.decode().strip()
    return {"files": blobs, "sha256": grading_code_sha256(blobs)}


def grading_code_sha256(blobs: dict) -> str:
    return hashlib.sha256(json.dumps(blobs, sort_keys=True).encode()).hexdigest()


def _py_behaviour(src: bytes) -> str | None:
    """The Python AST of `src` without docstrings, dumped without positions:
    two sources with the same value differ only in comments, docstrings and
    layout. None when `src` does not parse."""
    import ast
    try:
        tree = ast.parse(src)
    except (SyntaxError, ValueError):
        return None
    for node in ast.walk(tree):
        body = getattr(node, "body", None)
        if (isinstance(node, (ast.Module, ast.ClassDef, ast.FunctionDef,
                              ast.AsyncFunctionDef))
                and body and isinstance(body[0], ast.Expr)
                and isinstance(body[0].value, ast.Constant)
                and isinstance(body[0].value.value, str)):
            node.body = body[1:] or [ast.Pass()]
    return ast.dump(tree, include_attributes=False)


def grading_code_drift(recorded: dict | None, repo: Path = REPO,
                       current: dict | None = None) -> tuple[list, list]:
    """(findings, notes) comparing a recorded grading_code block with the
    code in `repo`'s working tree (or with `current`, another block). A
    finding is a reason the recorded grade is NOT a grade of this code:
    the block is missing or incoherent, a recorded blob is not in the
    repository, the file set differs, or a file changed in behaviour. A
    comment/docstring-only change is a note."""
    if not isinstance(recorded, dict) or not isinstance(recorded.get("files"), dict):
        return ["records no grading_code (the git blob ids of the oracle and "
                "grader sources that produced it, OPEN-126)"], []
    rf = recorded["files"]
    if recorded.get("sha256") != grading_code_sha256(rf):
        return ["grading_code.sha256 is not the hash of its own files map "
                "(edited by hand?)"], []
    findings, notes = [], []
    missing_core = sorted(set(GRADING_CODE_CORE) - set(rf))
    if missing_core:
        findings.append(f"grading_code omits the oracle core {missing_core}")
    if current is not None:
        cf = current.get("files") or {}
        if set(cf) != set(rf):
            findings.append(f"grading_code covers {sorted(rf)} but the "
                            f"current grader's is {sorted(cf)}")
    for path, blob in sorted(rf.items()):
        if not re.fullmatch(r"[0-9a-f]{40}|[0-9a-f]{64}", str(blob)):
            findings.append(f"grading_code[{path}] = {blob!r} is not a git blob id")
            continue
        old = _git_out(repo, "cat-file", "blob", blob)
        if old.returncode != 0:
            findings.append(
                f"grading_code[{path}] names blob {blob[:12]} which is not "
                f"in this repository (a shallow clone needs fetch-depth: 0; "
                f"otherwise the grade names code that never existed here)")
            continue
        if current is not None:
            now_blob = (current.get("files") or {}).get(path)
            if now_blob is None:
                continue
            now = _git_out(repo, "cat-file", "blob", now_blob)
            now_src = now.stdout if now.returncode == 0 else None
        else:
            f = repo / path
            now_src = f.read_bytes() if f.is_file() else None
            now_blob = (_git_out(repo, "hash-object", "--", path).stdout
                        .decode().strip() if now_src is not None else None)
        if now_src is None:
            findings.append(f"grading code {path} no longer exists")
            continue
        if now_blob == blob:
            continue
        if (path.endswith(".py") and _py_behaviour(old.stdout) is not None
                and _py_behaviour(old.stdout) == _py_behaviour(now_src)):
            notes.append(f"{path}: changed since the grade in comments, "
                         f"docstrings or layout only (same AST)")
            continue
        findings.append(
            f"{path} changed in behaviour since the grade (blob "
            f"{blob[:12]} -> {str(now_blob)[:12]}): the recorded grades are "
            f"not grades of the current grading code")
    return findings, notes


class RunStamp:
    """A GRADE'S PROVENANCE IS TAKEN WHEN ITS RUN STARTS (OPEN-128 (4); OPEN-126
    KNOWN LIMITS). Until OPEN-128 the producers read `grading_code` and the
    commit they stamp (`measured_at_sha`, `oracle_regraded_at_sha`) from
    HEAD when they WROTE the artefact, and two recorded runs spanned a commit
    (OPEN-126's full re-grade started at 7020f7e7 and is stamped a652a675):
    had the grading code changed between, the artefact would have named code
    that did not grade it. Every producer now takes a RunStamp before its
    first engine run -- the HEAD, and the grading code of the oracle core and
    its `graders` (grading_code refuses a file that differs from HEAD) --
    stamps THOSE, and calls `check` before writing: it refuses (a reason
    string, or OracleError from `require`) when the grading code at the end
    is not the one the run started with. HEAD itself may move during a long
    run (a documentation commit); the stamp is the start's."""

    def __init__(self, graders, repo: Path = REPO):
        self.repo = Path(repo)
        self.graders = tuple(graders)
        p = _git_out(self.repo, "rev-parse", "HEAD")
        if p.returncode != 0:
            raise OracleError("cannot read HEAD to stamp the run")
        self.head = p.stdout.decode().strip()
        self.gc = grading_code(self.graders, self.repo)

    def check(self) -> str | None:
        """Why the run's result may not be written, or None."""
        try:
            now = grading_code(self.graders, self.repo)
        except OracleError as e:
            return f"the grading code is no longer committed and clean: {e}"
        if now != self.gc:
            return (f"the grading code changed during the run (started "
                    f"{self.gc['sha256'][:12]} at {self.head[:12]}, now "
                    f"{now['sha256'][:12]}); the grades are of the code at the "
                    f"start, which is no longer the code. Re-run.")
        return None

    def require(self) -> None:
        why = self.check()
        if why:
            raise OracleError(f"nothing written: {why}")

    def oracle_block(self, oracle, clock: str = PROTOCOL_CLOCK) -> dict:
        """The oracle's provenance with the run's clock and grading code."""
        return dict(oracle.provenance(), clock=clock, grading_code=self.gc)


def require_same_grading_code(recorded: dict | None, current: dict,
                              what: str) -> None:
    """Refuse (OracleError) to carry forward or compare recorded grades whose
    grading code is not `current` (comment-only drift is accepted)."""
    findings, _ = grading_code_drift(recorded, REPO, current=current)
    if findings:
        raise OracleError(f"{what}: " + "; ".join(findings))


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
    supervised = True  # a grading backend's every engine run (C-99)

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
            "clock": PROTOCOL_CLOCK,
        }

    @property
    def banner(self) -> str:
        return self.fingerprint()["banner"]

    # -- work directories -------------------------------------------------
    def tempdir(self, prefix: str = "lp-oracle-"):
        return tempfile.TemporaryDirectory(prefix=prefix)

    def tex_env(self, td=None) -> dict:
        """The per-run environment a grader passes (oracle_tex_env). Since
        OPEN-128 graded_env imposes every TeX-shaping variable itself, so
        this is kept for the callers that pass it; `td` is ignored."""
        return oracle_tex_env(td)

    def remove(self, paths) -> None:
        """Delete files in a work directory that pdflatex will write again.
        See ContainerOracle.remove for why this must go through the oracle."""
        for p in paths:
            Path(p).unlink(missing_ok=True)  # unlink never follows a symlink

    def mkdtemp(self, prefix: str = "lp-oracle-") -> Path:
        """A work directory the oracle can run in that outlives a `with`
        block (the caller removes it). Container: under the work root."""
        return Path(tempfile.mkdtemp(prefix=prefix))

    # -- running ----------------------------------------------------------
    def run_pdflatex(self, cwd: Path, args: list[str], env: dict | None,
                     timeout: int, clock: str = PROTOCOL_CLOCK) -> tuple[int, bytes, bool]:
        """ONE graded pdflatex run, in the protocol's environment
        (`graded_env(env, clock)`: ORACLE_TEX_VARS, the fixed run variables
        and the clock imposed, no other TeX variable) and with an argv on the
        graded allow-list (`check_engine_argv`, C-91 round 5). Returns (rc,
        combined output, timed_out)."""
        args = list(args)
        check_engine_argv(args, cwd, graded=True)
        env = graded_env(env, clock)
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
        stale = [job_output(cwd, args, e) for e in self.RUN_OUTPUTS]
        # A document that ships its own output name as a SYMLINK (doc.pdf ->
        # fig.pdf) is not graded: pdfTeX would write through it into the
        # target (MEASURED, review round 2: rc 1 without clearing, the figure
        # deleted by a clearing that followed the link, rc 0 by one that
        # unlinked it -- three answers, none the document's). 0 symlinks in
        # the 2,719-paper corpus (measured).
        links = [q.name for q in stale if q.is_symlink()]
        if links:
            raise OracleError(f"{links} in {cwd} is a symlink: pdfTeX would write "
                              f"through it into its target, so no grade (C-95)")
        stale = [q for q in stale if q.exists()]
        if stale:
            self._clear(stale)

    def _clear(self, stale: list[Path]) -> None:
        """Delete the stale outputs found by clear_outputs (host side). The
        container backend deletes them INSIDE the run's container instead
        (its supervisor), so this is a no-op there."""
        self.remove(stale)

    def _exec(self, cwd: Path, engine: str, args: list[str], env: dict | None,
              timeout: int) -> tuple[int, bytes, bool]:
        raise NotImplementedError

    def run_engine(self, cwd: Path, engine: str, args: list[str], tex_vars: dict,
                   timeout: int, clock: str = PROTOCOL_CLOCK) -> tuple[int, bytes, bool]:
        """ONE run of a TeX `engine` (one of ENGINES) with argv `args` in
        `cwd`, for a client that is not a document grader: gen_contract.py's
        pdflatex jobs and its INITEX (`pdftex -ini`) kernel jobs.

        Same guarantees as run_pdflatex -- the pinned image, a verified tree,
        the rc read inside the container, positive proof pdfTeX ran (its
        banner, which INITEX prints too), the free-space floor before and
        after, pdfTeX's own write failures refused (OracleError: not a
        result) -- and the same environment, with two differences a caller
        states explicitly: `clock` (gen_contract.py runs under a SECOND fixed
        clock to find the kernel's date-dependent names, OPEN-128 (6)), and
        the log's line width (RUN_ENGINE_OVERRIDES). Every other key of
        `tex_vars` must be a TeX-shaping variable whose value is the
        protocol's own (`oracle_tex_vars()`), or the call is refused rather
        than silently overridden. Returns (rc, combined output, timed_out)."""
        if engine not in ENGINES:
            raise OracleError(f"engine {engine!r} is not one of {ENGINES}")
        check_engine_argv(list(args), cwd, graded=False)
        bad = sorted(k for k in tex_vars if not _ENV_FORWARD.match(k))
        if bad:
            raise OracleError(f"run_engine: {bad} are not TeX-shaping variables "
                              f"the oracle forwards (_ENV_FORWARD)")
        base = {**FIXED_RUN_VARS, **ORACLE_TEX_VARS, **clock_vars(clock)}
        proto = oracle_tex_vars()
        differ = sorted(k for k, v in tex_vars.items()
                        if k not in RUN_ENGINE_OVERRIDES
                        and v != base.get(k) and v != proto.get(k))
        if differ:
            raise OracleError(
                f"run_engine: {differ} differ from the protocol's values; a "
                f"caller may change only {sorted(RUN_ENGINE_OVERRIDES)} and the "
                f"clock (the `clock` parameter), OPEN-128")
        env = dict(base, **{k: v for k, v in tex_vars.items()
                            if k in RUN_ENGINE_OVERRIDES})
        self.clear_outputs(Path(cwd), list(args))
        return self._exec(Path(cwd), engine, list(args), env, timeout,
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
        r = self.run_pass(work, toplevel, env, timeout, halt)
        return r.rc, r.timed_out

    def run_pass(self, work: Path, toplevel: str, env: dict | None, timeout: int,
                 halt: bool = True, clock: str = PROTOCOL_CLOCK) -> OracleRun:
        """ONE graded pass, with its PDF verdict (pdf_written, from this
        pass's own terminal output and log)."""
        args = ["-interaction=nonstopmode"] + (["-halt-on-error"] if halt else []) + [toplevel]
        r = self.run_pdflatex(Path(work), args, env, timeout, clock)
        rc, _, to = r
        if to:
            return OracleRun(-1, 1, False, True)
        return OracleRun(rc, 1, pdf_written(Path(work), toplevel, r.stdout), False)

    def run_to_fixpoint(self, work: Path, toplevel: str, env: dict | None,
                        timeout: int, max_passes: int = MAX_PASSES,
                        clock: str = PROTOCOL_CLOCK) -> OracleRun:
        """The recorded protocol; see diff_real_roots.run_to_fixpoint's
        docstring for why each step exists."""
        work = Path(work)
        # Each pass's PDF/log is its own: run_pdflatex clears them (C-95).

        # The PDF verdict is the LAST pass's (the authoritative one), from
        # its own terminal output and log (pdf_written, C-99); a timed-out
        # pass has none.
        passes = 0
        r = None
        for _ in range(max_passes):
            r = self.run_pass(work, toplevel, env, timeout, clock=clock)
            passes += 1
            if r.timed_out:
                return OracleRun(-1, passes, False, True)
            if r.rc == 0:
                break
        if r.rc != 0:
            return OracleRun(r.rc, passes, r.pdf, False)
        r = self.run_pass(work, toplevel, env, timeout, clock=clock)
        passes += 1
        if r.timed_out:
            return OracleRun(-1, passes, False, True)
        return OracleRun(r.rc, passes, r.pdf, False)


class NativeOracle(_Base):
    """An engine run as a process of THIS host, not in a container.

    RETIRED AS A GRADER (ADR-015 E15, owner 2026-10-06; OPEN-128 (4)). Until
    OPEN-128 this was CI's backend: tex-oracle.yml started the pinned image
    itself (`docker run ... LP_ORACLE_IN_IMAGE=...`) and graded inside it,
    with a launch configuration of its own (a 4g /tmp without noexec, its
    work directories under /tmp) that check_oracle_pin compared with the
    container's flag by flag: two launch definitions, kept in step by hand.
    Now CI grades through ContainerOracle from its runner host, and
    get_oracle() refuses LP_ORACLE_IN_IMAGE. This class stays only as the
    base of HostDiagnostic, which grades nothing: constructing it directly
    is refused."""
    backend = "native"
    grading = False

    def __init__(self):
        raise OracleError(
            "the native backend (grading inside the image, LP_ORACLE_IN_IMAGE) "
            "is retired (ADR-015 E15, OPEN-128): every grade runs through "
            "ContainerOracle's one launch definition, in CI from the runner "
            "host")

    def _exec(self, cwd, engine, args, env, timeout, exact_env=False):
        # The run's private trees and TMPDIR: the fixed container paths
        # (PRIVATE_ROOT) mapped to a fresh host directory, removed after.
        with tempfile.TemporaryDirectory(prefix="lp-native-") as priv:
            env = {k: (v.replace(PRIVATE_ROOT, priv) if isinstance(v, str) else v)
                   for k, v in (env or {}).items()}
            for d in FIXED_RUN_DIRS:
                Path(d.replace(PRIVATE_ROOT, priv)).mkdir(parents=True, exist_ok=True)
            env = engine_env(env, self.engine_base)
            _require_free_space(cwd, "before")
            try:
                p = subprocess.Popen([engine, *args], cwd=cwd, env=env,
                                     stdin=subprocess.DEVNULL,
                                     stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                     start_new_session=True)
            except OSError as e:
                raise OracleError(f"cannot execute {engine}: {e}") from e
            try:
                out, err = p.communicate(timeout=timeout)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(p.pid, 9)
                except OSError:
                    pass
                p.communicate()
                _require_free_space(cwd, "after")
                return EngineRun(124, b"", True)
            _require_pdftex_ran(p.returncode, out, f"host {engine}")
            _require_output_written(out + err, args, f"host {engine}")
            _require_free_space(cwd, "after")
            return EngineRun(p.returncode, out + err, False, out)

    def _image_command(self, argv, cwd, timeout):
        try:
            p = subprocess.run(argv, cwd=cwd, capture_output=True, timeout=timeout,
                               env=engine_env({}, self.engine_base),
                               stdin=subprocess.DEVNULL)
        except (subprocess.TimeoutExpired, OSError) as e:
            raise OracleError(f"image command {argv[:1]} failed: {e}") from e
        return p.returncode, p.stdout, p.stderr


class HostDiagnostic(NativeOracle):
    """The host's own TeX Live, for DIAGNOSIS ONLY: attributing an
    oracle-baseline diff to the host tree (ADR-012 decision 7 asks for each
    changed cell to be classified). It is NOT the oracle: `get_oracle()` never
    returns it, it verifies nothing, and its provenance says so, so a grade it
    produces cannot be mistaken for one. Callers: oracle_baseline_classify.py.

    UNSUPERVISED (review round 4): the evidence supervisor needs inotify,
    which the Mac hosting this TeX Live lacks, so a supervised run refused
    every host run and the tool died on its first row. A diagnostic proves
    nothing about the document's evidence anyway; the engine still reads
    /dev/null, and get_oracle() never returns this class."""
    backend = "host-diagnostic-NOT-THE-ORACLE"
    supervised = False

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


# THE ORACLE'S LD_PRELOAD SHIM (OPEN-128 (1)-(3); scripts/tools/oracle_shim/).
# Built by oracle_shim/build.sh in a digest-pinned ubuntu:22.04 (gcc 11.4.0);
# these hashes pin the committed .so files, which the oracle copies into the
# work root, mounts read-only at SHIM_DIR and verifies twice: on the host
# before every session, and inside every run (the supervisor hashes the file
# it preloads, and the engine process must carry the shim's mark).
SHIM_SRC_DIR = REPO / "scripts" / "tools" / "oracle_shim"
SHIM_SHA256 = {
    "aarch64": "450f0ee7bc674d168f2709b9c8bed5555f35bed9b036269fe7f3ca4a98577d34",
    "x86_64": "b60e047ba73bf82dba423bf1f41bb32a3edbb2c5cbd247b3f43a2c89c74556bf",
}


def shim_name(arch: str) -> str:
    return f"lpshim-{arch}.so"


# Characters a host path may not hold in a `docker run -v HOST:CONT` mount.
_MOUNT_BAD = re.compile(r"[:,\x00-\x1f]")
# The in-container shell of a run: the protocol's timeout INSIDE the
# container (killing the docker client on the host would leave the engine
# running), the supervisor, then the rc on a line tagged with the run's
# nonce, which -- not the docker client's exit code -- is the rc (see
# PDFTEX_BANNER for why).
_RUN_SCRIPT = ('n=$1; t=$2; sup=$3; shift 3; '
               'timeout -k 10 "$t" python3 -I -c "$sup" "$n" "$@"; '
               'rc=$?; printf "\\n%s=%d\\n" "$n" "$rc" >&2')


def launch_argv(user: str, name: str, *, arch: str = ARCH_OF_RECORD,
                mounts=(), workdir: str = RUN_DIR, entry=()) -> list[str]:
    """THE ONE LAUNCH DEFINITION (ADR-015 E15, OPEN-128 (4)): the `docker`
    argv of every container the oracle starts -- a graded run, a
    run_engine job, a measurement, the session probe, an image command, a
    removal -- locally and in CI. `mounts` is ((host, container, read_only),
    ...); `entry` is the command (its first word becomes --entrypoint).
    check_oracle_pin.py and check_oracle_infra_grading.py read the flags
    from here; nothing else in the repository starts the image."""
    if arch not in PLATFORMS:
        raise OracleError(f"no platform for architecture {arch!r}")
    if not entry:
        raise OracleError("launch_argv needs a command")
    argv = ["run", "--rm", "--pull", "never", "--name", name,
            "--label", "lp-oracle-run=1", "--init",
            "--pids-limit", str(PIDS_LIMIT),
            "--memory", MEMORY_LIMIT, "--memory-swap", MEMORY_LIMIT,
            "--read-only", "--tmpfs", f"/tmp:{TMPFS_OPTIONS}",
            "--network", "none", "--hostname", ORACLE_HOSTNAME,
            "--user", user, "--platform", PLATFORMS[arch]]
    for host, cont, ro in mounts:
        host = str(host)
        if _MOUNT_BAD.search(host) or _MOUNT_BAD.search(cont):
            raise OracleError(f"mount {host!r} -> {cont!r} holds ':' , ',' or a "
                              f"control character")
        argv += ["-v", f"{host}:{cont}" + (":ro" if ro else "")]
    argv += ["-w", workdir, "-e", "HOME=/tmp", "--entrypoint", str(entry[0]),
             IMAGE, *map(str, entry[1:])]
    return argv


# The session probe: one container of the launch definition reports the TeX
# tree's fingerprint, the read-only/non-root facts, its own environment, the
# nonce the host wrote into its run directory (positive proof the work root
# is the same directory inside), and the sha256 of the shim it would preload.
def _session_probe_source(arch: str) -> str:
    import inspect
    return ("import hashlib, json, os, platform, subprocess\nfrom pathlib import Path\n"
            + inspect.getsource(tree_fingerprint)
            + "\n_ro_info = {}\nexec(" + repr(_READONLY_PROBE.replace(
                "print(json.dumps(", "_ro_info.update((")) + ")\n"
            + "out = {'fp': tree_fingerprint(), 'ro': _ro_info, 'env': dict(os.environ),\n"
            + f"       'nonce': open({RUN_DIR + '/nonce'!r}).read(),\n"
            + f"       'shim': hashlib.sha256(open({SHIM_DIR + '/' + shim_name(arch)!r}, 'rb')"
            + ".read()).hexdigest()}\n"
            + "print(json.dumps(out))\n")


class ContainerOracle(_Base):
    """THE oracle: every engine run is a fresh container of the pinned image,
    started by `launch_argv` (see the blocks above PIDS_LIMIT and RUN_DIR)."""
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
        if _MOUNT_BAD.search(wr):
            raise OracleError(f"oracle work root {wr} holds ':' or ','")
        self.workroot.mkdir(parents=True, exist_ok=True)
        # The engine's user: the host's, so the bind-mounted run directory is
        # its own (OPEN-126); never root.
        self.user = f"{os.getuid()}:{os.getgid()}"
        if os.getuid() == 0:
            raise OracleError("the container oracle is not started from a root "
                              "host process: its engine would run as root")
        # A label for messages; containers are per run and named per run.
        self.name = "lp-oracle-" + IMAGE.split("sha256:")[-1][:12]
        self._fps: dict = {}
        self._check_daemon()
        self.shim_dir = self._install_shim()
        # Verify the tree EAGERLY (the session probe), as before: graders that
        # never asked for provenance must not grade with an unchecked tree.
        self.fingerprint()

    def _dk(self, *args, timeout=120, check=False, input=None):
        try:
            p = subprocess.run([self.docker, *args], capture_output=True,
                               timeout=timeout, input=input,
                               **({} if input is not None else
                                  {"stdin": subprocess.DEVNULL}))
        except subprocess.TimeoutExpired as e:
            raise OracleError(f"docker {' '.join(args[:2])} timed out") from e
        if check and p.returncode != 0:
            raise OracleError(f"docker {' '.join(args[:3])} failed rc={p.returncode}: "
                              f"{p.stderr.decode(errors='replace').strip()[:400]}")
        return p

    def _check_daemon(self):
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

    def _install_shim(self) -> Path:
        """Copy the pinned shim files into the work root (the container can
        mount only the work root on colima) and return their directory."""
        tag = hashlib.sha256(json.dumps(SHIM_SHA256, sort_keys=True).encode()
                             ).hexdigest()[:16]
        d = self.workroot / ".lp-shim" / tag
        d.mkdir(parents=True, exist_ok=True)
        for arch, want in SHIM_SHA256.items():
            src = SHIM_SRC_DIR / shim_name(arch)
            try:
                data = src.read_bytes()
            except OSError as e:
                raise OracleError(f"the oracle's shim {src} is unreadable: {e}")
            if hashlib.sha256(data).hexdigest() != want:
                raise OracleError(
                    f"{src} has sha256 {hashlib.sha256(data).hexdigest()}, not "
                    f"the pinned {want} (_oracle.SHIM_SHA256): rebuild it with "
                    f"oracle_shim/build.sh or re-pin it in the same commit")
            dst = d / shim_name(arch)
            try:
                ok = hashlib.sha256(dst.read_bytes()).hexdigest() == want
            except OSError:
                ok = False
            if not ok:
                tmp = d / f".{shim_name(arch)}.{os.getpid()}.{uuid.uuid4().hex[:8]}"
                tmp.write_bytes(data)
                os.replace(tmp, dst)
        return d

    def _launch(self, name: str, argv: list[str], timeout: int):
        """Run one container (argv from launch_argv). An expired client
        timeout removes the container (by its per-run name) and is an
        OracleError, never an engine timeout."""
        try:
            return subprocess.run([self.docker, *argv], capture_output=True,
                                  timeout=timeout, stdin=subprocess.DEVNULL)
        except subprocess.TimeoutExpired:
            self._dk("rm", "-f", name, timeout=60)
            raise OracleError(f"docker run {name} did not return within {timeout}s")

    @staticmethod
    def _run_name() -> str:
        return "lp-oracle-run-" + uuid.uuid4().hex[:16]

    def session_probe(self, arch: str = ARCH_OF_RECORD) -> dict:
        """One container of the launch definition, checked: its TeX tree is
        the pinned image's for `arch`, read-only, its user is not root, its
        environment is the image's (plus the fixed HOSTNAME), the host's run
        directory is the same directory inside, and the shim it would
        preload is the pinned one. Returns the fingerprint."""
        where = f"container of {IMAGE} ({arch})"
        probe_dir = Path(tempfile.mkdtemp(prefix="lp-oracle-probe-", dir=self.workroot))
        nonce = uuid.uuid4().hex
        try:
            (probe_dir / "nonce").write_text(nonce)
            name = self._run_name()
            p = self._launch(name, launch_argv(
                self.user, name, arch=arch,
                mounts=((probe_dir, RUN_DIR, True), (self.shim_dir, SHIM_DIR, True)),
                entry=("python3", "-I", "-c", _session_probe_source(arch))), 300)
        finally:
            shutil.rmtree(probe_dir, ignore_errors=True)
        if p.returncode != 0:
            raise OracleError(f"{where}: the session probe failed (rc "
                              f"{p.returncode}): "
                              + p.stderr.decode(errors="replace")[:400])
        try:
            got = json.loads(p.stdout)
        except ValueError:
            raise OracleError(f"{where}: unreadable session probe {p.stdout[:200]!r}")
        if got.get("nonce") != nonce:
            raise OracleError(
                f"{where}: the work root {self.workroot} is not visible inside "
                f"the container (colima mounts only $HOME by default). Choose a "
                f"work root under $HOME via LP_ORACLE_WORKROOT.")
        _check_fingerprint(got["fp"], where, measurement=arch != ARCH_OF_RECORD)
        if got["fp"].get("arch") != arch:
            raise OracleError(f"{where}: the container runs on "
                              f"{got['fp'].get('arch')!r}, not {arch!r}")
        check_readonly(got["ro"], where)
        check_container_env(got["env"], where)
        if got.get("shim") != SHIM_SHA256[arch]:
            raise OracleError(f"{where}: the mounted shim has sha256 "
                              f"{got.get('shim')!r}, not {SHIM_SHA256[arch]}")
        return got["fp"]

    def fingerprint(self, arch: str = ARCH_OF_RECORD) -> dict:
        if arch not in self._fps:
            self._fps[arch] = self.session_probe(arch)
        if arch == ARCH_OF_RECORD:
            self._fp = self._fps[arch]
        return self._fps[arch]

    def tempdir(self, prefix: str = "lp-oracle-"):
        return tempfile.TemporaryDirectory(prefix=prefix, dir=self.workroot)

    def _inside(self, p: Path) -> bool:
        try:
            Path(p).resolve().relative_to(self.workroot)
            return True
        except ValueError:
            return False

    def remove(self, paths) -> None:
        """Delete files INSIDE a container, then on the host.

        MEASURED 2026-09-27 (colima 'default', docker runtime, virtiofs): a file
        the container created and the HOST then deleted cannot be re-created
        by a container for about a second -- `echo two > f.log` fails with
        "Directory nonexistent" -- because the VM's dentry cache is stale.
        pdflatex then cannot open its log, exits 1 and leaves no log. A
        deletion made through a container keeps the VM's cache coherent
        (measured). A graded run's own stale outputs are deleted by its
        supervisor, inside its container (_clear is a no-op here); this is
        for the shell graders (`_oracle.py rm`) and a grader's other files."""
        # The PARENT is resolved, never the name: resolving the name follows a
        # symlink, and clearing doc.pdf -> fig.pdf deleted the figure (review
        # round 2, LOW-2). `rm -f` on the link removes the link itself.
        paths = [Path(p).parent.resolve() / Path(p).name for p in paths]
        outside = [str(p) for p in paths if not self._inside(p.parent)]
        if outside:
            raise OracleError(f"refusing to delete outside the work root: {outside[:3]}")
        for i in range(0, len(paths), 200):
            name = self._run_name()
            p = self._launch(name, launch_argv(
                self.user, name, mounts=((self.workroot, str(self.workroot), False),),
                workdir="/", entry=("rm", "-f", "--", *[str(q) for q in paths[i:i + 200]])),
                120)
            if p.returncode != 0:
                raise OracleError(f"docker run rm failed rc={p.returncode}: "
                                  + p.stderr.decode(errors="replace")[:300])
        for p in paths:
            p.unlink(missing_ok=True)

    def _clear(self, stale) -> None:
        return  # the run's supervisor deletes them inside its container

    def mkdtemp(self, prefix: str = "lp-oracle-") -> Path:
        return Path(tempfile.mkdtemp(prefix=prefix, dir=self.workroot))

    def _image_command(self, argv, cwd, timeout):
        # NOT a grade and not an engine run (image_command refuses engines):
        # the work root is mounted at its own path so a caller's absolute
        # paths (gen_contract.py: `cp <fmt> <job dir>/shipped.fmt`) mean the
        # same inside.
        if cwd is not None and not self._inside(Path(cwd)):
            raise OracleError(f"{cwd} is outside the oracle work root")
        name = self._run_name()
        p = self._launch(name, launch_argv(
            self.user, name, mounts=((self.workroot, str(self.workroot), False),),
            workdir=str(Path(cwd).resolve()) if cwd is not None else "/",
            entry=argv), timeout + 60)
        return p.returncode, p.stdout, p.stderr

    def _exec(self, cwd, engine, args, env, timeout, exact_env=False, *,
              arch: str = ARCH_OF_RECORD, stdin: bytes | None = None,
              clock_log: bool = False, extra_env=frozenset(),
              require_banner: bool = True):
        """ONE engine run in a fresh container (see launch_argv). `env` is
        the run's TeX-shaping variables (graded_env / run_engine / measure);
        the engine gets exactly engine_env(env)."""
        cwd = Path(cwd).resolve()
        if not self._inside(cwd):
            raise OracleError(
                f"{cwd} is outside the oracle work root {self.workroot}, so the "
                f"container cannot see it. Create work directories with "
                f"oracle.tempdir().")
        if _MOUNT_BAD.search(str(cwd)):
            raise OracleError(f"run directory {cwd} holds ':' or ','")
        # The file argument as the container sees it: relative to RUN_DIR.
        args = [os.path.relpath(Path(a).resolve(), cwd)
                if os.path.isabs(a) and self._inside(Path(a)) else a for a in args]
        self.fingerprint(arch)
        _require_free_space(cwd, "before")
        nonce = "LP_ORACLE_RC_" + uuid.uuid4().hex
        name = self._run_name()
        cfg = {"names": evidence_names(args), "remove": evidence_names(args),
               "env": engine_env(env, extra=extra_env), "mkdirs": list(FIXED_RUN_DIRS),
               "shim": f"{SHIM_DIR}/{shim_name(arch)}", "mark": SHIM_MARK_DIR,
               "fs_log": FS_LOG}
        mounts = [(cwd, RUN_DIR, False), (self.shim_dir, SHIM_DIR, True)]
        indir = None
        if stdin is not None:
            indir = Path(tempfile.mkdtemp(prefix="lp-oracle-in-", dir=self.workroot))
            (indir / "stdin").write_bytes(stdin)
            mounts.append((indir, IN_DIR, True))
            cfg["stdin"] = IN_DIR + "/stdin"
        if clock_log:
            cfg["clock_log"] = CLOCK_LOG
        try:
            p = self._launch(name, launch_argv(
                self.user, name, arch=arch, mounts=mounts,
                entry=("sh", "-c", _RUN_SCRIPT, "sh", nonce, str(int(timeout)),
                       _SUPERVISOR_SRC, json.dumps(cfg, sort_keys=True),
                       engine, *args)), timeout + 90)
        finally:
            if indir is not None:
                shutil.rmtree(indir, ignore_errors=True)
        what = f"container {self.name} ({arch})"
        m = re.search(rb"^" + nonce.encode() + rb"=(\d+)$", p.stderr, re.M)
        if m is None:
            raise OracleError(
                f"docker run exited {p.returncode} without the in-container rc "
                f"line, so pdflatex's exit status is unknown (daemon lost, VM "
                f"gone, or the container never started); this is not a grade: "
                + p.stderr.decode(errors="replace").strip()[:400])
        rc = int(m.group(1))
        err = p.stderr[:m.start()] + p.stderr[m.end():]
        if rc in (124, 137):
            _require_free_space(cwd, "after")
            r = EngineRun(rc, p.stdout + err, True, p.stdout)
            r.evidence = {}
            return r
        if rc in (125, 126, 127):  # timeout(1) itself failed / engine missing
            raise OracleError(f"in-container timeout/{engine} failed rc={rc}: "
                              + err.decode(errors="replace")[:400])
        err, ev = check_evidence(err, nonce, args, what, SHIM_SHA256[arch])
        # A measurement may legitimately stop before pdfTeX's banner (spike
        # H.2's env-sde-bad: texmfmp.c refuses SOURCE_DATE_EPOCH=1788076260x
        # and exits 1 having printed nothing); the engine process's shim mark
        # (check_evidence) is the proof it ran. A grade still needs the banner.
        if require_banner:
            _require_pdftex_ran(rc, p.stdout, what)
        _require_output_written(p.stdout + err, args, what)
        _require_free_space(cwd, "after")
        r = EngineRun(rc, p.stdout + err, False, p.stdout)
        r.evidence = ev
        return r

    # -- the measurement entry point (ADR-015 E7) -------------------------
    def measure(self, cwd: Path, engine: str, args: list[str], *,
                stdin: bytes | None = None, env: dict | None = None,
                unset=(), arch: str = ARCH_OF_RECORD,
                clock: str = PROTOCOL_CLOCK, readings=None,
                timeout: int = 600) -> EngineRun:
        """See measure_doc below. Returns an EngineRun with `.evidence`
        (incl. the clock readings used) and `.provenance` (never a grade)."""
        if engine not in ENGINES:
            raise OracleError(f"engine {engine!r} is not one of {ENGINES}")
        if arch not in PLATFORMS:
            raise OracleError(f"architecture {arch!r} is not one of {sorted(PLATFORMS)}")
        check_engine_argv(list(args), cwd, graded=False, measure=True)
        run_env = dict(FIXED_RUN_VARS)
        if clock == "real":
            pass
        else:
            run_env.update(clock_vars(clock))
        for k, v in (env or {}).items():
            if k not in MEASURE_ENV:
                raise OracleError(f"measure: {k!r} is not a variable a measurement "
                                  f"may set ({sorted(MEASURE_ENV)[:8]}...)")
            if not isinstance(v, str) or "\x00" in v:
                raise OracleError(f"measure: {k}={v!r} is not a string")
            run_env[k] = v
        for k in unset:
            if k not in MEASURE_UNSET:
                raise OracleError(f"measure: {k!r} may not be unset ({sorted(MEASURE_UNSET)})")
            run_env.pop(k, None)
        if readings is not None:
            rs = []
            for sec, usec in readings:
                if not (isinstance(sec, int) and isinstance(usec, int)):
                    raise OracleError(f"measure: clock reading {(sec, usec)!r} is not two integers")
                rs.append(f"{sec}.{usec}")
            run_env["LP_CLOCK"] = ",".join(rs)
            run_env["LP_CLOCK_LOG"] = CLOCK_LOG
        self.clear_outputs(Path(cwd), list(args))
        r = self._exec(Path(cwd), engine, list(args), run_env, timeout, True,
                       arch=arch, stdin=stdin if stdin is not None else b"",
                       clock_log=readings is not None, extra_env=MEASURE_ENV,
                       require_banner=False)
        prov = dict(_Base.provenance(self) if arch == ARCH_OF_RECORD
                    else self._provenance_of(arch))
        prov.update({"entry": "measure", "measurement_only": arch != ARCH_OF_RECORD,
                     "clock": clock, "clock_readings": None if readings is None
                     else len(readings),
                     "env_set": sorted((env or {})), "env_unset": sorted(unset)})
        r.provenance = prov
        return r

    def _provenance_of(self, arch: str) -> dict:
        fp = self.fingerprint(arch)
        return {"engine": "pdflatex", "distribution": "TeX Live 2026",
                "version": fp["banner"], "image": IMAGE, "arch": fp["arch"],
                "tlpdb_sha256": fp["tlpdb_sha256"],
                "macro_layer_sha256": fp["macro_layer_sha256"],
                "fmt_sha256": fp["fmt_sha256"], "backend": self.backend,
                "protocol": PROTOCOL, "clock": PROTOCOL_CLOCK}

    def stop(self):
        """Remove leftover run containers of this oracle (a docker client
        killed mid-run can leave one; `--rm` removes the rest)."""
        ls = self._dk("ps", "-aq", "--filter", "label=lp-oracle-run=1", timeout=60)
        ids = ls.stdout.decode().split()
        if ids:
            self._dk("rm", "-f", *ids, timeout=120)


# THE MEASUREMENT ENTRY POINT'S ENVIRONMENT (ADR-015 E7). A measurement sees
# the fixed run variables and its clock, and may set exactly these variables
# (the spike's H.2 inputs vary them: `env SOURCE_DATE_EPOCH=...`,
# `FORCE_SOURCE_DATE=01`, and kpathsea's capacity values such as
# `main_memory=70abc`) and unset the two clock variables. It never gets
# shell_escape*, TEXMF* or a search path from its caller. The protocol's
# openin_any/openout_any are NOT imposed: spike H.2's model reads the image's
# defaults (base.spec: kpse openin_any=a), so a measurement states them.
MEASURE_ENV = frozenset((
    "SOURCE_DATE_EPOCH", "FORCE_SOURCE_DATE", "openin_any", "openout_any",
    "max_print_line", "error_line", "half_error_line", "main_memory",
    "extra_mem_top", "extra_mem_bot", "pool_size", "string_vacancies",
    "pool_free", "max_strings", "strings_free", "font_mem_size", "font_max",
    "trie_size", "hyph_size", "buf_size", "nest_size", "max_in_open",
    "param_size", "save_size", "stack_size", "dvi_buf_size", "hash_extra",
    "file_line_error_style", "parse_first_line", "command_line_encoding"))
MEASURE_UNSET = frozenset(("SOURCE_DATE_EPOCH", "FORCE_SOURCE_DATE"))


def _fingerprint_source() -> str:
    """The fingerprint function's own source, run inside the container, so the
    container and native paths cannot compute different things."""
    import inspect
    return ("import hashlib, json, platform, subprocess\nfrom pathlib import Path\n"
            + inspect.getsource(tree_fingerprint)
            + "\nprint(json.dumps(tree_fingerprint()))\n")


_FINGERPRINT_SNIPPET = _fingerprint_source()

_ORACLE = None


def in_image() -> bool:
    return bool(os.environ.get("LP_ORACLE_IN_IMAGE"))


def get_oracle(full_state: bool = True) -> _Base:
    """The oracle for this process: the container oracle, always (ADR-015
    E15). Raises OracleUnavailable/OracleError; never returns a host-pdflatex
    backend. LP_ORACLE_IN_IMAGE, which selected the retired native backend
    (CI grading inside the image), is refused: a process started inside the
    image with it is a launch the oracle did not define. `full_state` is
    kept for the callers written before OPEN-128 and has no effect: every
    run's container is fresh, so there is no long-lived state to scan."""
    global _ORACLE
    if in_image():
        raise OracleError(
            "LP_ORACLE_IN_IMAGE is set: grading inside the image (the native "
            "backend) is retired (ADR-015 E15, OPEN-128). Grade from the host, "
            "where the oracle starts each run's container itself "
            "(ContainerOracle.launch_argv, the one launch definition).")
    if _ORACLE is None:
        _ORACLE = ContainerOracle()
    if not _ORACLE.supervised:  # never a grade without the evidence supervisor
        raise OracleError(f"{type(_ORACLE).__name__} runs unsupervised (C-99)")
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
    is the inverse of the wrap).

    A DIAGNOSTIC, NOT EVIDENCE (C-99, review round 3 (c)): the log is
    pdfTeX's alone (the supervisor refuses a run whose document writes it),
    but pdfTeX itself prints what the document asks it to -- `\\message` of
    "! ..." or "l.N ..." lines lands on the terminal and in the log exactly
    like an error of pdfTeX's (MEASURED), and `\\PackageError` raises any
    message genuinely. So no grade may be decided from this text; the
    graders' cells are functions of the rc, the PDF verdict and the CLI
    verdict only (diff_real_roots.cell_of)."""
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
        if cmd == "grading-code":
            # grading-code FILE...: the grading_code block of a SHELL producer
            # (false_ready_oracle.sh's manifest re-record, OPEN-128 (8)).
            print(json.dumps(grading_code(rest), sort_keys=True))
            return 0
        if cmd == "measure":
            return measure_main(rest)
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
        # The shell graders' readers of a run's outputs (C-95/C-97 review
        # round 2): the SAME job name and PDF verdict as the Python graders.
        #   job FILEARG            print pdfTeX's job name for FILEARG
        #   pdf-written DIR FILEARG STDOUT  exit 0 iff pdfTeX wrote DIR/<job>.pdf
        #                          with pages, by its own report in the run's
        #                          log DIR/<job>.log AND its terminal output
        #                          (the file STDOUT: what the shim printed on
        #                          stdout), which must agree (C-99); exit
        #                          INFRA_RC when they disagree (not a grade)
        if cmd == "job":
            print(pdftex_jobname(rest[-1:]))
            return 0
        if cmd == "pdf-written":
            if len(rest) != 3:
                print("[oracle] pdf-written DIR FILE STDOUTFILE", file=sys.stderr)
                return INFRA_RC
            try:
                return 0 if pdf_written(Path(rest[0]), rest[1:2],
                                        Path(rest[2]).read_bytes()) else 1
            except (OracleError, OSError) as e:
                print(f"[oracle] NOT GRADED: {e}", file=sys.stderr)
                return INFRA_RC
        if cmd == "workroot":
            print(default_workroot().expanduser().resolve())
            return 0
        if cmd == "stop":
            ContainerOracle().stop()
            return 0
        o = get_oracle()
        if cmd == "info":
            print(json.dumps(o.provenance(), indent=1))
            return 0
        if cmd == "version":
            print(o.banner)
            return 0
        if cmd == "check-recorded":
            # check-recorded FILE KEY[.KEY...]: the shell graders' form of
            # require_same_oracle (ADR-015 E2, E10): the oracle block recorded
            # at KEY in the JSON FILE they grade against must be THIS oracle --
            # same image, ARCHITECTURE, tree and CLOCK. Exit 0, or INFRA_RC.
            if len(rest) != 2:
                print("[oracle] check-recorded FILE KEY[.KEY...]", file=sys.stderr)
                return INFRA_RC
            try:
                block = json.loads(Path(rest[0]).read_text())
                for k in rest[1].split("."):
                    block = block.get(k) if isinstance(block, dict) else None
                require_same_oracle(block, o.provenance(), rest[0])
            except (OracleError, OSError, ValueError) as e:
                print(f"[oracle] NOT GRADED: {e}", file=sys.stderr)
                return INFRA_RC
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
            r = o.run_pdflatex(Path.cwd(), rest, o.tex_env(), timeout)
            rc, out, to = r
            # pdfTeX's terminal output on stdout, everything else (the engine's
            # stderr, write18 children's) on stderr: the shell graders read
            # the PDF verdict from stdout (C-99, oracle_pdf_written).
            sys.stdout.buffer.write(r.stdout)
            sys.stdout.buffer.flush()
            rest = out[len(r.stdout):] if out.startswith(r.stdout) else b""
            if hasattr(sys.stderr, "buffer"):
                sys.stderr.buffer.write(rest)
            else:  # a text-only stderr (a test harness)
                sys.stderr.write(rest.decode(errors="replace"))
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


def measure_main(rest: list[str]) -> int:
    """`_oracle.py measure [OPTIONS] --work DIR -- ENGINE ARGS...` (ADR-015
    E7): ONE run of the pinned engine through the oracle's launch definition,
    for MEASUREMENT (spike H.2-H.6's binary side). Never a grade.

      --work DIR            the run directory (inside the oracle work root,
                            LP_ORACLE_WORKROOT); the files the run writes stay
                            there
      --arch A              aarch64 (default, the architecture of record) or
                            x86_64 (emulated on an arm64 host; the result is
                            tagged measurement_only)
      --stdin FILE          the run's terminal input (default: empty)
      --env N=V             set a MEASURE_ENV variable (repeatable)
      --env-file F          N=V lines; a line LP_CLOCK=S.U,S.U,... gives the
                            clock readings (the spike's docker.env format)
      --unset N             unset SOURCE_DATE_EPOCH or FORCE_SOURCE_DATE
      --clock C             fixed:E (default: the protocol clock) or real
                            (an uncontrolled control run)
      --clock-readings R    S.U,S.U,...: gettimeofday's readings in call
                            order; when none is left the run exits 97
      --timeout S           default 600
      --record FILE         write {rc, timed_out, provenance, evidence} as JSON
    The engine's terminal output goes to stdout, its standard error to
    stderr; the exit status is the engine's (124 on timeout, INFRA_RC when
    the oracle failed)."""
    if "--" not in rest:
        print(measure_main.__doc__, file=sys.stderr)
        return 2
    opts, cmdv = rest[:rest.index("--")], rest[rest.index("--") + 1:]
    if not cmdv:
        print("[oracle] measure: no engine given", file=sys.stderr)
        return 2
    work = None
    arch, stdin, env, unset = ARCH_OF_RECORD, b"", {}, []
    clock, readings, timeout, record = PROTOCOL_CLOCK, None, 600, None

    def parse_readings(text):
        out = []
        for r in text.split(","):
            m = re.fullmatch(r"(-?\d+)\.(\d+)", r.strip())
            if not m:
                raise OracleError(f"measure: bad clock reading {r!r}")
            out.append((int(m.group(1)), int(m.group(2))))
        return out
    try:
        it = iter(opts)
        for o in it:
            if o == "--work":
                work = Path(next(it))
            elif o == "--arch":
                a = next(it)
                arch = {"arm64": "aarch64", "amd64": "x86_64"}.get(a, a)
            elif o == "--stdin":
                stdin = Path(next(it)).read_bytes()
            elif o == "--env":
                k, _, v = next(it).partition("=")
                env[k] = v
            elif o == "--env-file":
                for ln in Path(next(it)).read_text().splitlines():
                    if not ln.strip():
                        continue
                    k, _, v = ln.partition("=")
                    if k == "LP_CLOCK":
                        readings = parse_readings(v)
                    else:
                        env[k] = v
            elif o == "--unset":
                unset.append(next(it))
            elif o == "--clock":
                clock = next(it)
            elif o == "--clock-readings":
                readings = parse_readings(next(it))
            elif o == "--timeout":
                timeout = int(next(it))
            elif o == "--record":
                record = Path(next(it))
            else:
                raise OracleError(f"measure: unknown option {o!r}")
        if arch not in PLATFORMS:
            raise OracleError("measure: --arch is aarch64/arm64 or x86_64/amd64")
        if work is None:
            raise OracleError("measure: --work DIR is required")
        if clock != "real":
            clock_epoch(clock)
        work.mkdir(parents=True, exist_ok=True)
        o = get_oracle()
        r = o.measure(work, cmdv[0], cmdv[1:], stdin=stdin, env=env, unset=unset,
                      arch=arch, clock=clock, readings=readings, timeout=timeout)
    except (OracleError, OSError, StopIteration, ValueError) as e:
        print(f"[oracle] measure FAILED (not a measurement): {e}", file=sys.stderr)
        return INFRA_RC
    sys.stdout.buffer.write(r.stdout)
    sys.stdout.buffer.flush()
    rest_err = r[1][len(r.stdout):] if r[1].startswith(r.stdout) else b""
    if hasattr(sys.stderr, "buffer"):
        sys.stderr.buffer.write(rest_err)
    else:  # a text-only stderr (a test harness)
        sys.stderr.write(rest_err.decode(errors="replace"))
    if record is not None:
        record.write_text(json.dumps({
            "rc": r[0], "timed_out": r[2], "provenance": r.provenance,
            "evidence": getattr(r, "evidence", {})}, indent=1, sort_keys=True) + "\n")
    return 124 if r[2] else r[0]


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
