#!/usr/bin/env python3
"""Kill-tests for check_workflow_triggers.py failure modes 6-9.

Each case copies the repo's .github into a temp dir, plants ONE edit, runs the
gate there, and requires the expected outcome: a REFUSE case must exit 1 with
its finding; an ACCEPT case (a near-miss that is legitimately fine) must exit
0. The clean copy must PASS first, or every REFUSE result would be vacuous.
The cases include every bypass the two reviews of 2026-11-03/04 found
(marked "review 1" / "review 2"), each of which exited 0 on the gate as it
then stood.

Usage: python3 scripts/tools/test_check_workflow_triggers.py [--gate PATH]
Exit 1 if any case has the wrong outcome.
"""
from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
COMPOSITE = ".github/actions/setup-ocaml-env/action.yml"
SETUP_OCAML_V2_SHA = "8cc6339f55862749298d198ef84788b8d6acdacc"  # v2.2.10
CACHE_V2_SHA = "1bd1e32a3bdc45362d1e726936510720a7c30a57"        # an actions/cache v2 commit
CACHE_SHA = "caa296126883cff596d87d8935842f9db880ef25"           # v5.1.0 (registered)
RUST_SHA = "683b588c487a69d01f6c6ddf40f036ff682cc2c8"            # registered, untagged
CHECKOUT = "actions/checkout@11d5960a326750d5838078e36cf38b85af677262 # v4.4.0"


def job(runs_on: str, extra: str = "", steps: str = "      - run: echo hi\n") -> str:
    return ("name: planted\non: workflow_dispatch\njobs:\n  planted:\n"
            f"    runs-on: {runs_on}\n{extra}    steps:\n{steps}")


def add(name: str, text: str):
    return ("add", name, text)


def sub(name: str, *pairs):
    return ("sub", name, pairs)


R, A = "REFUSE", "ACCEPT"
CASES = [
    # ── mode 7: runner labels (allow-list, case-insensitive, fail closed) ──
    (R, "runs-on group with a string labels: (review 1)",
     add(".github/workflows/zz.yml", job("\n      group: big\n      labels: ubuntu-latest")),
     r"FLOATING-RUNNER: .*zz\.yml job 'planted' runs on `ubuntu-latest`"),
    (R, "runs-on group with a list of labels",
     add(".github/workflows/zz.yml", job("\n      group: big\n      labels: [ubuntu-24.04, ubuntu-latest]")),
     r"FLOATING-RUNNER: .*runs on `ubuntu-latest`"),
    (R, "matrix.cfg.os (nested matrix value)",
     add(".github/workflows/zz.yml", job("${{ matrix.cfg.os }}",
         "    strategy:\n      matrix:\n        cfg: [{os: ubuntu-24.04}]\n")),
     r"FLOATING-RUNNER: .*an expression this gate cannot resolve"),
    (R, "inputs.os with a -latest default",
     add(".github/workflows/zz.yml",
         "name: planted\non:\n  workflow_dispatch:\n    inputs:\n      os:\n        default: ubuntu-latest\n"
         "jobs:\n  planted:\n    runs-on: ${{ inputs.os }}\n    steps:\n      - run: echo hi\n"),
     r"FLOATING-RUNNER: .*inputs\.os"),
    (R, "fromJSON runner label",
     add(".github/workflows/zz.yml", job("${{ fromJSON('[\"ubuntu-24.04\"]') }}")),
     r"FLOATING-RUNNER: .*fromJSON"),
    (R, "matrix.os literal list containing ubuntu-latest",
     add(".github/workflows/zz.yml", job("${{ matrix.os }}",
         "    strategy:\n      matrix:\n        os: [ubuntu-24.04, ubuntu-latest]\n")),
     r"FLOATING-RUNNER: .*runs on `ubuntu-latest`"),
    (R, "matrix include: adds macos-latest (review 2)",
     add(".github/workflows/zz.yml", job("${{ matrix.os }}",
         "    strategy:\n      matrix:\n        os: [ubuntu-24.04]\n        include:\n          - os: macos-latest\n")),
     r"FLOATING-RUNNER: .*runs on `macos-latest`"),
    (R, "ubuntu-slim (floating, no -latest suffix) (review 2)",
     add(".github/workflows/zz.yml", job("ubuntu-slim")),
     r"FLOATING-RUNNER: .*runs on `ubuntu-slim`"),
    (R, "Ubuntu-Latest in mixed case (review 2)",
     add(".github/workflows/zz.yml", job("Ubuntu-Latest")),
     r"FLOATING-RUNNER: .*runs on `Ubuntu-Latest`"),
    (A, "matrix.os over pinned literals",
     add(".github/workflows/zz.yml", job("${{ matrix.os }}",
         "    strategy:\n      matrix:\n        os: [ubuntu-24.04, ubuntu-24.04-arm]\n")),
     None),
    (R, "a *.yaml workflow on ubuntu-latest",
     add(".github/workflows/zz.yaml", job("ubuntu-latest")),
     r"FLOATING-RUNNER: .*zz\.yaml"),
    # ── `uses:` read through the YAML parse ──
    (R, "anchor alias to setup-ocaml (review 2)",
     add(".github/workflows/zz.yml",
         "name: planted\non: workflow_dispatch\nenv:\n  X: &so ocaml/setup-ocaml@v3\njobs:\n  planted:\n"
         "    runs-on: ubuntu-24.04\n    steps:\n      - uses: *so\n"),
     r"UNSCANNED-USES: .*zz\.yml has `uses: ocaml/setup-ocaml@v3`"),
    (R, "quoted uses key + fake uses line in a heredoc (review 2)",
     add(".github/workflows/zz.yml", job("ubuntu-24.04", steps=(
         '      - "uses": ocaml/setup-ocaml@v3\n      - run: |\n          cat <<X\n'
         f'          uses: {CHECKOUT}\n          X\n'))),
     r"UNSCANNED-USES: .*spells a `uses` key in quotes"),
    (R, "a uses: in flow style",
     add(".github/workflows/zz.yml", job("ubuntu-24.04", steps="      - {uses: actions/cache@v1}\n")),
     r"UNSCANNED-USES: .*zz\.yml has `uses: actions/cache@v1`"),
    # ── mode 8: pins (SHA + registered version comment only) ──
    (R, "a major tag @v1 (mutable) (review 2)",
     add(".github/workflows/zz.yml", job("ubuntu-24.04", steps="      - uses: some/toolchain@v1\n")),
     r"FLOATING-TOOLCHAIN: .*`some/toolchain@v1`: a third-party action must be pinned by a 40-hex"),
    (R, "no ref at all (review 2)",
     add(".github/workflows/zz.yml", job("ubuntu-24.04", steps="      - uses: some/toolchain\n")),
     r"FLOATING-TOOLCHAIN: .*`some/toolchain`: a third-party action must be pinned"),
    (R, "branch ref @release (review 2)",
     add(".github/workflows/zz.yml", job("ubuntu-24.04", steps="      - uses: some/toolchain@release\n")),
     r"FLOATING-TOOLCHAIN: .*`some/toolchain@release`"),
    (R, "dtolnay/rust-toolchain@1.99 (a branch) (review 2)",
     add(".github/workflows/zz.yml", job("ubuntu-24.04", steps="      - uses: dtolnay/rust-toolchain@1.99\n")),
     r"FLOATING-TOOLCHAIN: .*`dtolnay/rust-toolchain@1\.99`"),
    (R, "dtolnay/rust-toolchain@stable",
     add(".github/workflows/zz.yml", job("ubuntu-24.04", steps="      - uses: dtolnay/rust-toolchain@stable\n")),
     r"FLOATING-TOOLCHAIN: .*dtolnay/rust-toolchain@stable"),
    (R, "registered SHA + correct comment, but `toolchain: stable` (review 2)",
     add(".github/workflows/zz.yml", job("ubuntu-24.04", steps=(
         f"      - uses: dtolnay/rust-toolchain@{RUST_SHA} # untagged\n"
         "        with:\n          toolchain: stable\n"))),
     r"FLOATING-TOOLCHAIN: .*input `toolchain: stable` is not an exact version"),
    (R, "python-version: '3.12' (a minor floats its patch)",
     sub(".github/workflows/spec-drift.yml", ("python-version: '3.12.16'", "python-version: '3.12'")),
     r"FLOATING-TOOLCHAIN: .*input `python-version: 3\.12` is not an exact version"),
    (R, "a SHA with no version comment",
     sub(COMPOSITE, (f"actions/cache/restore@{CACHE_SHA} # v5.1.0", f"actions/cache/restore@{CACHE_SHA}")),
     r"FLOATING-TOOLCHAIN: .*actions/cache/restore@caa29612.* with comment `# None`"),
    (R, "an unregistered cache SHA behind a lying `# v4.3.0` (review 2)",
     add(".github/workflows/zz.yml", job("ubuntu-24.04", steps=f"      - uses: actions/cache@{CACHE_V2_SHA} # v4.3.0\n")),
     r"FLOATING-TOOLCHAIN: .*a SHA not recorded in \.github/action-pins\.json"),
    (R, "a registered SHA with the wrong version comment",
     sub(COMPOSITE, (f"actions/cache/save@{CACHE_SHA} # v5.1.0", f"actions/cache/save@{CACHE_SHA} # v6.1.0")),
     r"FLOATING-TOOLCHAIN: .*records that SHA as `v5\.1\.0`"),
    (R, "setup-ocaml v2 pinned by SHA",
     add(".github/workflows/zz.yml", job("ubuntu-24.04",
         steps=f"      - uses: ocaml/setup-ocaml@{SETUP_OCAML_V2_SHA} # v2.2.10\n")),
     r"FLOATING-TOOLCHAIN: .*ocaml/setup-ocaml@8cc6339f"),
    (R, "OCaml/Setup-OCaml in mixed case (review 2)",
     add(".github/workflows/zz.yml", job("ubuntu-24.04", steps="      - uses: OCaml/Setup-OCaml@v3\n")),
     r"FLOATING-TOOLCHAIN: .*OCaml/Setup-OCaml@v3`\. Every setup-ocaml"),
    (R, "docker:// by tag (review 2)",
     add(".github/workflows/zz.yml", job("ubuntu-24.04", steps="      - uses: docker://ocaml/opam:latest\n")),
     r"FLOATING-TOOLCHAIN: .*docker://ocaml/opam:latest`: a docker image must be pinned"),
    (A, "a registered SHA with its recorded version",
     add(".github/workflows/zz.yml", job("ubuntu-24.04", steps=f"      - uses: {CHECKOUT}\n")),
     None),
    (A, "an exact python-version matrix",
     add(".github/workflows/zz.yml", job("ubuntu-24.04",
         "    strategy:\n      matrix:\n        py: [\"3.11.18\", \"3.12.16\"]\n",
         steps=("      - uses: actions/setup-python@a26af69be951a213d495a4c3e4e4022e16d87065 # v5.6.0\n"
                "        with:\n          python-version: ${{ matrix.py }}\n"))),
     None),
    # ── mode 9: opam only from the canonical pinned step ──
    (R, "opam from releases/latest, checksum `|| true` (review 2)",
     sub(COMPOSITE,
         ('releases/download/${OPAM_VERSION}/opam-${OPAM_VERSION}-${arch}-linux"', 'releases/latest/download/opam-${arch}-linux"'),
         ("| sha256sum -c -\n", "| sha256sum -c - || true\n")),
     r"FLOATING-TOOLCHAIN: .*step `Install opam \(pinned, checksum-verified\)` differs from the canonical"),
    (R, "checksum only in a comment (review 2)",
     sub(COMPOSITE, ("| sha256sum -c -\n", "| cat\n        # sha256sum -c\n")),
     r"FLOATING-TOOLCHAIN: .*differs from the canonical"),
    (R, "binary installed before the checksum",
     sub(COMPOSITE,
         ('        echo "${sum}  ${RUNNER_TEMP}/opam" | sha256sum -c -\n        sudo install -m 0755 "${RUNNER_TEMP}/opam" /usr/local/bin/opam\n',
          '        sudo install -m 0755 "${RUNNER_TEMP}/opam" /usr/local/bin/opam\n        echo "${sum}  ${RUNNER_TEMP}/opam" | sha256sum -c -\n')),
     r"FLOATING-TOOLCHAIN: .*differs from the canonical"),
    (R, "the opam step without its OS/arch guard",
     sub(COMPOSITE, ("      if: runner.os == 'Linux' && (runner.arch == 'X64' || runner.arch == 'ARM64')\n", "")),
     r"FLOATING-TOOLCHAIN: .*must be guarded by `if:"),
    (R, "opam pin loosened to a minor version",
     sub(COMPOSITE, ('OPAM_VERSION: "2.6.1"', 'OPAM_VERSION: "2.6"')),
     r"FLOATING-TOOLCHAIN: .*must set exactly .*each exact"),
    (R, "opam arm64 checksum dropped",
     sub(COMPOSITE, ("        OPAM_SHA256_ARM64:", "        OPAM_SHA_ARM64:")),
     r"FLOATING-TOOLCHAIN: .*must set exactly"),
    (R, "compiler literal in the switch, apart from OCAML_VERSION (review 2)",
     sub(COMPOSITE, ('--packages="ocaml-base-compiler.${LP_OCAML_VERSION}"', '--packages="ocaml-base-compiler.5.2.0"')),
     r"FLOATING-TOOLCHAIN: .*(differs from the canonical|spells a version number)"),
    (R, "opam via install.sh in a workflow (review 2)",
     add(".github/workflows/zz.yml", job("ubuntu-24.04",
         steps='      - run: bash -c "sh <(curl -fsSL https://opam.ocaml.org/install.sh)"\n')),
     r"FLOATING-TOOLCHAIN: .*installs opam outside"),
    (R, "opam via apt-get in a workflow",
     add(".github/workflows/zz.yml", job("ubuntu-24.04", steps="      - run: sudo apt-get install -y opam\n")),
     r"FLOATING-TOOLCHAIN: .*installs opam outside"),
    # ── composite actions anywhere ──
    (R, "a composite under .github/actions/x/action.yaml (review 2)",
     add(".github/actions/x/action.yaml",
         "name: x\nruns:\n  using: composite\n  steps:\n    - uses: ocaml/setup-ocaml@v3\n"),
     r"FLOATING-TOOLCHAIN: \.github/actions/x/action\.yaml uses `ocaml/setup-ocaml@v3`"),
    (R, "a composite outside .github (review 2)",
     add("tools/act/action.yml",
         "name: x\nruns:\n  using: composite\n  steps:\n    - uses: ocaml/setup-ocaml@v3\n"),
     r"FLOATING-TOOLCHAIN: tools/act/action\.yml uses `ocaml/setup-ocaml@v3`"),
]


def run_gate(gate: Path, root: Path) -> tuple[int, str]:
    p = subprocess.run([sys.executable, str(gate), "--repo", str(root)],
                       capture_output=True, text=True)
    return p.returncode, p.stdout + p.stderr


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--gate", default=str(REPO / "scripts/tools/check_workflow_triggers.py"))
    gate = Path(ap.parse_args().gate).resolve()
    bad = 0
    with tempfile.TemporaryDirectory() as td:
        base = Path(td) / "base"
        shutil.copytree(REPO / ".github", base / ".github")
        rc, out = run_gate(gate, base)
        if rc != 0:
            print(f"[wt-killtests] FAIL: the unmutated tree does not PASS (rc={rc}); "
                  f"every result below would be vacuous\n{out}")
            return 1
        for i, (want, label, edit, rx) in enumerate(CASES):
            root = Path(td) / f"c{i}"
            shutil.copytree(base, root)
            if edit[0] == "add":
                (root / edit[1]).parent.mkdir(parents=True, exist_ok=True)
                (root / edit[1]).write_text(edit[2])
            else:
                f = root / edit[1]
                t = f.read_text()
                rot = False
                for old, new in edit[2]:
                    if t.count(old) != 1:
                        print(f"[wt-killtests] ROT: case '{label}': anchor occurs "
                              f"{t.count(old)} times in {edit[1]}")
                        rot = True
                        break
                    t = t.replace(old, new)
                if rot:
                    bad += 1
                    continue
                f.write_text(t)
            rc, out = run_gate(gate, root)
            if want == R:
                ok = rc == 1 and re.search(rx, out, re.S) is not None
            else:
                ok = rc == 0
            print(f"[wt-killtests] {'ok  ' if ok else 'FAIL'} {want} {label} (rc={rc})")
            if not ok:
                bad += 1
                print("    " + out.strip().replace("\n", "\n    ")[:1500])
    n = len(CASES)
    if bad:
        print(f"[wt-killtests] FAIL: {bad} of {n} case(s) had the wrong outcome")
        return 1
    print(f"[wt-killtests] PASS: {n} case(s) "
          f"({sum(c[0] == R for c in CASES)} refused, {sum(c[0] == A for c in CASES)} "
          f"accepted) against a clean tree that passes")
    return 0


if __name__ == "__main__":
    sys.exit(main())
