#!/usr/bin/env python3
"""Kill-tests for check_workflow_triggers.py failure modes 6, 7 and 8.

Each case copies the repo's .github into a temp dir, plants ONE edit, runs the
gate there, and requires the expected outcome: a REFUSE case must exit 1 with
its finding; an ACCEPT case (a near-miss that is legitimately fine) must exit
0. The clean copy must PASS first, or every REFUSE result would be vacuous.
The cases include the 2026-11-03 review's mutations of C-176/C-177 (a
`runs-on` group whose `labels:` is a plain string, matrix.cfg.os, inputs.os,
fromJSON, a *.yaml workflow, setup-ocaml v2 pinned by SHA, actions/cache by
minor version) — each one PASSED the gate as first written.

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
CACHE_V430_SHA = "0057852bfaa89a56745cba8c7296529d2fc39830"


def job(runs_on: str, extra: str = "", steps: str = "      - run: echo hi\n") -> str:
    return ("name: planted\non: workflow_dispatch\njobs:\n  planted:\n"
            f"    runs-on: {runs_on}\n{extra}    steps:\n{steps}")


def add(name: str, text: str):
    return ("add", name, text)


def sub(name: str, old: str, new: str):
    return ("sub", name, old, new)


R, A = "REFUSE", "ACCEPT"
CASES = [
    # ── mode 7: runner labels ──
    (R, "runs-on group with a string labels: (review zz.yml)",
     add(".github/workflows/zz.yml", job("\n      group: big\n      labels: ubuntu-latest")),
     r"FLOATING-RUNNER: .*zz\.yml job 'planted' runs on `ubuntu-latest`"),
    (R, "runs-on group with a list of labels",
     add(".github/workflows/zz.yml", job("\n      group: big\n      labels: [self-hosted, ubuntu-latest]")),
     r"FLOATING-RUNNER: .*runs on `ubuntu-latest`"),
    (R, "matrix.cfg.os (nested matrix value)",
     add(".github/workflows/zz.yml", job("${{ matrix.cfg.os }}",
         "    strategy:\n      matrix:\n        cfg: [{os: ubuntu-latest}]\n")),
     r"FLOATING-RUNNER: .*an expression this gate cannot resolve"),
    (R, "inputs.os with a -latest default",
     add(".github/workflows/zz.yml",
         "name: planted\non:\n  workflow_dispatch:\n    inputs:\n      os:\n        default: ubuntu-latest\n"
         "jobs:\n  planted:\n    runs-on: ${{ inputs.os }}\n    steps:\n      - run: echo hi\n"),
     r"FLOATING-RUNNER: .*inputs\.os"),
    (R, "fromJSON runner label",
     add(".github/workflows/zz.yml", job("${{ fromJSON('[\"ubuntu-latest\"]') }}")),
     r"FLOATING-RUNNER: .*fromJSON"),
    (R, "matrix.os over a literal list containing ubuntu-latest",
     add(".github/workflows/zz.yml", job("${{ matrix.os }}",
         "    strategy:\n      matrix:\n        os: [ubuntu-24.04, ubuntu-latest]\n")),
     r"FLOATING-RUNNER: .*runs on `ubuntu-latest`"),
    (A, "matrix.os over pinned literals",
     add(".github/workflows/zz.yml", job("${{ matrix.os }}",
         "    strategy:\n      matrix:\n        os: [ubuntu-24.04, ubuntu-24.04-arm]\n")),
     None),
    (R, "a *.yaml workflow on ubuntu-latest",
     add(".github/workflows/zz.yaml", job("ubuntu-latest")),
     r"FLOATING-RUNNER: .*zz\.yaml"),
    # ── mode 6: cache clients ──
    (R, "actions/cache@v4.1.0 (below 4.2.0)",
     add(".github/workflows/zz.yml", job("ubuntu-24.04", steps="      - uses: actions/cache@v4.1.0\n")),
     r"LEGACY-CACHE: .*actions/cache@v4\.1\.0"),
    (R, "actions/cache@v3.3.3 (below 3.4.0)",
     add(".github/workflows/zz.yml", job("ubuntu-24.04", steps="      - uses: actions/cache/restore@v3.3.3\n")),
     r"LEGACY-CACHE: .*actions/cache/restore@v3\.3\.3"),
    (R, "actions/cache@v2",
     add(".github/workflows/zz.yml", job("ubuntu-24.04", steps="      - uses: actions/cache@v2\n")),
     r"LEGACY-CACHE: .*actions/cache@v2"),
    (R, "actions/cache pinned by SHA with no version comment",
     sub(COMPOSITE, f"actions/cache/restore@{CACHE_V430_SHA} # v4.3.0",
         f"actions/cache/restore@{CACHE_V430_SHA}"),
     r"LEGACY-CACHE: .*a SHA with no `# vX\.Y\.Z` comment"),
    (A, "actions/cache@v3.4.0",
     add(".github/workflows/zz.yml", job("ubuntu-24.04", steps="      - uses: actions/cache@v3.4.0\n")),
     None),
    (A, "actions/cache@v3 (bare major resolves to 3.4.x)",
     add(".github/workflows/zz.yml", job("ubuntu-24.04", steps="      - uses: actions/cache@v3\n")),
     None),
    (R, "a uses: in flow style the line scan cannot see",
     add(".github/workflows/zz.yml", job("ubuntu-24.04", steps="      - {uses: actions/cache@v1}\n")),
     r"UNSCANNED-USES: .*zz\.yml"),
    # ── mode 8: toolchains ──
    (R, "setup-ocaml v2 pinned by SHA",
     add(".github/workflows/zz.yml", job("ubuntu-24.04",
         steps=f"      - uses: ocaml/setup-ocaml@{SETUP_OCAML_V2_SHA} # v2.2.10\n")),
     r"FLOATING-TOOLCHAIN: .*ocaml/setup-ocaml@8cc6339f"),
    (R, "setup-ocaml v3.9.0 by tag",
     add(".github/workflows/zz.yml", job("ubuntu-24.04", steps="      - uses: ocaml/setup-ocaml@v3.9.0\n")),
     r"FLOATING-TOOLCHAIN: .*ocaml/setup-ocaml@v3\.9\.0"),
    (R, "dtolnay/rust-toolchain@stable",
     add(".github/workflows/zz.yml", job("ubuntu-24.04", steps="      - uses: dtolnay/rust-toolchain@stable\n")),
     r"FLOATING-TOOLCHAIN: .*dtolnay/rust-toolchain@stable"),
    (R, "opam pin loosened to a minor version",
     sub(COMPOSITE, 'OPAM_VERSION: "2.6.1"', 'OPAM_VERSION: "2.6"'),
     r"FLOATING-TOOLCHAIN: .*exactly one `OPAM_VERSION"),
    (R, "opam arm64 checksum dropped",
     sub(COMPOSITE, "        OPAM_SHA256_ARM64:", "        OPAM_SHA_ARM64:"),
     r"FLOATING-TOOLCHAIN: .*sha256 for both X64 and ARM64"),
    (R, "opam checksum never checked",
     sub(COMPOSITE, "| sha256sum -c -", "| cat"),
     r"FLOATING-TOOLCHAIN: .*never checks the opam binary"),
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
                (root / edit[1]).write_text(edit[2])
            else:
                f = root / edit[1]
                t = f.read_text()
                if t.count(edit[2]) != 1:
                    print(f"[wt-killtests] ROT: case '{label}': anchor occurs "
                          f"{t.count(edit[2])} times in {edit[1]}")
                    bad += 1
                    continue
                f.write_text(t.replace(edit[2], edit[3]))
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
