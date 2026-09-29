#!/usr/bin/env python3
"""The states of `_measurement_provenance.check_cli_sha256`, each in its own
direction (C-68, C-72). Run it before trusting a change to that function.

A three-state check verified only at its two endpoints passed two broken
versions of this arm; this file checks every state separately, and asserts the
KIND of each outcome (failure, note, silence), not merely that something
happened.

    same platform, same build root, same source, different hash -> FAILURE
    same platform, same build root, same source, same hash      -> silent
    same platform, same build root, MOVED source                -> note
    same platform, OTHER build root                             -> note
    same platform, NO build root (legacy artefact)              -> note
    OTHER platform                                              -> note
    no built CLI                                                -> note
    no recorded hash                                            -> silent
"""
import pathlib
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import _measurement_provenance as mp  # noqa: E402

REPO = HERE.parent.parent
HEAD_TREE = subprocess.run(
    ["git", "--no-optional-locks", "rev-parse", "HEAD:latex-parse/src"],
    cwd=REPO, capture_output=True, text=True).stdout.strip()
assert HEAD_TREE, "cannot read HEAD:latex-parse/src"
HERE_ROOT = mp.build_root_fingerprint(REPO)
OTHER_ROOT = mp.build_root_fingerprint("/nonexistent/other-checkout")
PLAT = mp.cli_platform()
OTHER_PLAT = "Plan9-mips" if PLAT != "Plan9-mips" else "Darwin-arm64"
A, B = "a" * 64, "b" * 64
MOVED = "0" * 40

fails = 0


def case(name, expect, **kw):
    global fails
    args = dict(recorded_cli=A, built_cli=B, src_tree_sha=HEAD_TREE,
                recorded_platform=PLAT, recorded_build_root=HERE_ROOT)
    args.update(kw)
    findings, notes = mp.check_cli_sha256(REPO, "artefact", "howto", **args)
    got = "fail" if findings else ("note" if notes else "silent")
    ok = got == expect and not (findings and notes)
    print(f"{'ok  ' if ok else 'FAIL'} {name}: expected {expect}, got {got}")
    if not ok:
        fails += 1


case("same root, same source, different hash", "fail")
case("same root, same source, same hash", "silent", built_cli=A)
case("same root, moved source", "note", src_tree_sha=MOVED)
case("other build root", "note", recorded_build_root=OTHER_ROOT)
case("legacy artefact without a build root", "note", recorded_build_root=None)
case("other platform", "note", recorded_platform=OTHER_PLAT)
case("other platform AND other root", "note", recorded_platform=OTHER_PLAT,
     recorded_build_root=OTHER_ROOT)
case("no built CLI", "note", built_cli=None)
case("no recorded hash", "silent", recorded_cli=None)

# The producer's fingerprint of a CLI under <root>/_build is the gate's
# fingerprint of <root>: the two sides must agree for the failure arm to live.
cli = REPO / "_build/default/latex-parse/src/validators_cli.exe"
if mp.cli_build_root(cli) != HERE_ROOT:
    print("FAIL cli_build_root(<repo>/_build/...) != build_root_fingerprint(repo)")
    fails += 1
else:
    print("ok   producer and gate fingerprints agree for this checkout")
# A different spelling of the same directory must give the same fingerprint.
if mp.build_root_fingerprint(REPO / "scripts" / "..") != HERE_ROOT:
    print("FAIL the fingerprint depends on how the path is spelled")
    fails += 1
else:
    print("ok   the fingerprint is of the resolved path")

# built_cli_path: "this build root" is the binary's own, symlinks resolved.
# A checkout whose _build is a symlink into THIS checkout's _build (the
# isolated copies of check_gate_selftests) must reach the failure arm exactly
# as this checkout does; a binary under another root must stay a note.
import tempfile  # noqa: E402

with tempfile.TemporaryDirectory() as td:
    other = pathlib.Path(td).resolve() / "copy"
    (other / "_build/default/latex-parse/src").mkdir(parents=True)
    linked = other / "_build/default/latex-parse/src/validators_cli.exe"
    linked.write_bytes(b"")
    case("binary built in another root (by path)", "note",
         built_cli_path=linked)
    case("binary under a real _build of this root (by path)", "fail",
         built_cli_path=REPO / "_build/default/latex-parse/src/validators_cli.exe")
    via = other / "via"
    via.mkdir()
    (via / "_build").symlink_to(REPO / "_build")
    case("_build symlinked into this checkout's _build (by path)", "fail",
         built_cli_path=via / "_build/default/latex-parse/src/validators_cli.exe")
    findings, notes = mp.check_cli_sha256(
        via, "artefact", "howto", recorded_cli=A, built_cli=B,
        src_tree_sha=HEAD_TREE, recorded_platform=PLAT,
        recorded_build_root=HERE_ROOT)
    ok = bool(notes) and not findings
    print(f"{'ok  ' if ok else 'FAIL'} without built_cli_path the gate keeps "
          f"the directory comparison: expected note, got "
          f"{'fail' if findings else ('note' if notes else 'silent')}")
    fails += not ok

print(f"{'PASS' if not fails else 'FAILED'}: {fails} failing case(s)")
sys.exit(1 if fails else 0)
