#!/usr/bin/env python3
"""Monotone false-READY regression gate (R7-INFRA-1).

Runs `validators_cli --compile-check` on every fixture in
corpora/false_ready/manifest.json and compares the verdict to the recorded
`expected_cli`. NO pdflatex is needed at gate time: the pdflatex ground truth is
baked into the manifest (verified locally by scripts/tools/false_ready_oracle.sh),
so this runs in CI wherever the CLI is built.

Every fixture is a document pdflatex rejects under the strict READY oracle. At
baseline each has expected_cli=READY (a LIVE false-READY). Each round-7 fix PR
flips the entries it fixes to expected_cli=NOT-READY (and lowers the baseline).

The gate FAILS on either direction of drift, so a false-READY can never ship or
regress unnoticed:
  * REGRESSION  — a fixture recorded as fixed (expected NOT-READY) is READY again.
  * UNRECORDED  — a fixture recorded as live (expected READY) is now NOT-READY:
                  a real fix landed; update the manifest to lock it in.

Usage: check_known_false_ready.py [--repo DIR] [--cli PATH]
Exit 0 = clean; 1 = drift (with per-fixture detail); 2 = harness error.
"""
import argparse, json, os, subprocess, sys


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=".")
    ap.add_argument("--cli", default=None,
                    help="path to validators_cli.exe (default: _build/default/...)")
    args = ap.parse_args()
    repo = os.path.abspath(args.repo)
    cli = args.cli or os.path.join(
        repo, "_build/default/latex-parse/src/validators_cli.exe")
    frdir = os.path.join(repo, "corpora/false_ready")
    manifest_path = os.path.join(frdir, "manifest.json")

    if not os.path.exists(manifest_path):
        print(f"[known-false-ready] ERROR: manifest not found: {manifest_path}")
        return 2
    if not (os.path.exists(cli) and os.access(cli, os.X_OK)):
        print(f"[known-false-ready] ERROR: CLI not built/executable: {cli}\n"
              f"  build it first: dune build latex-parse/src/validators_cli.exe")
        return 2

    with open(manifest_path) as fh:
        manifest = json.load(fh)
    fixtures = manifest["fixtures"]

    regressions, unrecorded = [], []
    overrej_regressions, unrecorded_rescues = [], []
    live, fixed, accept_pins, overrej_pins = 0, 0, 0, 0
    for fx in fixtures:
        root = os.path.join(frdir, fx["path"])
        if not os.path.exists(root):
            print(f"[known-false-ready] ERROR: fixture missing: {fx['path']}")
            return 2
        # --compile-check exits 0 = READY, 1 = NOT-READY.
        rc = subprocess.run([cli, "--compile-check", root],
                            capture_output=True).returncode
        actual = "READY" if rc == 0 else "NOT-READY"
        expected = fx["expected_cli"]
        if fx.get("pdflatex") == "compiles":
            # pdflatex ACCEPTS these fixtures: the row pins the OVER-REJECTION
            # direction (OPEN-007 rescue targets), so READY is the CORRECT
            # verdict and the failure mode is the REVERSE of the classes below.
            # A NOT-READY against expected READY is a rescue REGRESSION -
            # never an "unrecorded fix" to lock in.
            if actual == "READY" and expected == "READY":
                accept_pins += 1
            elif actual == "NOT-READY" and expected == "NOT-READY":
                overrej_pins += 1  # pinned, rescue not yet shipped
            elif actual == "NOT-READY" and expected == "READY":
                overrej_regressions.append(fx["id"])
            else:  # READY vs expected NOT-READY: a rescue landed unrecorded
                unrecorded_rescues.append(fx["id"])
        elif actual == "READY" and expected == "READY":
            live += 1
        elif actual == "NOT-READY" and expected == "NOT-READY":
            fixed += 1
        elif actual == "READY" and expected == "NOT-READY":
            regressions.append(fx["id"])
        else:  # NOT-READY vs expected READY
            unrecorded.append(fx["id"])

    total = len(fixtures)
    print(f"[known-false-ready] fixtures={total}  live-false-READY={live}  "
          f"fixed={fixed}  accept-pins={accept_pins}  overrej-pins={overrej_pins}  (baseline live={manifest['baseline']['false_ready_total']})")

    if regressions:
        print("[known-false-ready] FAIL — REGRESSION (a fixed false-READY is READY again):")
        for i in regressions:
            print(f"    {i}: expected NOT-READY, got READY")
    if unrecorded:
        print("[known-false-ready] FAIL — UNRECORDED FIX (fixture now NOT-READY; "
              "lock it in by setting expected_cli=NOT-READY in the manifest and "
              "lowering baseline.false_ready_total):")
        for i in unrecorded:
            print(f"    {i}: expected READY, got NOT-READY")

    if overrej_regressions:
        print("[known-false-ready] FAIL — OVER-REJECTION REGRESSION (the CLI "
              "again rejects a document pdflatex compiles; the rescue "
              "regressed):")
        for i in overrej_regressions:
            print(f"    {i}: expected READY (pdflatex compiles), got NOT-READY")
    if unrecorded_rescues:
        print("[known-false-ready] FAIL — UNRECORDED RESCUE (a compiles-graded "
              "fixture is now READY; lock it in by setting expected_cli=READY "
              "in the manifest):")
        for i in unrecorded_rescues:
            print(f"    {i}: expected NOT-READY, got READY (pdflatex compiles)")
    if regressions or unrecorded or overrej_regressions or unrecorded_rescues:
        return 1
    # Cross-check the human-facing baseline stays consistent with the entries.
    if live != manifest["baseline"]["false_ready_total"]:
        print(f"[known-false-ready] FAIL — baseline.false_ready_total="
              f"{manifest['baseline']['false_ready_total']} disagrees with "
              f"{live} entries whose expected_cli=READY; reconcile the manifest.")
        return 1
    print("[known-false-ready] PASS — no false-READY regression; "
          "known set unchanged.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
