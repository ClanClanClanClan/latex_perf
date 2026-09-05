#!/usr/bin/env python3
"""Produce corpora/real_roots/proven_coverage_sample{1,2}.json — the inputs to
the North-Star metric published in PROJECT_STATE §1.

WHY THIS FILE EXISTS. The artefacts were committed before their producer was,
and they carried no provenance. The metric therefore had a silent failure
mode: change the CLI verdict strings and the published number freezes while
every gate stays green, because check_project_state.py regenerates the block
from the same stale artefacts. Committing the producer, pinning the parse to
the FROZEN state token, and stamping provenance closes that.

THE PARSE CONTRACT. The CLI prints one line:

    MODEL-CONNECTED \t <STATE> \t tier=<tier> \t <prose>

Field 2 is the frozen token owned by Compile_evidence.verdict_state_to_string
(PREMISE-CERTIFIED | PREMISE-INAPPLICABLE | PREMISE-REJECTED). Parse THAT.
Never regex the prose — that is what broke before.

The tokens say PREMISE, not PROVEN, deliberately: the capstone certifies its
premises over an abstract model, and measured against real documents that
certificate is wrong 6.7% of the time on the virgin sample 2 and 6.1% on
sample 1. Restricting to LP-Core does not reliably help (7.6% / 4.3%).
"""
import argparse
import hashlib
import json
import pathlib
import subprocess
import sys

STATES = {"PREMISE-CERTIFIED", "PREMISE-INAPPLICABLE", "PREMISE-REJECTED"}


def sha256_file(p: pathlib.Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def parse_verdict(out: str):
    """Return (state, tier) from the MODEL-CONNECTED line, or (None, None)."""
    for line in out.splitlines():
        if not line.startswith("MODEL-CONNECTED\t"):
            continue
        fields = line.split("\t")
        if len(fields) < 3:
            raise SystemExit(
                f"[gen-proven-coverage] FATAL: malformed verdict line "
                f"(expected >=3 tab fields): {line!r}")
        state = fields[1].strip()
        if state not in STATES:
            raise SystemExit(
                f"[gen-proven-coverage] FATAL: unknown state token {state!r}. "
                f"The vocabulary is owned by Compile_evidence.verdict_state; "
                f"if it changed, update STATES here IN THE SAME COMMIT.")
        tier = fields[2].strip()
        tier = tier[5:] if tier.startswith("tier=") else "unknown"
        return state, tier
    return None, None


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--results", required=True, help="results.json to join against")
    ap.add_argument("--out", required=True)
    ap.add_argument("--corpus", required=True)
    ap.add_argument("--cli", required=True)
    args = ap.parse_args()

    cli = pathlib.Path(args.cli)
    results = json.loads(pathlib.Path(args.results).read_text())
    rows = []
    for doc in results["docs"]:
        root = pathlib.Path(args.corpus) / doc["arxiv_id"] / doc["toplevel"]
        proc = subprocess.run([str(cli), "--compile-check", str(root)],
                              capture_output=True, text=True, timeout=300)
        state, tier = parse_verdict(proc.stdout + proc.stderr)
        if state is None:
            raise SystemExit(
                f"[gen-proven-coverage] FATAL: no MODEL-CONNECTED line for "
                f"{doc['arxiv_id']}; the CLI surface changed shape.")
        rows.append({
            "id": doc["arxiv_id"],
            "cell": doc["cell"],
            "ready": proc.returncode == 0,
            # `model` keeps the ARTEFACT vocabulary stable for consumers:
            # certified / inapplicable / rejected, mapped from the CLI token.
            "model": state.replace("PREMISE-", "").lower(),
            "profile": tier,
        })

    certified_ok = sum(1 for r in rows
                       if r["model"] == "certified" and r["cell"] == "true-READY")
    core_ok = sum(1 for r in rows
                  if r["model"] == "certified" and r["cell"] == "true-READY"
                  and r["profile"] == "lp-core")
    out = {
        "provenance": {
            "produced_by": "scripts/tools/gen_proven_coverage.py",
            "results_source": args.results,
            "cli_sha256": sha256_file(cli),
            "measured_at_sha": subprocess.run(
                ["git", "rev-parse", "HEAD"], capture_output=True, text=True
            ).stdout.strip(),
            "state_vocabulary": sorted(STATES),
        },
        "summary": {
            "n": len(rows),
            "premise_certified_and_compiles": certified_ok,
            "lp_core_certified_and_compiles": core_ok,
        },
        "rows": rows,
    }
    pathlib.Path(args.out).write_text(json.dumps(out, indent=1) + "\n")
    print(f"[gen-proven-coverage] {args.out}: {len(rows)} rows, "
          f"lp-core certified+compiles = {core_ok}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
