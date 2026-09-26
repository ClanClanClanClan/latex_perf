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
(PREMISE-CERTIFIED | PREMISE-REJECTED). Parse THAT. Never regex the prose —
that is what broke before.

C1 (2026-09-04) retired PREMISE-INAPPLICABLE. It meant "every premise bearing on
compilability holds, but the body defines some \\label twice", and the capstone
never takes that conjunct — so the token described the DECIDER's shape, not the
theorem's, and withheld the metric from 33 of 400 documents, 31 of which
compile. Certification is now keyed on exactly the capstone's hypotheses.

The tokens say PREMISE, not PROVEN, deliberately: the capstone certifies its
premises over an abstract model, and measured against real documents that
certificate is wrong on a few percent of them. The rate itself is GENERATED
into docs/v27/PROJECT_STATE.md from the artefacts this script writes — see
C-43 for why it is not restated in prose anywhere.
"""
import argparse
import hashlib
import json
import pathlib
import subprocess
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from _measurement_provenance import cli_platform  # noqa: E402

STATES = {"PREMISE-CERTIFIED", "PREMISE-REJECTED"}

# ADR-012 (M0). The CLI also prints one tier line AFTER the frozen token lines:
#
#     TIER \t <tier> \t <KIND> \t <human headline>
#
# Fields 2 and 3 are frozen tokens owned by latex-parse/src/verdict.ml
# (tier_token and kind_token). Only a PROVEN tier can yield the strict-tier
# (North-Star) numerator; in M0 no verdict is proven, so it is 0 by
# measurement, not by assertion.
TIERS = {"proven", "heuristic", "foreign"}
KINDS = {"PROVEN-READY", "PROVEN-NOT-READY", "PENDING", "LIKELY-OK",
         "LIKELY-FAIL", "FOREIGN"}


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


def parse_tier(out: str):
    """Return (tier, kind) from the TIER line, or (None, None)."""
    for line in out.splitlines():
        if not line.startswith("TIER\t"):
            continue
        fields = line.split("\t")
        if len(fields) < 4:
            raise SystemExit(
                f"[gen-proven-coverage] FATAL: malformed tier line "
                f"(expected >=4 tab fields): {line!r}")
        tier, kind = fields[1].strip(), fields[2].strip()
        if tier not in TIERS or kind not in KINDS:
            raise SystemExit(
                f"[gen-proven-coverage] FATAL: unknown tier/kind token "
                f"{tier!r}/{kind!r}. The vocabulary is owned by "
                f"latex-parse/src/verdict.ml; if it changed, update TIERS/KINDS "
                f"here IN THE SAME COMMIT.")
        if (tier == "proven") != kind.startswith("PROVEN-"):
            raise SystemExit(
                f"[gen-proven-coverage] FATAL: tier {tier!r} with kind {kind!r} "
                f"— only the proven tier may carry a PROVEN kind.")
        return tier, kind
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
        vtier, vkind = parse_tier(proc.stdout)
        if vtier is None:
            raise SystemExit(
                f"[gen-proven-coverage] FATAL: no TIER line for "
                f"{doc['arxiv_id']}; the CLI surface changed shape, or this "
                f"binary predates ADR-012 (M0).")
        rows.append({
            "id": doc["arxiv_id"],
            "cell": doc["cell"],
            "ready": proc.returncode == 0,
            # `model` keeps the ARTEFACT vocabulary stable for consumers:
            # certified / inapplicable / rejected, mapped from the CLI token.
            "model": state.replace("PREMISE-", "").lower(),
            "profile": tier,
            # ADR-012: the verdict tier. Only "proven" can count toward the
            # strict-tier North Star.
            "verdict_tier": vtier,
            "verdict_kind": vkind,
        })

    certified_ok = sum(1 for r in rows
                       if r["model"] == "certified" and r["cell"] == "true-READY")
    core_ok = sum(1 for r in rows
                  if r["model"] == "certified" and r["cell"] == "true-READY"
                  and r["profile"] == "lp-core")
    strict_ok = sum(1 for r in rows
                    if (r["verdict_kind"] == "PROVEN-READY"
                        and r["cell"] == "true-READY")
                    or (r["verdict_kind"] == "PROVEN-NOT-READY"
                        and r["cell"] == "true-NOT-READY"))
    strict_wrong = sum(1 for r in rows if r["verdict_tier"] == "proven") - strict_ok
    out = {
        "provenance": {
            "produced_by": "scripts/tools/gen_proven_coverage.py",
            "results_source": args.results,
            "cli_sha256": sha256_file(cli),
            # The hash is only comparable on this platform (C-64).
            "cli_platform": cli_platform(),
            "measured_at_sha": subprocess.run(
                ["git", "rev-parse", "HEAD"], capture_output=True, text=True
            ).stdout.strip(),
            # Engine source anchor (C-64). cli_sha256 above is a MACHINE-LOCAL
            # fact — CI builds ubuntu-22.04, this is produced by a macOS arm64
            # binary, and those sha256s can never agree — so it can never gate
            # anything in CI. This one can: it is git's own tree id for
            # latex-parse/src, identical on every platform.
            "src_tree_sha": subprocess.run(
                ["git", "rev-parse", "HEAD:latex-parse/src"],
                capture_output=True, text=True).stdout.strip() or None,
            "state_vocabulary": sorted(STATES),
            "tier_vocabulary": sorted(TIERS),
        },
        "summary": {
            "n": len(rows),
            "premise_certified_and_compiles": certified_ok,
            "lp_core_certified_and_compiles": core_ok,
            # ADR-012. A PROVEN verdict whose cell disagrees with pdflatex is
            # strict_wrong. The row-level cell carries READY/NOT-READY only, so
            # a wrong reason or location is not visible here; that is graded
            # by the strict battery and the generated differential.
            "strict_tier_matches_oracle": strict_ok,
            "strict_wrong": strict_wrong,
        },
        "rows": rows,
    }
    pathlib.Path(args.out).write_text(json.dumps(out, indent=1) + "\n")
    print(f"[gen-proven-coverage] {args.out}: {len(rows)} rows, "
          f"lp-core certified+compiles = {core_ok}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
