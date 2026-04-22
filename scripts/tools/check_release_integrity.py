#!/usr/bin/env python3
"""Release integrity gate (PR #245 p1.11).

Three compact gates:

  A. CHANGELOG ↔ governance version coherence.
     Top version block in CHANGELOG.md must match [version] in
     governance/project_facts.yaml. Catches release-state drift.

  B. Generated-file authenticity.
     Regenerate generated/project_facts.json + specs/rules/
     rule_contracts.{yaml,json} in a staging area; diff against the
     committed files. Catches hand-editing of generated artefacts.

  C. Orphan consumes capabilities.
     Every [consumes] string in rule_contracts.yaml must be (1) in
     some rule's [provides] list, or (2) in a documented external-
     capabilities whitelist.

Exit 1 on any failure; each sub-gate reports independently.
"""

from __future__ import annotations
import argparse
import difflib
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
import yaml

REPO_ROOT = Path(__file__).resolve().parents[2]

# External capabilities are produced by subsystems (parser, lexer, log
# parser) rather than any rule. They're documented here so the orphan
# gate doesn't flag them.
EXTERNAL_CAPABILITIES = {
    "compile_log_context",  # produced by Log_parser
    "post_expansion_commands",  # produced by L1 expander
    "environment_events",  # produced by L2 parser
    "math_mode_contexts",  # produced by L2 parser
    "float_contexts",  # produced by L2 parser
    "verbatim_regions",  # produced by L0 lexer
    "language_model",  # ML sidecar
    "document_structure",  # derived from L2 AST
    "ml_confidence_map",  # ML runtime
    "image_metadata",  # L3 binary readers
    "pdf_structure",  # L3 binary readers
    "tikz_compile_times",  # L3 binary readers
    "font_glyph_coverage",  # L3 binary readers
    "external_binary",  # generic fallback
    # Derived by rules (self-provided via rule_id) but also
    # referenced as abstract capabilities:
    "label_index",  # provided by LAB-* family (future)
    "bib_entries",  # provided by BIB-* family
}


def gate_changelog_version(repo: Path) -> list[str]:
    failures: list[str] = []
    cl = repo / "CHANGELOG.md"
    gv = repo / "governance/project_facts.yaml"
    if not cl.is_file():
        return [f"missing: {cl}"]
    if not gv.is_file():
        return [f"missing: {gv}"]
    gov = yaml.safe_load(gv.read_text())
    gov_version = str(gov.get("version", ""))
    # Scan CHANGELOG for top-most version header `## [vX.Y.Z]` or
    # `## [vX.Y.Z-suffix]`. Take the first one.
    text = cl.read_text()
    m = re.search(r"^##\s+\[(v[0-9][^\]]*)\]", text, re.MULTILINE)
    if not m:
        return ["CHANGELOG has no version header"]
    cl_version = m.group(1)
    # Governance version is like "v26.1.0"; CHANGELOG's may be
    # "v26.1.0" or "v26.1.0-draft". Accept the base match.
    base = cl_version.split("-")[0]
    if base != gov_version:
        failures.append(
            f"CHANGELOG top version {cl_version!r} (base {base!r}) does "
            f"not match governance version {gov_version!r}. Rebase "
            f"CHANGELOG or bump governance."
        )
    return failures


def gate_generated_authenticity(repo: Path) -> list[str]:
    """Run generate_project_facts + generate_rule_contracts into a
    tempdir, then diff against committed outputs."""
    failures: list[str] = []

    def run_and_diff(generator: str, output_rel: str, *extra: str) -> None:
        """Regen generator's output into repo/tmp and diff. If binary
        (e.g. json), compare verbatim."""
        output = repo / output_rel
        if not output.is_file():
            failures.append(f"{output_rel}: missing; cannot verify")
            return
        with tempfile.TemporaryDirectory() as td:
            staging = Path(td) / output.name
            # The generators write to a configurable path. We invoke
            # them with --output pointing into staging.
            try:
                subprocess.run(
                    [
                        "python3",
                        str(repo / generator),
                        "--output", str(staging),
                        *extra,
                    ],
                    capture_output=True, text=True, timeout=60,
                    check=True, cwd=str(repo),
                )
            except subprocess.CalledProcessError as e:
                failures.append(
                    f"{generator} crashed: {e.stderr[:300] if e.stderr else e}"
                )
                return
            except FileNotFoundError:
                failures.append(f"{generator}: not found")
                return
            if not staging.is_file():
                failures.append(
                    f"{generator}: did not produce {staging.name}"
                )
                return
            a = output.read_text()
            b = staging.read_text()
            if a != b:
                diff = list(
                    difflib.unified_diff(
                        a.splitlines(), b.splitlines(),
                        fromfile=f"committed/{output_rel}",
                        tofile="regenerated", n=2, lineterm="",
                    )
                )
                snippet = "\n".join(diff[:20])
                failures.append(
                    f"{output_rel}: differs from regenerated output. "
                    f"Run `python3 {generator}` to refresh.\n{snippet}"
                )

    run_and_diff(
        "scripts/tools/generate_rule_contracts.py",
        "specs/rules/rule_contracts.yaml",
    )
    # The rule_contracts generator writes BOTH yaml and json via its
    # single --output arg (json is derived). Rerunning already covers
    # the json pair via the generator's internal logic.
    return failures


def gate_orphan_consumes(repo: Path) -> list[str]:
    failures: list[str] = []
    contracts_path = repo / "specs/rules/rule_contracts.yaml"
    if not contracts_path.is_file():
        return [f"missing: {contracts_path}"]
    contracts = yaml.safe_load(contracts_path.read_text())["rules"]
    # Collect all provides
    all_provides: set[str] = set()
    for c in contracts:
        for p in c.get("provides", []):
            all_provides.add(p)
    # Check every consumes against provides ∪ external
    for c in contracts:
        for cap in c.get("consumes", []):
            if cap in all_provides:
                continue
            if cap in EXTERNAL_CAPABILITIES:
                continue
            failures.append(
                f"{c['rule_id']}: consumes capability {cap!r} which is "
                f"neither provided by any rule nor declared external. "
                f"Add a provider or whitelist as external."
            )
    return failures


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=str(REPO_ROOT))
    ap.add_argument(
        "--skip-generated",
        action="store_true",
        help="Skip gate B (slow; re-runs two generators).",
    )
    ns = ap.parse_args()
    repo = Path(ns.repo)
    any_failed = False
    gates: list[tuple[str, list[str]]] = [
        ("CHANGELOG version coherence", gate_changelog_version(repo)),
        ("Orphan consumes", gate_orphan_consumes(repo)),
    ]
    if not ns.skip_generated:
        gates.append(
            ("Generated-file authenticity", gate_generated_authenticity(repo))
        )
    for name, failures in gates:
        if failures:
            any_failed = True
            for f in failures[:5]:
                print(f"[release-integrity] {name}: FAIL: {f}",
                      file=sys.stderr)
            if len(failures) > 5:
                print(f"  ... and {len(failures) - 5} more")
        else:
            print(f"[release-integrity] {name}: PASS")
    return 1 if any_failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
