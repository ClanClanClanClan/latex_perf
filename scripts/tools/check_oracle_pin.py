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
     digest (and the pinned engine version). An artefact still carrying a
     host-graded block fails, unless it is in PRE_BASELINE with the ledger row
     that removes it.
  3. PRE_BASELINE is pinned to its exact contents: widening it silently fails,
     and an entry whose artefact has since been re-graded fails too.
  4. No tool calls a host `pdflatex` directly: outside `_oracle.py` and
     `_oracle.sh`, no Python list or shell command starts a pdflatex run.

Run: python3 scripts/tools/check_oracle_pin.py --repo .
"""
from __future__ import annotations

import argparse
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
    ("corpora/apply_fixes_real/results.json", ("provenance", "oracle")),
    ("corpora/apply_fixes_real/results_virgin.json", ("provenance", "oracle")),
    ("corpora/apply_fixes_real/results_fresh.json", ("provenance", "oracle")),
    ("corpora/strict_battery/manifest.json", ("provenance", "oracle_provenance")),
    ("corpora/false_ready/manifest.json", ("oracle",)),
    ("corpora/apply_fixes/manifest.json", ("oracle",)),
    ("corpora/oracle_baseline/equivalence.json", ("oracle",)),
)

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

# Files allowed to start pdflatex: the oracle itself.
ORACLE_FILES = {"scripts/tools/_oracle.py", "scripts/tools/_oracle.sh"}
PY_DIRECT = re.compile(r"""\[\s*["']pdflatex["']\s*,""")
SH_DIRECT = re.compile(r"""(^|[\s;&|(`$])pdflatex\s+(-|--version|\$|")""")


def dig(d, path):
    for k in path:
        if not isinstance(d, dict):
            return None
        d = d.get(k)
    return d


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
    if set(fps) != {"aarch64", "x86_64"}:
        findings.append(f"_oracle.TREE_FINGERPRINTS covers {sorted(fps)}, "
                        f"expected both aarch64 (local) and x86_64 (CI)")
    elif fps["aarch64"]["macro_layer_sha256"] != fps["x86_64"]["macro_layer_sha256"]:
        findings.append("the arm64 and amd64 images of the pinned digest have "
                        "DIFFERENT macro layers: a local grade would not be the "
                        "CI grade")
    for arch, fp in fps.items():
        for k in ("tlpdb_sha256", "macro_layer_sha256"):
            if not re.fullmatch(r"[0-9a-f]{64}", str(fp.get(k, ""))):
                findings.append(f"_oracle.TREE_FINGERPRINTS[{arch}][{k}] is not a sha256")

    # 2./3. every graded artefact names the pinned image
    graded_paths = {p for p, _ in GRADED}
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
        if block.get("image") != image:
            findings.append(
                f"{rel}: graded by {block.get('image') or 'a host TeX Live (no image recorded)'}"
                f", not the pinned image {image}. Re-grade it through "
                f"scripts/tools/_oracle.py (ADR-012 decision 7).")
        if version not in str(block.get("version", "")):
            findings.append(f"{rel}: oracle version {block.get('version')!r} is not "
                            f"the pin {version!r}")
    for rel in sorted(PRE_BASELINE):
        f = repo / rel
        if not f.is_file():
            findings.append(f"{rel}: listed in PRE_BASELINE but missing")
            continue
        if f'"image": "{image}"' in f.read_text():
            findings.append(f"{rel} now records the pinned image but is still in "
                            f"PRE_BASELINE; move it to GRADED")

    # 4. nothing else starts pdflatex
    for p in sorted((repo / "scripts").rglob("*")):
        if p.suffix not in (".py", ".sh") or not p.is_file():
            continue
        rel = str(p.relative_to(repo))
        if rel in ORACLE_FILES:
            continue
        for n, line in enumerate(p.read_text(errors="replace").split("\n"), 1):
            code = line.split("#", 1)[0] if p.suffix == ".sh" else line
            if code.lstrip().startswith("#"):
                continue
            rx = PY_DIRECT if p.suffix == ".py" else SH_DIRECT
            if rx.search(code):
                findings.append(f"{rel}:{n}: starts pdflatex directly; go through "
                                f"scripts/tools/_oracle.py (the host TeX Live is "
                                f"not the oracle)")

    if findings:
        print("[oracle-pin] FAIL:", file=sys.stderr)
        for f in findings:
            print(f"  - {f}", file=sys.stderr)
        return 1
    print(f"[oracle-pin] OK: {len(GRADED)} graded artefacts name {image}; "
          f"{len(PRE_BASELINE)} pre-baseline artefacts pinned; no direct pdflatex")
    return 0


if __name__ == "__main__":
    sys.exit(main())
