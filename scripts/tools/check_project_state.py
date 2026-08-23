#!/usr/bin/env python3
"""Gate: docs/v27/PROJECT_STATE.md must stay true.

PROJECT_STATE.md is the single source of truth for where this project is. The
failure mode it exists to prevent is the one that already happened to
docs/v27/ROADMAP.md: hand-typed numbers drifted until the banner, the
false-READY count, the over-rejection claim and the version-of-record were each
factually false -- while check_roadmap_facts.py printed "passed", because it
asserts only the numbers it knows about and uses re.search, so of two
contradictory matrices only the first was ever checked.

So this gate does not check numbers against a list it maintains. It REGENERATES
the measured-position block from the artefacts that own those numbers and diffs,
the same authenticity pattern check_release_integrity.py applies to
project_facts.yaml. A number in that block can only be wrong if its source is.

It also enforces the ledger discipline that makes the document usable across
sessions:
  * every open item has a unique, well-formed OPEN-nnn id (ids are never reused,
    so a PR can cite the item it closes);
  * every open item carries evidence and a size;
  * the corrections log is non-empty -- an empty §4 means either nothing was
    learned or nobody wrote it down, and the second is far likelier.

Exit 1 on any violation.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

DOC = Path("docs/v27/PROJECT_STATE.md")
GEN = Path("scripts/tools/gen_project_state.py")
BEGIN = "<!-- BEGIN GENERATED: measured-position -->"
END = "<!-- END GENERATED: measured-position -->"
MIN_OPEN = 10
MIN_CORRECTIONS = 5
# Commits touching latex-parse/src that may land before the real-paper
# measurement must be refreshed. Deliberately not 0: see C-13.
MAX_MEASUREMENT_LAG = 5


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", default=".")
    ns = ap.parse_args()
    repo = Path(ns.repo).resolve()
    doc = repo / DOC
    if not doc.is_file():
        print(f"FAIL: {DOC} is missing. It is the single source of truth; "
              f"the project does not have one without it.", file=sys.stderr)
        return 1

    text = doc.read_text()
    findings: list[str] = []

    # ── 1. the generated block must match its sources ────────────────────
    if BEGIN not in text or END not in text:
        print(f"FAIL: generated-block markers missing from {DOC}", file=sys.stderr)
        return 1
    committed = text.split(BEGIN, 1)[1].split(END, 1)[0]
    proc = subprocess.run([sys.executable, str(repo / GEN), "--repo", str(repo)],
                          capture_output=True, text=True)
    if proc.returncode != 0:
        print(f"FAIL: {GEN} exited {proc.returncode}\n{proc.stderr}", file=sys.stderr)
        return 1
    fresh = proc.stdout.split(BEGIN, 1)[1].split(END, 1)[0]
    if committed.strip() != fresh.strip():
        findings.append(
            "the measured-position block is STALE. A number in it disagrees with "
            "the artefact that owns it. Regenerate:\n"
            "      python3 scripts/tools/gen_project_state.py --repo . --write\n"
            "    Do not hand-edit the block -- if a number looks wrong, the SOURCE "
            "is wrong, and that is the bug worth finding.")

    # ── 2. ledger discipline ─────────────────────────────────────────────
    rows = re.findall(r"^\|\s*(OPEN-\d{3})\s*\|([^|]*)\|(.*)$", text, re.M)
    ids = [r[0] for r in rows]
    if len(ids) < MIN_OPEN:
        findings.append(f"only {len(ids)} OPEN items; expected at least {MIN_OPEN}. "
                        f"An almost-empty ledger means it stopped being maintained, "
                        f"not that the work is done.")
    dupes = {i for i in ids if ids.count(i) > 1}
    if dupes:
        findings.append(f"duplicate OPEN ids {sorted(dupes)} — ids are never reused, "
                        f"because PRs cite them.")
    KNOWN = {"SOUND", "OVERREJ", "INSTR", "HONEST", "GATE", "TRACK"}
    for oid, cls, rest in rows:
        c = cls.strip().replace("*", "")
        if c not in KNOWN:
            findings.append(f"{oid}: class {c!r} is not one of {sorted(KNOWN)}")
        # A markdown row ends with a trailing "|", so the split yields an empty
        # final cell. Drop it before indexing from the right.
        cells = [x.strip() for x in rest.split("|")]
        while cells and cells[-1] == "":
            cells.pop()
        if len(cells) < 3 or not cells[-2]:
            findings.append(f"{oid}: no evidence cell — every item must say how it "
                            f"is known, or be marked UNVERIFIED")
        if len(cells) < 3 or cells[-1] not in {"S", "M", "L", "XL"}:
            findings.append(f"{oid}: size must be one of S/M/L/XL, got "
                            f"{cells[-1] if cells else '(none)'!r}")

    # ── 2b. the MEASUREMENT itself must not be silently stale ────────────
    #
    # The generated block is checked against its source, but nothing checked
    # whether the SOURCE was current. It went three PRs stale while this gate
    # passed, publishing 56.8% when main measured 65.8% — the block correctly
    # matched a results.json that was simply out of date.
    #
    # This cannot re-measure (CI has no corpus, by design — it is 12 GB of
    # non-redistributable arXiv source), so it checks PROVENANCE: results.json
    # records the sha it was measured at, and this counts commits touching
    # latex-parse/src since then.
    #
    # It is a RATCHET, not a treadmill. Failing on every source change would
    # train people to refresh without reading, which is the failure mode C-13
    # records. The threshold allows normal churn and stops long-term decay.
    rr = repo / "corpora/real_roots/results.json"
    if rr.is_file():
        # Catch only what can genuinely go wrong with reading a JSON file. A
        # bare `except Exception` here swallowed a NameError (json was not
        # imported) and reported "no measured_at_sha" — a WRONG diagnostic that
        # sent me looking at the data instead of the code. A broad except turns
        # a programming error into a plausible-looking finding.
        try:
            sha = json.loads(rr.read_text()).get("measured_at_sha")
        except (json.JSONDecodeError, OSError) as exc:
            findings.append(f"corpora/real_roots/results.json is unreadable: {exc}")
            sha = "unreadable"
        if not sha:
            findings.append(
                "corpora/real_roots/results.json has no measured_at_sha, so its "
                "staleness cannot be checked. Refresh with:\n"
                "      python3 scripts/tools/diff_real_roots.py --repo . --refresh-cli")
        else:
            r = subprocess.run(
                ["git", "--no-optional-locks", "rev-list", "--count",
                 f"{sha}..HEAD", "--", "latex-parse/src"],
                cwd=repo, capture_output=True, text=True)
            if r.returncode == 0 and r.stdout.strip().isdigit():
                behind = int(r.stdout.strip())
                if behind > MAX_MEASUREMENT_LAG:
                    findings.append(
                        f"the real-paper measurement is {behind} commits behind "
                        f"HEAD on latex-parse/src (limit {MAX_MEASUREMENT_LAG}). "
                        f"The published position is probably wrong. Refresh:\n"
                        f"      python3 scripts/tools/diff_real_roots.py --repo . "
                        f"--refresh-cli\n"
                        f"    A CLI-only refresh is valid while the corpus and "
                        f"engine are unchanged — it asserts both.")

    # ── 3. the corrections log must not be empty ─────────────────────────
    m = re.search(r"^##\s*4\..*?corrections log.*?$(.*?)^##\s", text,
                  re.M | re.S | re.I)
    n_corr = len(re.findall(r"^\|\s*C-\d+\s*\|", m.group(1), re.M)) if m else 0
    if n_corr < MIN_CORRECTIONS:
        findings.append(f"corrections log has {n_corr} entries, expected at least "
                        f"{MIN_CORRECTIONS}. This section is the point of the "
                        f"document; an empty one means nobody wrote down what was "
                        f"learned.")

    if findings:
        print(f"[project-state] FAIL: {len(findings)} problem(s)", file=sys.stderr)
        for f in findings:
            print(f"  - {f}", file=sys.stderr)
        return 1

    print(f"[project-state] PASS: generated block matches its sources; "
          f"{len(ids)} open items with ids/evidence/sizes; "
          f"{n_corr} corrections recorded")
    return 0


if __name__ == "__main__":
    sys.exit(main())
