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
import hashlib
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
            rr_data = json.loads(rr.read_text())
            sha = rr_data.get("measured_at_sha")
        except (json.JSONDecodeError, OSError) as exc:
            findings.append(f"corpora/real_roots/results.json is unreadable: {exc}")
            sha, rr_data = "unreadable", None

        # ── CLAIM PROVENANCE: a published protocol must be recomputable from
        # per-row data in the same artefact. results.json once advertised
        # "up to 3 passes" while 182 of 200 rows had pdflatex_passes: null —
        # the protocol had been applied to 18 rows (C-28). The repair made
        # --repass write "APPLIED TO k/n" into the protocol string; THIS check
        # makes that claim binding: k and n are recomputed from the rows and a
        # mismatch fails. A protocol with no APPLIED-TO clause claims the full
        # protocol for every row, so every graded row must then carry a
        # pdflatex_passes count.
        if rr_data is not None:
            proto = (rr_data.get("oracle") or {}).get("protocol", "")
            docs = rr_data.get("docs") or []
            with_passes = sum(1 for d in docs if d.get("pdflatex_passes"))
            m = re.search(r"APPLIED TO (\d+)/(\d+) rows", proto)
            if m:
                k, n = int(m.group(1)), int(m.group(2))
                if k != with_passes or n != len(docs):
                    findings.append(
                        f"results.json protocol claims 'APPLIED TO {k}/{n}' but "
                        f"the rows say {with_passes}/{len(docs)} — the published "
                        f"claim does not match the recorded measurement")
            elif "passes" in proto and docs and with_passes < len(docs):
                findings.append(
                    f"results.json protocol claims multi-pass wholesale but only "
                    f"{with_passes}/{len(docs)} rows carry pdflatex_passes — "
                    f"either re-measure the rest or scope the claim with an "
                    f"'APPLIED TO k/n rows' clause")
    # ── 2c. EVERY artefact the block reads must be fresh, not just one ───
    #
    # OPEN-080 / C-47. Until 2026-09-12 the ratchet above pointed at
    # results.json ALONE. The generated block reads four artefacts, and the
    # two it did not watch are the ones that produce the North-Star metric:
    # proven_coverage_sample{1,2}.json were 13 and 14 commits behind HEAD on
    # latex-parse/src, against this same limit of 5, and no check_* script
    # read them at all. Their cli_sha256 was compared to nothing, so the
    # staleness was also provable directly: both had been produced by a
    # binary that no longer existed.
    #
    # The rule this now encodes (C-47): a gate that reads one of N artefacts
    # owning a published number must NAME the other N-1 and say why they are
    # excluded. Hence the explicit list, and the pinned exclusion below.
    ARTEFACTS = (
        ("corpora/real_roots/results.json", ("measured_at_sha",),
         "python3 scripts/tools/diff_real_roots.py --repo . --refresh-cli"),
        ("corpora/real_roots/results_sample2.json", ("measured_at_sha",),
         "OPEN-081: this artefact has no producer in-repo"),
        ("corpora/real_roots/proven_coverage_sample1.json",
         ("provenance", "measured_at_sha"),
         "python3 scripts/tools/gen_proven_coverage.py --results "
         "corpora/real_roots/results.json --out "
         "corpora/real_roots/proven_coverage_sample1.json --corpus $LP_REAL_CORPUS "
         "--cli _build/default/latex-parse/src/validators_cli.exe"),
        ("corpora/real_roots/proven_coverage_sample2.json",
         ("provenance", "measured_at_sha"),
         "python3 scripts/tools/gen_proven_coverage.py --results "
         "corpora/real_roots/results_sample2.json --out "
         "corpora/real_roots/proven_coverage_sample2.json --corpus $LP_REAL_CORPUS "
         "--cli _build/default/latex-parse/src/validators_cli.exe"),
    )
    # Artefacts that CANNOT yet carry provenance, each with the ledger row that
    # removes it. Pinned to its exact size: adding a new unwatched artefact, or
    # quietly widening this set, fails the gate. Removing an entry here without
    # the artefact gaining a sha also fails, in the loop below.
    NO_PROVENANCE_YET = {
        "corpora/real_roots/results_sample2.json":
            "OPEN-081 — measured_at_sha is null and NO script in the repo "
            "writes this file; the sha cannot be stamped honestly until the "
            "producer exists. Do not hand-stamp it: a guessed provenance is "
            "worse than a declared absence.",
    }
    if len(NO_PROVENANCE_YET) != 1:
        findings.append(
            f"NO_PROVENANCE_YET holds {len(NO_PROVENANCE_YET)} entries, expected "
            f"exactly 1. Every artefact owning a published number must be "
            f"staleness-checked; widening this set needs a ledger row and a "
            f"deliberate edit here (C-47).")

    def _dig(d, path):
        for k in path:
            if not isinstance(d, dict):
                return None
            d = d.get(k)
        return d

    cli_path = repo / "_build/default/latex-parse/src/validators_cli.exe"
    cli_hash = None
    if cli_path.is_file():
        h = hashlib.sha256()
        with cli_path.open("rb") as fh:
            for chunk in iter(lambda: fh.read(1 << 20), b""):
                h.update(chunk)
        cli_hash = h.hexdigest()

    for rel, sha_path, howto in ARTEFACTS:
        f = repo / rel
        if not f.is_file():
            findings.append(f"{rel} is missing, but the generated block reads it")
            continue
        try:
            data = json.loads(f.read_text())
        except (json.JSONDecodeError, OSError) as exc:
            findings.append(f"{rel} is unreadable: {exc}")
            continue
        a_sha = _dig(data, sha_path)
        if not a_sha:
            if rel not in NO_PROVENANCE_YET:
                findings.append(
                    f"{rel} has no {'.'.join(sha_path)}, so its staleness cannot "
                    f"be checked. Refresh with:\n      {howto}")
            continue
        if rel in NO_PROVENANCE_YET:
            findings.append(
                f"{rel} now HAS provenance but is still listed in "
                f"NO_PROVENANCE_YET. Remove the entry — the exemption has "
                f"outlived its reason.")
        r = subprocess.run(
            ["git", "--no-optional-locks", "rev-list", "--count",
             f"{a_sha}..HEAD", "--", "latex-parse/src"],
            cwd=repo, capture_output=True, text=True)
        if r.returncode == 0 and r.stdout.strip().isdigit():
            behind = int(r.stdout.strip())
            if behind > MAX_MEASUREMENT_LAG:
                findings.append(
                    f"{rel} is {behind} commits behind HEAD on latex-parse/src "
                    f"(limit {MAX_MEASUREMENT_LAG}). The number it publishes is "
                    f"probably wrong. Refresh:\n      {howto}")
        # A commit count is a proxy; the binary hash is the fact. When the CLI
        # is built (the `build` job; spec-drift is a pure job and has none),
        # prove the artefact came from THIS binary.
        recorded_cli = _dig(data, ("provenance", "cli_sha256"))
        if cli_hash and recorded_cli and recorded_cli != cli_hash:
            findings.append(
                f"{rel} was produced by a DIFFERENT binary "
                f"(records {recorded_cli[:12]}…, built is {cli_hash[:12]}…). "
                f"Commit distance can be zero and this still wrong. Refresh:\n"
                f"      {howto}")

    # ── 3. the corrections log must not be empty ─────────────────────────
    m = re.search(r"^##\s*4\..*?corrections log.*?$(.*?)^##\s", text,
                  re.M | re.S | re.I)
    n_corr = len(re.findall(r"^\|\s*C-\d+\s*\|", m.group(1), re.M)) if m else 0
    if n_corr < MIN_CORRECTIONS:
        findings.append(f"corrections log has {n_corr} entries, expected at least "
                        f"{MIN_CORRECTIONS}. This section is the point of the "
                        f"document; an empty one means nobody wrote down what was "
                        f"learned.")

    # ── CELL CONSISTENCY: every row's verdict cell must follow from the row's
    # own recorded outcomes. C-45: `ungraded-infra` is assigned only when
    # pdflatex FAILS, but both refresh paths in diff_real_roots.py made the
    # label STICKY (`if cell.startswith("ungraded"): pass`), so when OPEN-053's
    # re-grade flipped 2507.08096v1 to rc 0 the row kept `ungraded-infra`. A
    # compiling, READY, PREMISE-CERTIFIED document sat outside the published
    # metric for two commits and nothing noticed, because the count block was
    # recomputed FROM the stale cells and therefore agreed with them.
    #
    # ⚠ The two samples have DIFFERENT schemas — sample 1 records pdflatex_rc,
    # sample 2 records pdflatex_verdict and has no rc at all. A check keyed on
    # rc alone silently "passes" 200 sample-2 rows by reading -1 for every one.
    def _compiles(row):
        rc = row.get("pdflatex_rc")
        if rc is not None and rc != -1:
            return rc == 0
        v = str(row.get("pdflatex_verdict") or "").lower()
        return True if v == "compiles" else False if v == "fails" else None

    for name in ("results.json", "results_sample2.json"):
        f = repo / "corpora/real_roots" / name
        if not f.is_file():
            continue
        try:
            rows = json.loads(f.read_text()).get("docs", [])
        except (json.JSONDecodeError, OSError) as exc:
            findings.append(f"corpora/real_roots/{name} is unreadable: {exc}")
            continue
        for row in rows:
            rid, cell = row.get("arxiv_id", "?"), row.get("cell", "")
            comp, ready = _compiles(row), row.get("cli_rc") == 0
            if cell.startswith("ungraded"):
                if comp is True:
                    findings.append(
                        f"{name}: {rid} is '{cell}' but its recorded outcome says it "
                        f"COMPILES. The ungraded classes only apply while pdflatex "
                        f"fails; re-derive the cell (C-45).")
                continue
            if comp is None:
                findings.append(
                    f"{name}: {rid} has cell '{cell}' but no usable pdflatex outcome "
                    f"(neither pdflatex_rc nor pdflatex_verdict).")
                continue
            want = ("true-READY" if (ready and comp) else
                    "FALSE-READY" if (ready and not comp) else
                    "false-NOT-READY" if comp else "true-NOT-READY")
            if want != cell:
                findings.append(
                    f"{name}: {rid} has cell '{cell}' but cli_rc={row.get('cli_rc')} "
                    f"with compiles={comp} implies '{want}'.")

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
