"""The totals a real-paper artefact stores, as functions of its rows. C-126.

Shared by the publisher (gen_project_state.py) and the gate
(check_project_state.py).

Why it exists. A stored total is a second copy of a fact its rows already
hold, and a second copy drifts. results_sample2.json said "correct": 179 while
its own rows gave 181: `diff_real_roots.py --refresh-cli` moved two cells and
rewrote `counts`, and no committed writer computes `correct` (the one-off
sweeps of #572 and #576 set it; later rewrites carried it). Worse, gen_project_state published the
headline FROM the stored `counts`, so a hand-edited `counts` plus `--write`
regenerated a self-consistent wrong block that every gate passed. The rules
this module encodes:

  * a published number is computed from the PRIMARY rows (`cell_counts`);
  * a stored total is checked against that computation, never trusted;
  * a results artefact stores ONLY keys some writer maintains
    (`RESULTS_KEYS`). An unlisted key is refused, so a total no writer keeps
    true cannot be added again without a deliberate edit here.

Why the check is here and not in the writer. The writers live in
diff_real_roots.py, whose git blob is part of every grade's identity
(`oracle.grading_code`, OPEN-126): any behavioural edit to it voids all 600
recorded sample grades until they are re-graded. The writers' totals are
already correct functions of the rows (`counts`, and a re-grade diff's
`summary`); what was missing was a CHECK of every stored total and a schema
that refuses the unmaintained ones. The diff writer keeps its own inline
computation; `diff_summary` below is the checking definition, and any
divergence between the two fails the gate.
"""

from __future__ import annotations

import collections

# Every top-level key a results artefact (corpora/real_roots/results*.json)
# may carry: written by diff_real_roots.py (--record, --repass,
# --refresh-cli), except `sample` and `measured_at_note`, hand-written prose
# that states no total. `counts` is the one stored total, and it must equal
# cell_counts(docs).
RESULTS_KEYS = frozenset({
    "sample", "frame", "oracle", "counts", "docs", "measured_at",
    "measured_at_note", "measured_at_sha", "src_tree_sha",
    "oracle_regraded_at_sha"})

# A re-grade row's "outcome" is the oracle's observation, not the cell
# (diff_real_roots.repass_failures builds the row flags from these).
OUTCOME_KEYS = ("pdflatex_rc", "pdflatex_pdf", "pdflatex_passes")


def cell_counts(docs) -> dict:
    return dict(collections.Counter(d["cell"] for d in docs))


def results_summary_findings(res: dict, name: str) -> list[str]:
    out = []
    extra = sorted(set(res) - RESULTS_KEYS)
    if extra:
        out.append(f"{name}: top-level key(s) {extra} that no writer maintains "
                   f"(C-126: `correct` stayed 179 while the rows gave 181). A "
                   f"total belongs in the rows or in `counts`; a new key needs "
                   f"a writer and an entry in _results_summary.RESULTS_KEYS.")
    want = cell_counts(res.get("docs") or [])
    if res.get("counts") != want:
        out.append(f"{name}: stored counts {res.get('counts')!r} is not what its "
                   f"rows give, {want!r} (C-126). Never hand-edit a total; "
                   f"re-derive it from the rows.")
    return out


def diff_row_flags(row) -> dict:
    b, a = row["before"], row["after"]
    return {"cell_changed": b["cell"] != a["cell"],
            "outcome_changed": any(b[k] != a[k] for k in OUTCOME_KEYS)}


def diff_summary(rows) -> dict:
    """The `summary` of a re-grade diff, from its rows.

    `counts_after` counts the rows' after-cells. diff_real_roots writes the
    whole artefact's counts there; the two agree because every committed diff
    was taken with --repass-scope all (every row), and the gate fails if one
    ever does not.
    """
    return {"rows": len(rows),
            "cells_moved": sum(1 for r in rows if diff_row_flags(r)["cell_changed"]),
            "outcomes_moved": sum(1 for r in rows
                                  if diff_row_flags(r)["outcome_changed"]),
            "counts_after": cell_counts([r["after"] for r in rows])}


def diff_summary_findings(doc: dict, name: str) -> list[str]:
    rows = doc.get("rows") or []
    out = []
    for r in rows:
        for k, v in diff_row_flags(r).items():
            if r.get(k) != v:
                out.append(f"{name}: {r.get('arxiv_id', '?')} records {k}="
                           f"{r.get(k)!r} but its before/after give {v!r} (C-126)")
    want = diff_summary(rows)
    if "summary" in doc and doc["summary"] != want:
        out.append(f"{name}: its summary {doc['summary']} is not what its rows "
                   f"give, {want} (C-126)")
    if "counts" in doc and doc["counts"] != want["counts_after"]:
        out.append(f"{name}: its counts {doc['counts']} are not what its rows' "
                   f"after-cells give, {want['counts_after']} (C-126)")
    if "summary" not in doc and "counts" not in doc:
        out.append(f"{name}: no stored summary or counts to check")
    return out
