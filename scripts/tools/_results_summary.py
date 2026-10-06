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


# ── C-127 (review round 2): THE REST OF THE EVIDENCE THE LEDGER CITES ──────
# C-126 checked the totals of three results artefacts and six re-grade diffs
# and said "every stored total". Review round 2 changed totals in four more
# evidence artefacts (the OPEN-118 re-grade diffs, the oracle-baseline
# summary, the CLI re-verification) and every gate passed; and it dropped a
# row from an O-5 diff (with `counts` re-derived), cut a re-grade diff to 150
# rows, and changed a first-error line, all unseen. The definitions below
# close those, artefact by artefact. The artefacts whose stored totals ARE
# checked are exactly CHECKED below; a total outside them is NOT checked (the
# false_ready, apply_fixes and compile_check entries of
# oracle_baseline/summary.json record runs whose rows are not committed).

#: re-grade diff -> the results artefact it re-grades, for the six diffs
#: OPEN-126 (d)/(e) cite; every one must exist (a deleted diff is a finding).
REGRADE_DIFFS = {
    f"corpora/oracle_baseline/{kind}_sample{n}.json": res
    for kind in ("regrade_open126", "o5_forced_clock")
    for n, res in ((1, "corpora/real_roots/results.json"),
                   (2, "corpora/real_roots/results_sample2.json"),
                   (3, "corpora/real_roots/results_sample3.json"))}

#: OPEN-118's two real_roots re-grade diffs -> their results artefact.
OPEN118_ROOT_DIFFS = {
    "corpora/oracle_baseline/diff_real_roots_sample1.json":
        "corpora/real_roots/results.json",
    "corpora/oracle_baseline/diff_real_roots_sample2.json":
        "corpora/real_roots/results_sample2.json"}

#: OPEN-118's cell diffs (oracle_baseline_cells.py) -> their artefact and the
#: row-id key of that artefact's rows.
OPEN118_CELL_DIFFS = {
    "corpora/oracle_baseline/diff_apply_fixes_real_results.json":
        ("corpora/apply_fixes_real/results.json", "arxiv_id"),
    "corpora/oracle_baseline/diff_apply_fixes_real_results_virgin.json":
        ("corpora/apply_fixes_real/results_virgin.json", "arxiv_id"),
    "corpora/oracle_baseline/diff_apply_fixes_real_results_fresh.json":
        ("corpora/apply_fixes_real/results_fresh.json", "arxiv_id"),
    "corpora/oracle_baseline/diff_strict_battery.json":
        ("corpora/strict_battery/manifest.json", "file")}

BASELINE_SUMMARY = "corpora/oracle_baseline/summary.json"
CLI_VERIFY = "corpora/oracle_baseline/cli_verify_fe673dc1.json"

#: Every artefact whose stored totals this module checks.
CHECKED = (("corpora/real_roots/results.json",
            "corpora/real_roots/results_sample2.json",
            "corpora/real_roots/results_sample3.json")
           + tuple(REGRADE_DIFFS) + tuple(OPEN118_ROOT_DIFFS)
           + tuple(OPEN118_CELL_DIFFS) + (BASELINE_SUMMARY, CLI_VERIFY))


def _ids(rows, key="arxiv_id"):
    return [r.get(key) for r in rows]


def id_set_findings(rows, results_docs, name, res_name) -> list[str]:
    """A diff must cover its results artefact exactly: the same ids, each
    once. A dropped row with re-derived totals passes every total check."""
    got, want = _ids(rows), _ids(results_docs)
    out = []
    dup = sorted({i for i in got if got.count(i) > 1})
    if dup:
        out.append(f"{name}: rows repeat {dup[:5]}")
    if set(got) != set(want):
        out.append(f"{name}: its rows are not {res_name}'s ({len(got)} rows "
                   f"vs {len(want)} docs; only in the diff "
                   f"{sorted(set(got) - set(want))[:5]}, missing "
                   f"{sorted(set(want) - set(got))[:5]})")
    return out


def field_moves(rows) -> dict:
    """field -> number of rows whose before and after differ in it, over
    EVERY field either side records (cell, rc, PDF, verdict, passes, first
    error...), not only OUTCOME_KEYS."""
    out = collections.Counter()
    for r in rows:
        b, a = r.get("before") or {}, r.get("after") or {}
        for k in sorted(set(b) | set(a)):
            if b.get(k) != a.get(k):
                out[k] += 1
    return dict(out)


def real_roots_diff_summary(rows) -> dict:
    """OPEN-118's real_roots diff summary, from its rows (the checking
    definition; the one-off writer of 4adcc30c was not committed). rc is
    compared only where the before side recorded one: sample 2's recorder
    stored none (200/200), which `rc_unrecorded_before` states, so its
    `rc_changed` 0 is not read as 200 comparisons."""
    def bf(r, k):
        return (r.get("before") or {}).get(k)

    def af(r, k):
        return (r.get("after") or {}).get(k)
    return {
        "rows": len(rows),
        "cell_changed": sum(bf(r, "cell") != af(r, "cell") for r in rows),
        "rc_changed": sum(bf(r, "pdflatex_rc") is not None
                          and bf(r, "pdflatex_rc") != af(r, "pdflatex_rc")
                          for r in rows),
        "rc_unrecorded_before": sum(bf(r, "pdflatex_rc") is None for r in rows),
        "verdict_changed": sum(bf(r, "pdflatex_verdict") != af(r, "pdflatex_verdict")
                               for r in rows),
        "rc0_without_pdf": sum(af(r, "pdflatex_rc") == 0 and not af(r, "pdflatex_pdf")
                               for r in rows),
        "first_error_text_changed": sum(bf(r, "first_error") != af(r, "first_error")
                                        for r in rows)}


def real_roots_diff_findings(doc, results_doc, name, res_name) -> list[str]:
    rows = doc.get("rows") or []
    out = id_set_findings(rows, results_doc.get("docs") or [], name, res_name)
    for r in rows:
        want = (r["before"]["cell"] != r["after"]["cell"])
        if r.get("cell_changed") != want:
            out.append(f"{name}: {r.get('arxiv_id')} records cell_changed="
                       f"{r.get('cell_changed')!r} but its before/after give {want!r}")
    want = real_roots_diff_summary(rows)
    got = {k: v for k, v in (doc.get("summary") or {}).items()
           if k != "first_error_note"}
    if got != want:
        out.append(f"{name}: its summary {got} is not what its rows give, "
                   f"{want} (C-127)")
    return out


def cell_diff_findings(doc, artefact_doc, name, art_name, key) -> list[str]:
    """oracle_baseline_cells.py's diff: its `rows` total is the artefact's
    row count, and every row it names is one of the artefact's. (Its before
    side is a git revision, not committed rows; its lists are what it
    found, so their lengths are the totals summary.json quotes.)"""
    rows = artefact_doc.get("rows") or []
    ids = set(_ids(rows, key))
    out = []
    if doc.get("rows") != len(rows):
        out.append(f"{name}: records rows={doc.get('rows')!r} but {art_name} "
                   f"has {len(rows)} (C-127)")
    for lst in ("outcome_moved", "first_error_changed_only"):
        for m in doc.get(lst) or []:
            if m.get("row") not in ids:
                out.append(f"{name}: {lst} names {m.get('row')!r}, not a row "
                           f"of {art_name}")
    return out


def baseline_summary_findings(summ, load) -> list[str]:
    """oracle_baseline/summary.json's per-artefact totals, each from the diff
    it names (`load(rel)` reads a repo file). Entries naming no diff record a
    run whose rows are not committed and are not checked."""
    out = []
    for label, e in (summ.get("artefacts") or {}).items():
        dpath = e.get("diff")
        if not dpath:
            continue
        d = load(dpath)
        where = f"{BASELINE_SUMMARY} [{label}]"
        if dpath in OPEN118_ROOT_DIFFS:
            rows = d.get("rows") or []
            want = {"rows": len(rows),
                    "outcome_changed": sum(
                        r["before"]["cell"] != r["after"]["cell"]
                        or r["before"].get("pdflatex_verdict") != r["after"].get("pdflatex_verdict")
                        or (r["before"].get("pdflatex_rc") is not None
                            and r["before"]["pdflatex_rc"] != r["after"].get("pdflatex_rc"))
                        for r in rows)}
            if "reason_changed_class_i" in e:
                want["reason_changed_class_i"] = sum(
                    str(r.get("classification") or "").startswith("(i)") for r in rows)
        elif dpath in OPEN118_CELL_DIFFS:
            want = {"rows": d.get("rows"),
                    "outcome_changed": len(d.get("outcome_moved") or [])}
            if "broken" in e:
                arows = load(OPEN118_CELL_DIFFS[dpath][0]).get("rows") or []
                cells = collections.Counter(r.get("cell") for r in arows)
                want["broken"] = (f"{cells['broken']}/"
                                  f"{len(arows) - cells['excluded-did-not-compile']}")
        else:
            out.append(f"{where}: names diff {dpath}, which this module does "
                       f"not know how to check; add it to OPEN118_*_DIFFS")
            continue
        got = {k: e.get(k) for k in want}
        if got != want:
            out.append(f"{where}: {got} is not what {dpath} gives, {want} (C-127)")
    return out


def cli_verify_findings(doc, load) -> list[str]:
    """cli_verify_fe673dc1.json: per sample, `rows` is the results
    artefact's doc count, `differ` the number of listed diffs, `rc_differs`
    the listed diffs whose rc differs, and every listed id is a doc."""
    out = []
    for res_name, s in (doc.get("samples") or {}).items():
        docs = load(f"corpora/real_roots/{res_name}").get("docs") or []
        diffs = s.get("diffs") or []
        want = {"rows": len(docs), "differ": len(diffs),
                "rc_differs": sum(d.get("rec_rc") != d.get("rc") for d in diffs)}
        got = {k: s.get(k) for k in want}
        if got != want:
            out.append(f"{CLI_VERIFY} [{res_name}]: {got} is not what its diffs "
                       f"and {res_name} give, {want} (C-127)")
        ids = set(_ids(docs))
        for d in diffs:
            if d.get("id") not in ids:
                out.append(f"{CLI_VERIFY} [{res_name}]: lists {d.get('id')!r}, "
                           f"not a doc of {res_name}")
    return out


# ── C-128 (review round 3): THE EVIDENCE JOINED BY VALUE ───────────────────
# C-127 joined each OPEN-126 diff to its results artefact by row ids and by
# totals only. Review round 3 changed a results row to rc 1 / FALSE-READY
# (totals re-derived) while both diffs that cite it still said rc 0; set
# both sides of an O-5 row to the same forged first error; and moved a CLI
# re-verification's rc; every gate passed. Now each row's recorded VALUES
# must be the results row's.

#: The oracle-side fields of a diff row's before/after sides; each must equal
#: the same-named field of the results doc it re-grades.
ORACLE_SIDE_FIELDS = ("pdflatex_rc", "pdflatex_verdict", "pdflatex_pdf",
                      "pdflatex_passes", "first_error")

#: The one diff measured BEFORE its results artefact's CLI side was
#: re-measured (OPEN-126 (e)(ii), C-120): its cli_rc/cell may differ from the
#: results doc exactly on the rows the CLI re-verification lists as
#: rc-differing, and there they must be the re-verification's recorded side.
CLI_REFRESH_AFTER = {
    "corpora/oracle_baseline/regrade_open126_sample2.json": "results_sample2.json"}


def graded_cell(side: dict, cli_rc) -> str:
    """The cell a side's OWN values give (C-129): the grader's own cell_of
    and row_compiles (diff_real_roots.py), never a recorded cell."""
    from diff_real_roots import cell_of, row_compiles  # noqa: E402
    if side.get("pdflatex_rc") == -1 or cli_rc == -1:
        return "ungraded-timeout"
    return cell_of(row_compiles(side), cli_rc == 0)


def evidence_value_findings(load) -> list[str]:
    """Each OPEN-126 diff row agrees with its results doc in every value it
    records (toplevel, cli_rc, cell, passes, both sides' oracle fields), and
    the CLI re-verification's rc for every listed row is the results doc's
    cli_rc (its recorded rc, where no refresh happened, too).

    EVERY CELL IS RE-DERIVED (C-129, review round 4): on every side of every
    row, and on the results doc's row, the recorded cell must be the cell the
    side's own oracle values and CLI rc give (graded_cell). The moved rows
    (CLI refreshed) used to be checked on cli_rc alone, so both sides' cells
    forged to FALSE-READY on 2507.03521v2 passed."""
    out = []
    cv = load(CLI_VERIFY).get("samples") or {}
    refreshed = {}
    for res_name, s in cv.items():
        refreshed[res_name] = {d.get("id"): d for d in s.get("diffs") or []
                               if d.get("rec_rc") != d.get("rc")}
    for rel, res in REGRADE_DIFFS.items():
        name, res_name = rel.rsplit("/", 1)[-1], res.rsplit("/", 1)[-1]
        docs = {d.get("arxiv_id"): d for d in load(res).get("docs") or []}
        moved = (refreshed.get(CLI_REFRESH_AFTER[rel], {})
                 if rel in CLI_REFRESH_AFTER else {})
        for r in load(rel).get("rows") or []:
            i = r.get("arxiv_id")
            doc = docs.get(i)
            if doc is None:
                continue        # id_set_findings reports it
            bad = []
            for side in ("before", "after"):
                sd = r.get(side) or {}
                if sd.get("cell") != graded_cell(sd, r.get("cli_rc")):
                    bad.append(f"{side}.cell (vs its own oracle values and "
                               f"cli_rc)")
            if doc.get("cell") != graded_cell(doc, doc.get("cli_rc")):
                bad.append(f"{res_name}'s cell (vs its own oracle values and "
                           f"cli_rc)")
            if r.get("toplevel") != doc.get("toplevel"):
                bad.append("toplevel")
            if r.get("passes") != doc.get("pdflatex_passes"):
                bad.append("passes")
            for side in ("before", "after"):
                sd = r.get(side) or {}
                for k in ORACLE_SIDE_FIELDS:
                    if sd.get(k) != doc.get(k):
                        bad.append(f"{side}.{k}")
            if i in moved:
                if r.get("cli_rc") != moved[i].get("rec_rc") or \
                        doc.get("cli_rc") != moved[i].get("rc"):
                    bad.append("cli_rc (vs the CLI re-verification)")
            else:
                if r.get("cli_rc") != doc.get("cli_rc"):
                    bad.append("cli_rc")
                for side in ("before", "after"):
                    if (r.get(side) or {}).get("cell") != doc.get("cell"):
                        bad.append(f"{side}.cell")
            if bad:
                out.append(f"{name}: row {i} records {bad} unlike {res_name}'s "
                           f"row (C-128): the evidence must be the grade it "
                           f"cites")
    for res_name, s in cv.items():
        docs = {d.get("arxiv_id"): d
                for d in load(f"corpora/real_roots/{res_name}").get("docs") or []}
        refreshed_here = res_name in CLI_REFRESH_AFTER.values()
        for d in s.get("diffs") or []:
            doc = docs.get(d.get("id"))
            if doc is None:
                continue        # cli_verify_findings reports it
            if d.get("rc") != doc.get("cli_rc"):
                out.append(f"{CLI_VERIFY} [{res_name}]: {d.get('id')} rc "
                           f"{d.get('rc')!r} is not {res_name}'s cli_rc "
                           f"{doc.get('cli_rc')!r} (C-128)")
            if not refreshed_here and d.get("rec_rc") != doc.get("cli_rc"):
                out.append(f"{CLI_VERIFY} [{res_name}]: {d.get('id')} recorded "
                           f"rc {d.get('rec_rc')!r} is not {res_name}'s cli_rc "
                           f"{doc.get('cli_rc')!r}, and {res_name}'s CLI side "
                           f"was never re-measured (C-128)")
    return out
