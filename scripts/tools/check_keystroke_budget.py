#!/usr/bin/env python3
"""check_keystroke_budget.py — the R-BUDGET latency invariant gate.

WHY THIS EXISTS
---------------
ROADMAP.md:267 promises a per-keystroke edit window of p50 <= 3 ms / p99 <= 10 ms,
and ROADMAP.md:276 makes that concrete as a PER-STAGE budget at 300 KB:

    parse <= 40 | shared <= 20 | rules <= 30 | structural <= 15 | IPC <= 5   (ms)

Nothing enforced it. `check_keystroke_budget.py` is named in the R-BUDGET row as
the gate that would, and it did not exist; `scripts/bench_wedge.sh` (R-BENCH) did
not exist either. What perf-ci DOES enforce is `edit_window_gate.sh`, and that
gate times `Real_processor.run` — the L0 LEXER — on a random 4096-byte slice.
It is not a smaller version of the budget above; it measures a different stage of
the pipeline. Measured warm, startup excluded, on an IDLE CI runner (load 1.0):

    band      parse_ms   fastrun_ms   rules_ms
    100 KB       3.3        98.7        95.4
    300 KB      10.5       294.5       284.0      <-- budget says rules <= 30

    edit_window_gate.sh on the same 300 KB document:  p95 = 0.031 ms  PASS

So the required gate passed with a 39x margin while the budgeted stage missed by
9.5x. Parse is fine (10.5 vs 40 ms, ~4% of the kernel); ~96% of the cost is rule
execution, and it is LINEAR in document size — the signature of every rule
scanning the whole document.

The miss is HARDWARE-DEPENDENT and should always be quoted as a pair: 9.5x on the
shared ubuntu-latest runner, ~5.3x on an idle Apple-Silicon laptop, a ~1.8x
spread. CI is the baseline environment because it is reproducibly idle, NOT
because it represents a user's machine.

WHAT THIS GATE MEASURES
-----------------------
Two surfaces, because the project has two and only one of them has ever had a
stated budget:

  KEYSTROKE  `bench_readiness_kernel.exe` — parse + the 37 compile-blocking
             rules, warm, startup excluded. This is the surface ROADMAP:276
             budgets. Reported per stage.
  BATCH      `validators_cli.exe --apply-fixes-best-effort` — ONE pass of the
             full ~641-rule set, wall clock. ROADMAP.md:80 (Principle 9) requires
             every serving change to state and defend a latency budget; this one
             never got one. There is no target to compare against, so this gate
             establishes a measured baseline and forbids regression from it.

Both are measured on deterministic slices of corpora/perf/perf_smoke_big.tex cut
at line boundaries. Slicing rather than committing new fixtures keeps 300 KB of
duplicate corpus out of the repo and makes the bands impossible to desync from
their source.

MONOTONE, LIKE THE OTHER BASELINES IN THIS REPO
-----------------------------------------------
Same idiom as corpora/false_ready/manifest.json and corpora/apply_fixes/
manifest.json: the measured numbers are recorded, the gate lands GREEN, and it
fails on a REGRESSION. It additionally reports the distance to the ROADMAP:276
budget on every run and fails if that gap WIDENS, so an 11x miss is a tracked,
visible debt instead of an absent one.

⚠ TIMING GATES ARE NOISY AND THIS ONE KNOWS IT. The recorded baseline carries the
machine and load it was taken on. TOLERANCE defaults to 1.5x precisely so that
ordinary scheduling noise does not turn a required context red; it is a ratchet
against real regressions, not a benchmark.

⚠⚠ AND IT IS NOT SENSITIVE ENOUGH TO CATCH GRADUAL EROSION. A regression must
clear BOTH the ratio AND --min-delta-ms, so a ~7% regression on the budgeted path
passes. The 5 ms floor is not removable: parse is only a few ms, and 3 ms of
scheduler noise clears 1.5x, which reddened a REQUIRED context on an unmodified
baseline during development. This gate stops catastrophes, not drips — and drips
are how rules reached ~9.5x over budget. For precision use an interleaved A/B of
two binaries ON A QUIET MACHINE; a loaded machine has been measured INVERTING the
sign of an A/B result.

⚠ NOT MEASURED: the `shared`, `structural` and `IPC` stages of the ROADMAP:276
budget have no separate instrumentation in bench_readiness_kernel.ml, so this
gate covers `parse` and `rules` only. Recorded here rather than passed over in
silence; extending the bench is the follow-up.

USAGE
    check_keystroke_budget.py [--repo DIR] [--record] [--reps N] [--tolerance F]

EXIT 0 clean | 1 regression or widened spec gap | 2 infrastructure
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

SOURCE_DOC = "corpora/perf/perf_smoke_big.tex"
BASELINE = "corpora/perf/keystroke_budget.json"
BANDS_KB = [4, 50, 100, 300]

# ROADMAP.md:276, per-stage at 300 KB. Only the stages the bench can actually
# separate are listed; see the NOT MEASURED note above.
SPEC_BUDGET_300KB_MS = {"parse": 40.0, "rules": 30.0}


def die(msg: str) -> int:
    print(f"[keystroke-budget] FATAL: {msg}", file=sys.stderr)
    return 2


def build_bands(repo: Path, tmp: Path) -> dict[int, Path]:
    """Deterministic line-aligned slices of the perf corpus."""
    src = repo / SOURCE_DOC
    raw = src.read_bytes()
    out: dict[int, Path] = {}
    for kb in BANDS_KB:
        want = kb * 1000
        if len(raw) < want:
            raise RuntimeError(
                f"{SOURCE_DOC} is {len(raw)} bytes, too small for a {kb} KB band")
        cut = raw[:want]
        nl = cut.rfind(b"\n")  # drop the partial trailing line
        cut = cut[: nl + 1] if nl > 0 else cut
        cut += b"\n\\end{document}\n"
        p = tmp / f"band_{kb}kb.tex"
        p.write_bytes(cut)
        out[kb] = p
    return out


def run_keystroke(bench: Path, bands: dict[int, Path], reps: int) -> dict[str, dict]:
    """bench_readiness_kernel: size parse_ms fastrun_ms rules_ms (warm, no startup)."""
    args = [str(bench), str(reps)] + [str(bands[kb]) for kb in BANDS_KB]
    p = subprocess.run(args, capture_output=True, text=True)
    if p.returncode != 0:
        raise RuntimeError(f"bench_readiness_kernel exited {p.returncode}: {p.stderr[:400]}")
    rows: dict[str, dict] = {}
    order = list(BANDS_KB)
    for line in p.stdout.splitlines():
        f = line.split()
        if len(f) != 4 or not f[0].isdigit():
            continue  # header
        if not order:
            break
        kb = order.pop(0)
        rows[str(kb)] = {
            "bytes": int(f[0]),
            "parse_ms": float(f[1]),
            "fastrun_ms": float(f[2]),
            "rules_ms": float(f[3]),
        }
    if len(rows) != len(BANDS_KB):
        raise RuntimeError(
            f"bench emitted {len(rows)} rows, expected {len(BANDS_KB)} — refusing to grade")
    return rows


def run_batch(cli: Path, bands: dict[int, Path], reps: int) -> dict[str, float]:
    """One full-lint pass, wall clock, best-of-reps."""
    out: dict[str, float] = {}
    for kb in BANDS_KB:
        best = None
        for _ in range(max(1, reps)):
            t0 = time.monotonic()
            r = subprocess.run(
                [str(cli), "--apply-fixes-best-effort", str(bands[kb])],
                capture_output=True)
            dt = (time.monotonic() - t0) * 1000.0
            if r.returncode not in (0, 1):
                raise RuntimeError(f"CLI exited {r.returncode} on the {kb} KB band")
            best = dt if best is None else min(best, dt)
        out[str(kb)] = round(best, 1)
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=".")
    ap.add_argument("--record", action="store_true",
                    help="re-measure and rewrite the baseline (deliberate act)")
    ap.add_argument("--reps", type=int, default=11)
    ap.add_argument("--tolerance", type=float, default=1.5,
                    help="fail when measured > recorded * TOLERANCE")
    ap.add_argument("--min-delta-ms", type=float, default=5.0,
                    help="a regression must exceed BOTH --tolerance and this "
                         "absolute delta, so sub-noise swings cannot flake")
    ap.add_argument("--max-record-load", type=float, default=4.0,
                    help="refuse to --record above this 1-minute load average")
    ap.add_argument("--force-record", action="store_true",
                    help="record anyway, marking the baseline provisional")
    ns = ap.parse_args()
    repo = Path(ns.repo).resolve()

    bench = repo / "_build/default/latex-parse/src/bench_readiness_kernel.exe"
    cli = repo / "_build/default/latex-parse/src/validators_cli.exe"
    for b in (bench, cli):
        if not b.exists():
            return die(f"not built: {b} (build it in its own step)")
    if not (repo / SOURCE_DOC).exists():
        return die(f"missing perf corpus {SOURCE_DOC}")

    # Check this BEFORE measuring: a full sweep costs about a minute, and
    # refusing afterwards wastes it. (Found by running the gate's own proof
    # script — step A sat there benchmarking only to decline at the end.)
    if ns.record and os.getloadavg()[0] > ns.max_record_load and not ns.force_record:
        return die(
            f"refusing to record a baseline at load average "
            f"{os.getloadavg()[0]:.1f} (limit {ns.max_record_load}). These "
            f"timings would be inflated by concurrent work, and a too-high "
            f"baseline makes this gate vacuous. Record on an idle machine or "
            f"in CI; pass --force-record to override and mark it provisional.")

    base_path = repo / BASELINE
    recorded = None
    if base_path.exists():
        try:
            recorded = json.loads(base_path.read_text())
        except Exception as exc:  # noqa: BLE001
            return die(f"cannot parse {BASELINE}: {exc}")
    elif not ns.record:
        return die(f"{BASELINE} missing — run with --record to create it")

    with tempfile.TemporaryDirectory(prefix="ksb-") as td:
        try:
            bands = build_bands(repo, Path(td))
            keystroke = run_keystroke(bench, bands, ns.reps)
            batch = run_batch(cli, bands, max(3, ns.reps // 3))
        except Exception as exc:  # noqa: BLE001
            return die(str(exc))

    # NON-VACUITY: a bench that silently did nothing reports zeros, and zeros
    # would compare favourably against every baseline forever.
    for kb, row in keystroke.items():
        if row["rules_ms"] <= 0.0 or row["fastrun_ms"] <= 0.0:
            return die(f"{kb} KB band measured {row} — a zero timing means the "
                       f"bench did not run; refusing to report success")

    load1 = os.getloadavg()[0]
    k300 = keystroke["300"]
    gap = {stage: round(k300[f"{stage}_ms"] / budget, 2)
           for stage, budget in SPEC_BUDGET_300KB_MS.items()}

    print("[keystroke-budget] KEYSTROKE surface "
          "(bench_readiness_kernel, warm, startup excluded):")
    print(f"  {'band':>8}  {'parse_ms':>9}  {'rules_ms':>9}  {'fastrun_ms':>11}")
    for kb in BANDS_KB:
        r = keystroke[str(kb)]
        print(f"  {kb:>6}KB  {r['parse_ms']:>9.1f}  {r['rules_ms']:>9.1f}  "
              f"{r['fastrun_ms']:>11.1f}")
    print("[keystroke-budget] BATCH surface (one full-lint pass, wall clock):")
    for kb in BANDS_KB:
        print(f"  {kb:>6}KB  {batch[str(kb)]:>9.1f} ms")
    print(f"[keystroke-budget] vs ROADMAP:276 budget @300KB "
          f"(parse<={SPEC_BUDGET_300KB_MS['parse']:.0f}, "
          f"rules<={SPEC_BUDGET_300KB_MS['rules']:.0f} ms): "
          + ", ".join(f"{s} {g}x" for s, g in sorted(gap.items())))
    print(f"[keystroke-budget] load average during run: {load1:.1f} "
          f"(absolute numbers are inflated by concurrent work; ratios are not)")

    measured = {"keystroke": keystroke, "batch_ms": batch,
                "spec_gap_300kb": gap, "reps": ns.reps,
                "loadavg_1min": round(load1, 2)}

    if ns.record:
        # The refusal itself is enforced up front, before the sweep is paid for.
        # Reaching here means either the machine was quiet or --force-record was
        # passed; in the latter case the baseline is inflated and must say so.
        provisional = load1 > ns.max_record_load
        base_path.parent.mkdir(parents=True, exist_ok=True)
        base_path.write_text(json.dumps({
            "description": (
                "R-BUDGET baseline. Monotone: the gate fails on a regression "
                "beyond TOLERANCE and on a WIDENED gap to the ROADMAP:276 "
                "budget. Re-record from CI, not a busy laptop."),
            "provisional": provisional,
            "provisional_note": (
                "Recorded above the load limit, so these numbers are inflated "
                "and the ratchet is LOOSE until re-recorded on an idle runner."
                if provisional else ""),
            "spec_budget_300kb_ms": SPEC_BUDGET_300KB_MS,
            "stages_not_instrumented": ["shared", "structural", "IPC"],
            **measured,
        }, indent=2) + "\n", encoding="utf-8")
        print(f"[keystroke-budget] recorded baseline to {BASELINE}"
              + (" (PROVISIONAL — inflated, re-record when idle)"
                 if provisional else ""))
        return 0

    if recorded.get("provisional"):
        print(f"[keystroke-budget] ⚠ BASELINE IS PROVISIONAL — recorded at load "
              f"{recorded.get('loadavg_1min')}, so it is inflated and this "
              f"ratchet is LOOSE. Re-record on an idle runner "
              f"(--record) to make it bind.")

    findings: list[str] = []
    for kb in BANDS_KB:
        prev = recorded.get("keystroke", {}).get(str(kb))
        if not prev:
            findings.append(f"{kb} KB band absent from the baseline — re-record")
            continue
        # A regression must exceed BOTH the ratio AND an absolute delta. A ratio
        # alone is the wrong test for small values: `parse` at 100 KB is ~5 ms,
        # so ordinary scheduler noise of 3 ms trips 1.5x and turns a REQUIRED
        # context red for nothing. That is not hypothetical — this gate's own
        # proof run failed exactly that way on a restored, unmodified baseline.
        # 5 ms is below anything that could matter against a 30-40 ms budget and
        # well above the noise floor seen here.
        for stage in ("parse_ms", "rules_ms"):
            now, was = keystroke[str(kb)][stage], prev[stage]
            if was > 0 and now > was * ns.tolerance and now - was > ns.min_delta_ms:
                findings.append(
                    f"{kb} KB {stage}: {now:.1f} ms vs baseline {was:.1f} ms "
                    f"(> {ns.tolerance}x and > {ns.min_delta_ms} ms) — "
                    f"latency regression")
        pb = recorded.get("batch_ms", {}).get(str(kb))
        if pb and batch[str(kb)] > pb * ns.tolerance \
                and batch[str(kb)] - pb > ns.min_delta_ms:
            findings.append(
                f"{kb} KB batch: {batch[str(kb)]:.1f} ms vs baseline {pb:.1f} ms "
                f"(> {ns.tolerance}x and > {ns.min_delta_ms} ms) — "
                f"latency regression")

    for stage, now in gap.items():
        was = recorded.get("spec_gap_300kb", {}).get(stage)
        if was is not None and now > was * ns.tolerance:
            findings.append(
                f"spec gap for {stage} widened: {now}x over the ROADMAP:276 "
                f"budget, was {was}x")

    if findings:
        print("\n[keystroke-budget] FAIL:\n", file=sys.stderr)
        for f in findings:
            print(f"  - {f}", file=sys.stderr)
        if load1 > ns.max_record_load:
            # NOT a skip path — the failure still stands and the exit code is
            # still 1. But the baseline is recorded on an idle CI runner, and a
            # developer machine under load will exceed it for environmental
            # reasons alone. Say so, rather than letting someone burn an hour
            # hunting a regression that is really just their own build.
            print(
                f"\n  NOTE: this ran at load average {load1:.1f}, well above the "
                f"{ns.max_record_load} the baseline assumes. The baseline is "
                f"measured on an idle CI runner, so a busy machine can exceed it "
                f"without anything having regressed. Trust the CI result; to "
                f"compare locally, use an interleaved A/B of two binaries rather "
                f"than this gate.",
                file=sys.stderr)
        return 1
    print("[keystroke-budget] PASS — no latency regression, spec gap not widened.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
