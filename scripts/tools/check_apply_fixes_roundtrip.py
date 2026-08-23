#!/usr/bin/env python3
"""check_apply_fixes_roundtrip.py — the apply-fixes round-trip gate (R7-INFRA-4).

WHY THIS EXISTS
---------------
`--apply-fixes` rewrites user documents. It is the one class the round-7 audit
called out as able to SILENTLY DESTROY user files: nothing re-checks the fixer's
own output, so a fix that breaks a document is invisible.

Measured on `corpora/compile_check` (65 docs, TL2026) while writing this gate:

    the fixer rewrites            25 / 65
    non-idempotent                 0
    verdict-degrading              0
    COMPILED BEFORE, FAILS AFTER   2      good_accents_utf8, good_tikz_simple

Both breakages are the same class — a typography fix applied inside a LOAD-BEARING
region, where the character is syntax rather than punctuation:

  * `good_tikz_simple`   `--` inside a TikZ path is pgf's line-to OPERATOR.
                         Rewritten to an en dash it yields
                         "! Package tikz Error: Giving up on this path." and no PDF.
  * `good_accents_utf8`  the backtick in `\\`a` IS the grave-accent command.
                         Rewritten to U+2018 the command is destroyed.

**Neither is caught by `--compile-check`.** Only real pdflatex sees them. That is
the whole argument for this gate, and it is why property (b) is not optional.

THE THREE PROPERTIES (the audit's R7-INFRA-4)
---------------------------------------------
  (a) IDEMPOTENT              applying twice == applying once
      (measured: good_quotes_dashes under --apply-fixes-best-effort needs TWO
       passes to reach a fixpoint — pass 1 leaves ``quotes'' alone, pass 2 curls
       them. Bounded, but "apply twice != apply once" is exactly what (a) forbids.)
  (c) VERDICT-NON-DEGRADING   a READY document must not become NOT-READY
  (b) ORACLE-CLASS-PRESERVING a document that compiled must still compile

(a) and (c) need only the CLI, so they run in CI's `build` job. (b) needs real
pdflatex and rides the pinned-image `tex-oracle` workflow, ADVISORY. Same split
as the false-READY gates: check_known_false_ready.py (CLI-only) vs
false_ready_oracle.sh.

⚠ This sentence was ASPIRATIONAL until the wiring landed: tex-oracle.yml never
invoked this script, and the only --require-pdflatex caller was
pre_release_check.py's BUILD_CHECKS, which release.sh skips via --skip-build. So
(b) — the one property that can see the fixer break a compiling document — ran
in no automated path at all, while this docstring said otherwise. If you are
reading this because (b) is failing, check first whether
corpora/apply_fixes/manifest.json's baseline was recorded on the same engine:
unlike corpora/false_ready/manifest.json it carries no oracle.version pin.

MONOTONE, LIKE THE FALSE-READY CORPUS
-------------------------------------
The known breakages are recorded in `corpora/apply_fixes/manifest.json` so the
gate lands GREEN and any NEW breakage fails. It fails in BOTH directions — a
recorded-broken document that starts working is also an error, forcing the
manifest to be updated, so the baseline can only improve and can never silently
desync. R7-3 (the fixer guard) will flip these entries.

`corpora/apply_fixes/` additionally holds adversarial fixtures for destructive
patterns the natural corpus does not contain. Without them this gate would be
VACUOUS on exactly the class it exists to catch — `corpora/compile_check` has no
`--` inside an `\\input` filename, so nothing would exercise it.

⚠ STAGING IS LOAD-BEARING. The fixed output must be written into a copy of the
WHOLE corpus directory, because `\\input{sibling}` resolves RELATIVE to the file.
Writing it to a bare temp dir makes every multi-file document report a spurious
"T2 project not closed" — I hit exactly that while measuring, and it would have
made this gate cry wolf on `good_input_child.tex`.

USAGE
    check_apply_fixes_roundtrip.py [--repo DIR] [--record] [--require-pdflatex]

  --record   re-measure and rewrite the manifest baseline (deliberate act)

EXIT 0 clean | 1 a NEW breakage or an unrecorded improvement | 2 infrastructure
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

CORPORA = ["corpora/compile_check", "corpora/apply_fixes"]
MANIFEST = "corpora/apply_fixes/manifest.json"
# TWO ORTHOGONAL AXES, and both matter:
#   flag    --apply-fixes converges internally; --apply-fixes-best-effort is one pass
#   profile default vs L0_VALIDATORS=pilot — pilot is a REAL shipping profile
#           (scripts/tools/diff_compile_check.sh:48 exports it) and is strictly
#           MORE destructive. Measured: good_longtable_free.tex is corrupted only
#           under pilot (`>{\bfseries}` -> `\textgreater{}{\bfseries}`, an illegal
#           pream-token, pdflatex 0 -> 1). Varying only the flag misses that class
#           entirely, which is exactly what my first version of this gate did.
FLAGS = ["--apply-fixes", "--apply-fixes-best-effort"]
PROFILES = [("default", {}), ("pilot", {"L0_VALIDATORS": "pilot"})]
CELLS = [(pname, penv, flag) for pname, penv in PROFILES for flag in FLAGS]
MIN_DOCS = 60  # compile_check alone is 65 standalone docs; a smaller sweep is a bug


def die(msg: str) -> int:
    print(f"[fixer-roundtrip] FATAL: {msg}", file=sys.stderr)
    return 2


def find_timeout() -> str | None:
    return shutil.which("gtimeout") or shutil.which("timeout")


def pdflatex_ok(workdir: Path, base: str, timeout_bin: str | None, secs: int = 60) -> bool | None:
    """True=compiles, False=fails, None=could not be graded (timeout/not run)."""
    cmd = ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", base]
    if timeout_bin:
        cmd = [timeout_bin, str(secs)] + cmd
    p = subprocess.run(cmd, cwd=workdir, capture_output=True)
    if p.returncode in (124, 125, 126, 127):
        return None
    return p.returncode == 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=".")
    ap.add_argument("--record", action="store_true",
                    help="re-measure and rewrite the manifest baseline")
    ap.add_argument("--require-pdflatex", action="store_true",
                    help="fail rather than skip when pdflatex is unavailable")
    args = ap.parse_args()
    repo = Path(args.repo).resolve()

    cli = repo / "_build/default/latex-parse/src/validators_cli.exe"
    if not cli.exists():
        return die(f"CLI not built at {cli} (build it in its own step)")
    # A CLI that cannot execute answers non-zero to everything, which would read
    # as a uniform column of NOT-READY and grade perfectly `ok`.
    banner = subprocess.run([str(cli)], capture_output=True)
    if b"Usage:" not in (banner.stdout + banner.stderr):
        return die("the CLI did not produce its usage banner — it cannot execute here")

    require_tex = args.require_pdflatex or os.environ.get("REQUIRE_PDFLATEX") == "1"
    have_tex = shutil.which("pdflatex") is not None
    if require_tex and not have_tex:
        return die("REQUIRE_PDFLATEX=1 but pdflatex is not on PATH")
    timeout_bin = find_timeout()
    if have_tex and not timeout_bin and require_tex:
        return die("pdflatex present but no gtimeout/timeout; a hang would be scored as a failure")

    manifest_path = repo / MANIFEST
    recorded: dict[str, dict] = {}
    if manifest_path.exists():
        try:
            # Key by (doc, MODE): a document can break under one fixer mode and
            # not the other, and keying by doc alone silently collapses them so
            # one mode's baseline masks the other's.
            recorded = {(e["doc"], e["mode"]): e
                        for e in json.loads(manifest_path.read_text())["known_broken"]}
        except Exception as exc:  # noqa: BLE001
            return die(f"cannot parse {MANIFEST}: {exc}")
    elif not args.record:
        return die(f"{MANIFEST} missing — run with --record to create the baseline")

    # REFUSE to re-record a pdflatex-graded baseline on a runner without TeX.
    # Property (b) is the only one that can see the fixer break a compiling
    # document, and without pdflatex `broke` is False for EVERY cell — so a
    # --record here silently deletes every breaks_compile row while leaving an
    # oracle block that still claims it was graded against TL2026. The result
    # looks like a clean baseline and is actually a blindfolded one.
    #
    # Checked HERE rather than at the write, so it costs nothing: the refusal
    # lands before the 73-document sweep instead of after it.
    if args.record and not have_tex and manifest_path.exists():
        # Catch only what reading JSON can genuinely raise. A broad except here
        # treated a CORRUPT manifest as "not pdflatex_graded" and then allowed
        # the --record it exists to prevent — erasing every breaks_compile row.
        # The safe reading of "I cannot tell" is REFUSE, not proceed.
        try:
            prior_graded = json.loads(manifest_path.read_text()).get("pdflatex_graded")
        except (json.JSONDecodeError, OSError) as exc:
            return die(f"cannot read {MANIFEST} to check whether it is "
                       f"pdflatex-graded ({exc}); refusing to --record, because "
                       f"if it IS graded this would erase every breaks_compile "
                       f"row")
        if prior_graded:
            return die(
                "refusing to re-record: the existing baseline is pdflatex_graded "
                "but pdflatex is not on PATH, so every breaks_compile row would "
                "be erased. Re-record inside the pinned image — tex-oracle.yml "
                "already runs this script there.")

    findings: list[str] = []
    observed_broken: list[dict] = []
    n_docs = 0
    n_changed = 0
    ungraded = 0

    for corpus_rel in CORPORA:
        corpus = repo / corpus_rel
        if not corpus.is_dir():
            return die(f"corpus directory missing: {corpus_rel}")
        docs = sorted(p for p in corpus.glob("*.tex") if not p.name.endswith("_part.tex"))
        # Fixtures whose only role is to be \input by another fixture are not
        # standalone documents; skip them the way the differential does.
        docs = [p for p in docs if not p.name.startswith("adv--")]
        if not docs:
            return die(f"no documents found in {corpus_rel} — refusing to report success")

        for doc in docs:
            n_docs += 1
            base = doc.name
            key = f"{corpus_rel}/{base}"
            before_ready = subprocess.run(
                [str(cli), "--compile-check", str(doc)],
                capture_output=True).returncode == 0

            # (b) BEFORE-half, hoisted out of the cell loop. The pristine
            # compile depends only on the DOCUMENT, never on the fixer cell, so
            # grading it once per doc instead of once per cell removes three of
            # every four pdflatex runs on this half (576 -> 360 across the
            # sweep) for a bit-identical answer. That is what makes running
            # property (b) per-PR affordable rather than a ~25-minute tax.
            # b4 is bound OUTSIDE the have_tex guard on purpose: the cell loop
            # reads it unconditionally, so leaving it unbound would raise
            # UnboundLocalError on every no-pdflatex run — which is the path CI
            # actually takes today.
            b4: bool | None = None
            if have_tex:
                with tempfile.TemporaryDirectory(prefix="fixer-rt-pristine-") as ptmp:
                    pristine = Path(ptmp) / "p"
                    shutil.copytree(corpus, pristine)
                    b4 = pdflatex_ok(pristine, base, timeout_bin)

            for pname, penv, flag in CELLS:
                mode = f"{pname}:{flag}"
                env = {**os.environ, **penv}
                # Stage the WHOLE directory: \input{sibling} resolves relative to
                # the file, so a bare temp dir manufactures T2 failures.
                with tempfile.TemporaryDirectory(prefix="fixer-rt-") as tmp:
                    stage = Path(tmp) / "c"
                    shutil.copytree(corpus, stage)
                    # BYTES, not text. The corpus deliberately contains
                    # mis-encoded documents (that is part of what it tests), and
                    # the fixer is a byte-level rewriter — decoding its output as
                    # strict UTF-8 raises, and decoding it leniently would CORRUPT
                    # the very bytes we are trying to compare.
                    fixed = subprocess.run([str(cli), flag, str(doc)], capture_output=True, env=env)
                    if fixed.returncode not in (0, 1):
                        findings.append(f"{key} [{mode}]: fixer exited {fixed.returncode}")
                        continue
                    out = fixed.stdout
                    staged_doc = stage / base
                    if out != doc.read_bytes():
                        n_changed += 1
                    staged_doc.write_bytes(out)

                    # (a) idempotence
                    again = subprocess.run(
                        [str(cli), flag, str(staged_doc)], capture_output=True, env=env)
                    not_idem = again.returncode in (0, 1) and again.stdout != out

                    # (c) verdict-non-degradation
                    after_ready = subprocess.run(
                        [str(cli), "--compile-check", str(staged_doc)],
                        capture_output=True).returncode == 0
                    degraded = before_ready and not after_ready

                    # (b) oracle-class preservation. The AFTER half only:
                    # b4 was graded once per document above.
                    broke = False
                    if have_tex:
                        for junk in ("aux", "log", "pdf", "out"):
                            (stage / f"{base[:-4]}.{junk}").unlink(missing_ok=True)
                        af = pdflatex_ok(stage, base, timeout_bin)
                        if b4 is None or af is None:
                            ungraded += 1
                            findings.append(f"{key} [{mode}]: pdflatex could not be graded")
                        else:
                            broke = b4 and not af

                    # (c') NO FIXER-MANUFACTURED FALSE-READY: if the fixed
                    # document still says READY while pdflatex now rejects it, the
                    # fixer has created the project's cardinal bug. This is the
                    # property that matters — plain verdict-monotonicity (c)
                    # catches NONE of the corpus breakages, because the checker
                    # keeps saying READY before and after.
                    manufactured = bool(broke and after_ready)
                    if broke or degraded or not_idem or manufactured:
                        entry = {"doc": key, "mode": mode,
                                 "breaks_compile": bool(broke),
                                 "degrades_verdict": bool(degraded),
                                 "not_idempotent": bool(not_idem),
                                 "manufactured_false_ready": manufactured}
                        observed_broken.append(entry)
                        prev = recorded.get((key, mode))
                        if not prev:
                            findings.append(
                                f"{key} [{mode}]: NEW FIXER DEFECT "
                                f"(breaks_compile={broke}, degrades_verdict={degraded}, "
                                f"not_idempotent={not_idem}, "
                                f"manufactured_false_ready={manufactured}) — the fixer damages or "
                                f"destabilises a document it was asked to improve")
                        else:
                            # Recorded, but make sure it has not got WORSE along an
                            # axis the baseline did not already admit.
                            for axis, now in (("breaks_compile", broke),
                                              ("degrades_verdict", degraded),
                                              ("not_idempotent", not_idem),
                                              ("manufactured_false_ready", manufactured)):
                                if now and not prev.get(axis):
                                    findings.append(
                                        f"{key} [{mode}]: newly {axis} (was recorded "
                                        f"broken only on other axes)")

    if n_docs < MIN_DOCS:
        return die(f"processed {n_docs} documents, expected at least {MIN_DOCS} "
                   f"(corpus misrooted?) — refusing to report success")
    if n_changed == 0:
        return die("the fixer changed NOTHING across the whole corpus — it is "
                   "not running; these results would be meaningless")

    # Unrecorded improvement: a recorded-broken doc that no longer breaks. Forces
    # the manifest to be updated so the baseline can only descend.
    observed_keys = {(e["doc"], e["mode"]) for e in observed_broken}
    if have_tex and not args.record:
        for (key, mode), entry in recorded.items():
            if (entry.get("breaks_compile") or entry.get("not_idempotent")) \
                    and (key, mode) not in observed_keys:
                findings.append(
                    f"{key} [{mode}]: recorded as broken but is now CLEAN — a fix landed; "
                    f"update {MANIFEST} to lock it in (--record)")

    if args.record:
        # CARRY FORWARD anything this writer does not own. The template below is
        # a fixed literal, so every top-level key absent from it is DESTROYED on
        # each --record. That is not hypothetical: the `oracle` block recording
        # which pdflatex graded this baseline was added separately, and
        # tex-oracle.yml now ASSERTS manifest["oracle"]["version"] against the
        # pinned image — so the next --record would have deleted the key and
        # turned that assertion into a KeyError rather than a readable failure.
        # Carrying unknown keys forward keeps a re-record from silently
        # discarding provenance that another gate depends on.
        owned = {"description", "properties", "pdflatex_graded", "known_broken"}
        carried: dict = {}
        if manifest_path.exists():
            # [carried = {}] on failure performs exactly the destruction this
            # block exists to prevent: it drops the `oracle` provenance block
            # that tex-oracle.yml pin-asserts. Unreadable means STOP.
            try:
                carried = {k: v for k, v in json.loads(manifest_path.read_text()).items()
                           if k not in owned}
            except (json.JSONDecodeError, OSError) as exc:
                return die(f"cannot read {MANIFEST} to carry its unowned keys "
                           f"forward ({exc}); refusing to --record rather than "
                           f"silently discarding the oracle provenance block")
        manifest_path.parent.mkdir(parents=True, exist_ok=True)
        manifest_path.write_text(json.dumps({
            "description": (
                "R7-INFRA-4 baseline: documents that --apply-fixes damages. Each "
                "entry is a KNOWN defect awaiting the R7-3 fixer guard. The gate "
                "fails on a NEW breakage and on an unrecorded improvement, so this "
                "list can only shrink."),
            "properties": {
                "a_idempotent": "applying twice == applying once",
                "c_verdict_non_degrading": "a READY document must not become NOT-READY",
                "b_oracle_class_preserving": "a document that compiled must still compile",
            },
            "pdflatex_graded": have_tex,
            **carried,
            "known_broken": sorted(observed_broken, key=lambda e: (e["doc"], e["mode"])),
        }, indent=2) + "\n", encoding="utf-8")
        print(f"[fixer-roundtrip] recorded {len(observed_broken)} known breakage(s) "
              f"to {MANIFEST}")
        return 0

    print(f"[fixer-roundtrip] {n_docs} documents x {len(CELLS)} cells (profile x flag); "
          f"fixer rewrote {n_changed}; pdflatex={'yes' if have_tex else 'NO (b skipped)'}; "
          f"known-broken {len(recorded)}")
    if not have_tex and not require_tex:
        print("[fixer-roundtrip] NOTE: property (b) not evaluated without pdflatex; "
              "the tex-oracle workflow covers it (advisory).")
    if findings:
        print("\n[fixer-roundtrip] FAIL:\n", file=sys.stderr)
        for f in findings:
            print(f"  - {f}", file=sys.stderr)
        return 1
    print("[fixer-roundtrip] PASS — no new fixer damage.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
