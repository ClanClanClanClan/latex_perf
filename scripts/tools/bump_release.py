#!/usr/bin/env python3
"""bump_release.py — rewrite stale version/producer-count LABELS in maintained docs.

This is the WRITE counterpart to ``check_version_labels.py``. ``release.sh`` already
bumps ``dune-project`` and regenerates the generated files (opam, project_facts,
rule_contracts), but it does NOT touch the prose labels scattered across the
maintained ``*.md`` files — the README headings, the docs/index fix-count, the
specs READMEs, the CADENCE "N shipped as of vN" stamps, etc. Those were bumped by
hand every release, drifted repeatedly (three release audits caught stale labels),
and — now that ``check_version_labels.py`` runs inside the pre-release gate — a
stale label will actively FAIL a release.

This script closes that gap. It reads the canonical version and producer count the
*same way the gate does*:

  - version:        ``dune-project``  ``(version X.Y.Z)``
  - producer count: ``produces_fix: true`` lines in ``specs/rules/rule_contracts.yaml``

and rewrites every stale label to match, reusing the gate's own compiled patterns so
the set of sites updated is exactly the set of sites checked — they can never drift
apart. It is idempotent (re-running when everything is current changes nothing) and
granularity-preserving (a doc that says ``v27`` stays ``v27`` when 27 is still the
current major; only fully-stale tokens like ``v27.0.67`` are rewritten).

Typical use — inside the release flow, AFTER dune-project is bumped and the
generators have run so rule_contracts.yaml carries the new count:

    python3 scripts/tools/bump_release.py            # rewrite labels to canonical
    python3 scripts/tools/bump_release.py --version 27.0.73   # also bump dune-project first
    python3 scripts/tools/bump_release.py --dry-run  # show what would change, write nothing

Exit 0 on success (and the post-write ``check_version_labels`` gate passes); exit 1
if, after rewriting, any label is still stale (a site the gate checks but no pattern
here can rewrite — meaning a new pattern must be added to BOTH files).
"""

from __future__ import annotations

import argparse
import importlib.util
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent


def _load_gate():
    """Import check_version_labels as a module so we reuse ITS patterns/helpers.

    We depend on these names by reference, so assert they exist: if the gate is
    refactored and a pattern is renamed, fail LOUDLY here with a clear pointer
    rather than with an opaque AttributeError mid-rewrite (or, worse, by silently
    skipping a site the gate still checks)."""
    spec = importlib.util.spec_from_file_location(
        "check_version_labels", HERE / "check_version_labels.py"
    )
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    required = (
        "canonical_version", "producer_count", "ver_components", "version_is_current",
        "tracked_md_files", "line_of", "RE_CURSTATE", "RE_LATEST_TAG", "RE_MASTER_SPEC",
        "RE_FIX_PROD_ASOF", "RE_CURRENT_N_PROD", "RE_SHIPPED_ASOF", "RE_SHIPPED_PLAIN_ASOF",
    )
    missing = [n for n in required if not hasattr(mod, n)]
    if missing:
        raise SystemExit(
            "[bump] ERROR: check_version_labels.py is missing expected names "
            f"{missing}. The gate was refactored; update bump_release.py to match "
            "so the rewriter and the checker stay in sync.")
    return mod


GATE = _load_gate()


def set_dune_version(repo: Path, version: str, dry_run: bool) -> bool:
    """Rewrite dune-project's (version X.Y.Z). Returns True if it changed."""
    p = repo / "dune-project"
    text = p.read_text()
    new, n = re.subn(r"\(version\s+[0-9][0-9.]*\)", f"(version {version})", text)
    if n == 0:
        raise SystemExit("[bump] ERROR: no (version ...) line in dune-project")
    if new == text:
        return False
    print(f"  dune-project: (version {version})")
    if not dry_run:
        p.write_text(new)
    return True


def _ver_token(canon: tuple[int, ...], old: str) -> str:
    """New version digits at the SAME granularity as the old token (e.g. old
    '27.0.67' -> '27.0.73'; old '27.0' stays 2 components)."""
    ncomp = len(GATE.ver_components(old))
    return ".".join(str(c) for c in canon[:ncomp])


def plan_doc_edits(text: str, canon: tuple[int, ...], prod: int):
    """Return a list of (start, end, new_text, why) span edits for one document.

    Each gate pattern contributes the spans of its version/count capture groups,
    but only where the captured value is actually stale — so the result is
    idempotent and minimal.
    """
    edits: list[tuple[int, int, str, str]] = []

    def ver_edit(m, gi):
        tok = m.group(gi)
        if not GATE.version_is_current(tok, canon):
            edits.append((m.start(gi), m.end(gi), _ver_token(canon, tok),
                          f"v{tok}->v{_ver_token(canon, tok)}"))

    def count_edit(m, gi):
        if int(m.group(gi)) != prod:
            edits.append((m.start(gi), m.end(gi), str(prod),
                          f"count {m.group(gi)}->{prod}"))

    def major_edit(m, gi):  # RE_MASTER_SPEC: specs/vN/ — N is the major only
        if int(m.group(gi)) != canon[0]:
            edits.append((m.start(gi), m.end(gi), str(canon[0]),
                          f"major v{m.group(gi)}->v{canon[0]}"))

    for m in GATE.RE_CURSTATE.finditer(text):
        ver_edit(m, 1)
    for m in GATE.RE_LATEST_TAG.finditer(text):
        ver_edit(m, 1)
    for m in GATE.RE_MASTER_SPEC.finditer(text):
        major_edit(m, 1)
    for m in GATE.RE_FIX_PROD_ASOF.finditer(text):
        count_edit(m, 1)
        ver_edit(m, 2)
    for m in GATE.RE_CURRENT_N_PROD.finditer(text):
        count_edit(m, 1)
    for m in GATE.RE_SHIPPED_ASOF.finditer(text):
        count_edit(m, 1)
        ver_edit(m, 2)
    for m in GATE.RE_SHIPPED_PLAIN_ASOF.finditer(text):
        if m.start() > 0 and text[m.start() - 1] == "/":
            continue  # the 'N/M (P%)' form is owned by RE_SHIPPED_ASOF
        count_edit(m, 1)
        ver_edit(m, 2)
    return edits


def apply_edits(text: str, edits) -> str:
    # De-dup identical spans (two patterns can target the same token) and apply
    # in reverse offset order so earlier spans keep their positions.
    seen = set()
    uniq = []
    for s, e, new, why in sorted(edits, key=lambda x: x[0], reverse=True):
        if (s, e) in seen:
            continue
        seen.add((s, e))
        uniq.append((s, e, new))
    for s, e, new in uniq:
        text = text[:s] + new + text[e:]
    return text


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--repo", default=".", help="repo root (default: .)")
    ap.add_argument("--version", help="also bump dune-project to this X.Y.Z first")
    ap.add_argument("--dry-run", action="store_true",
                    help="print the changes that would be made; write nothing")
    ns = ap.parse_args()
    repo = Path(ns.repo).resolve()

    print(f"[bump] {'DRY-RUN — ' if ns.dry_run else ''}rewriting stale version/count labels")

    if ns.version:
        if not re.fullmatch(r"\d+\.\d+\.\d+", ns.version):
            raise SystemExit(f"[bump] ERROR: --version must be X.Y.Z, got {ns.version!r}")
        set_dune_version(repo, ns.version, ns.dry_run)

    # Canonical sources (read AFTER an optional --version bump). In --dry-run the
    # on-disk dune-project is unchanged, so honour --version for the preview.
    canon = (tuple(int(p) for p in ns.version.split(".")) if (ns.version and ns.dry_run)
             else GATE.canonical_version(repo))
    prod = GATE.producer_count(repo)
    print(f"[bump] canonical: v{'.'.join(map(str, canon))} / {prod} producers")

    files = GATE.tracked_md_files(repo)
    total = 0
    for path in files:
        rel = str(path.relative_to(repo))
        text = path.read_text(encoding="utf-8", errors="ignore")
        edits = plan_doc_edits(text, canon, prod)
        if not edits:
            continue
        total += len(edits)
        for s, _e, _new, why in sorted(edits, key=lambda x: x[0]):
            print(f"  {rel}:{GATE.line_of(text, s)}: {why}")
        if not ns.dry_run:
            path.write_text(apply_edits(text, edits), encoding="utf-8")

    if total == 0:
        print("[bump] nothing stale — all labels already current.")
    else:
        print(f"[bump] {'would rewrite' if ns.dry_run else 'rewrote'} {total} label(s).")

    if ns.dry_run:
        return 0

    # Self-verify with the very gate whose patterns we used to rewrite.
    print("[bump] verifying with check_version_labels.py ...")
    rc = subprocess.run([sys.executable, str(HERE / "check_version_labels.py"),
                         "--repo", str(repo)]).returncode
    if rc != 0:
        print("[bump] FAIL: labels still stale after rewrite — a gate pattern has no "
              "corresponding rewrite rule here; add it to plan_doc_edits().", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
