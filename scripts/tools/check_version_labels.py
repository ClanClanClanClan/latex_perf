#!/usr/bin/env python3
"""check_version_labels.py — fail if a maintained doc carries a stale version/count LABEL.

Catches the recurring drift class where a heading or stamp names an OLD version (or an
OLD fix-producer count) while the content underneath is already current. `check_doc_refs`
validates that referenced paths exist and `check_repo_facts` validates the generated fact
files, but neither checks doc *label currency* — so this class recurred across three
release audits (v27.0.67 / v27.0.68): "## Current Status — v26.1", "latest tag v27.0.67",
"96 as of v27.0.67", "## Current State (v26.2)", "the current 32 fix-producing rules", and
a "current release master spec" pointer left aimed at the v26 spec.

Canonical sources:
  - version:        dune-project  `(version X.Y.Z)`
  - producer count: number of `produces_fix: true` lines in specs/rules/rule_contracts.yaml

Patterns (deliberately high-precision — calibrated against the live corpus so legitimate
historical references do NOT trip the gate, e.g. CHANGELOG entries, "shipped in vN"
provenance, and "annotation ... as of v27.0.42" stamps):

  A  '## Current State/Status (vX)'  or  '— vX'  heading label      vX must be current version
  B  'latest tag vX'                                                vX must be current version
  C  '[..](specs/vN/..) — current release master spec'             N must be current major
  D  'Fix producers ...: N as of vX'                               N == producer count, vX current
  E  'the current N fix-producing rules'                           N == producer count
  F  'N/M (~P%) shipped as of vX'                                  N == producer count, vX current

A version token in a doc passes if its components are a prefix of the canonical version
(so "v27", "v27.0", "v27.0.68" all pass when canonical is 27.0.68; "v27.0.67" / "v26.1" fail).

Scope: tracked *.md files, excluding CHANGELOG.md and anything under archive/, .claude/,
_build/, node_modules/, ml/ (historical / generated / experiment outputs).

Exit 0 if every label is current; exit 1 (listing each violation) otherwise.
"""

import argparse
import re
import subprocess
import sys
from pathlib import Path

EXCLUDE_SEGMENTS = ("/archive/", "/.claude/", "/_build/", "/node_modules/")
EXCLUDE_PREFIXES = ("archive/", "docs/archive/", ".claude/", "_build/", "node_modules/", "ml/")
EXCLUDE_BASENAMES = ("CHANGELOG.md",)

# Escape hatch: a violation whose offending text contains any allowlisted substring is
# skipped. Keep empty unless a genuinely-legitimate exception appears; document why.
ALLOWLIST: tuple[str, ...] = ()


def canonical_version(repo: Path) -> tuple[int, ...]:
    m = re.search(r"\(version\s+([0-9][0-9.]*)\)", (repo / "dune-project").read_text())
    if not m:
        raise SystemExit("[version-labels] ERROR: could not read version from dune-project")
    return tuple(int(p) for p in m.group(1).split("."))


def producer_count(repo: Path) -> int:
    text = (repo / "specs/rules/rule_contracts.yaml").read_text()
    return len(re.findall(r"^\s*produces_fix:\s*true\b", text, re.M))


def ver_components(token: str) -> tuple[int, ...]:
    """'v27.0.68' / '27.0' -> (27,0,68) / (27,0); stops at the first non-numeric part."""
    out: list[int] = []
    for p in token.lstrip("vV").split("."):
        if p.isdigit():
            out.append(int(p))
        else:
            break
    return tuple(out)


def version_is_current(token: str, canon: tuple[int, ...]) -> bool:
    doc = ver_components(token)
    return len(doc) > 0 and canon[: len(doc)] == doc


def tracked_md_files(repo: Path) -> list[Path]:
    try:
        out = subprocess.run(
            ["git", "ls-files", "*.md"], cwd=repo, capture_output=True, text=True, check=True
        ).stdout
        rels = [r for r in out.splitlines() if r]
    except Exception:
        rels = [str(p.relative_to(repo)) for p in repo.rglob("*.md")]
    keep = []
    for rel in rels:
        if any(seg in f"/{rel}" for seg in EXCLUDE_SEGMENTS):
            continue
        if rel.startswith(EXCLUDE_PREFIXES):
            continue
        if Path(rel).name in EXCLUDE_BASENAMES:
            continue
        keep.append(repo / rel)
    return keep


# Pattern A — "Current State/Status" heading whose label is a version (sep = ( — – - :)
RE_CURSTATE = re.compile(
    r"^#{1,6}[^\n]*?Current\s+Stat(?:e|us)\s*[\(\-—–:]\s*v?(\d+(?:\.\d+)+)",
    re.M | re.I,
)
RE_LATEST_TAG = re.compile(r"latest\s+tag\s*[`'\"]?\s*v?(\d+(?:\.\d+)+)", re.I)
RE_MASTER_SPEC = re.compile(
    r"specs/v(\d+)/[^\s)]+\)\**\s*[—–\-]\s*current release master spec", re.I
)
# Non-greedy [^\n]*? (not [^:\n]*) so an inline `produces_fix: true` colon inside the
# label text does not block the match; the count/version may wrap across one newline.
RE_FIX_PROD_ASOF = re.compile(
    r"[Ff]ix[- ]produc\w*[^\n]*?:\s*(\d+)\s+as of\s+v?(\d+(?:\.\d+)+)", re.I
)
RE_CURRENT_N_PROD = re.compile(r"current\s+(\d+)\s+fix[- ]?produc\w*\s+rules", re.I)
RE_SHIPPED_ASOF = re.compile(
    r"(\d+)\s*/\s*\d+\s*\([^)]*%\)\s*shipped\s+as of\s+v?(\d+(?:\.\d+)+)", re.I
)


def line_of(text: str, pos: int) -> int:
    return text.count("\n", 0, pos) + 1


def check_file(path: Path, rel: str, canon, prod, violations: list):
    text = path.read_text(encoding="utf-8", errors="ignore")

    def add(pos: int, msg: str):
        snippet = text[pos : text.find("\n", pos) if text.find("\n", pos) != -1 else len(text)]
        if any(a in snippet for a in ALLOWLIST):
            return
        violations.append(f"{rel}:{line_of(text, pos)}: {msg}")

    for m in RE_CURSTATE.finditer(text):
        if not version_is_current(m.group(1), canon):
            add(m.start(), f"'Current State/Status' label says v{m.group(1)} (current is "
                           f"v{'.'.join(map(str, canon))})")
    for m in RE_LATEST_TAG.finditer(text):
        if not version_is_current(m.group(1), canon):
            add(m.start(), f"'latest tag v{m.group(1)}' is stale (current is "
                           f"v{'.'.join(map(str, canon))})")
    for m in RE_MASTER_SPEC.finditer(text):
        if int(m.group(1)) != canon[0]:
            add(m.start(), f"'current release master spec' points at specs/v{m.group(1)}/ "
                           f"(current major is v{canon[0]})")
    for m in RE_FIX_PROD_ASOF.finditer(text):
        n, v = int(m.group(1)), m.group(2)
        if n != prod or not version_is_current(v, canon):
            add(m.start(), f"'Fix producers: {n} as of v{v}' stale (current is "
                           f"{prod} as of v{'.'.join(map(str, canon))})")
    for m in RE_CURRENT_N_PROD.finditer(text):
        if int(m.group(1)) != prod:
            add(m.start(), f"'current {m.group(1)} fix-producing rules' stale (current is {prod})")
    for m in RE_SHIPPED_ASOF.finditer(text):
        n, v = int(m.group(1)), m.group(2)
        if n != prod or not version_is_current(v, canon):
            add(m.start(), f"'{n}/... shipped as of v{v}' stale (current is "
                           f"{prod} as of v{'.'.join(map(str, canon))})")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=".", help="repo root (default: .)")
    ns = ap.parse_args()
    repo = Path(ns.repo).resolve()

    canon = canonical_version(repo)
    prod = producer_count(repo)
    files = tracked_md_files(repo)

    violations: list[str] = []
    for path in files:
        rel = str(path.relative_to(repo))
        try:
            check_file(path, rel, canon, prod, violations)
        except Exception as e:  # never let one unreadable file mask the gate
            violations.append(f"{rel}: ERROR reading/checking ({e})")

    if violations:
        print(f"[version-labels] FAIL: {len(violations)} stale label(s) "
              f"(canonical v{'.'.join(map(str, canon))} / {prod} producers):", file=sys.stderr)
        for v in violations:
            print(f"  {v}", file=sys.stderr)
        print("  Bump the label(s) to the current version/count, or add a documented "
              "ALLOWLIST entry if genuinely historical.", file=sys.stderr)
        return 1

    print(f"[version-labels] PASS: all version/count labels current across {len(files)} docs "
          f"(v{'.'.join(map(str, canon))} / {prod} producers).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
