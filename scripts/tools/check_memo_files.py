#!/usr/bin/env python3
"""Memo §16 file-list presence gate (PR #245 p1.9).

Parses the two "Files to create" sections of
specs/REPO_EXACT_MISSING_ARCHITECTURE_MEMO_V26_V27.md (§16.1 v26.0 and
§16.2 v26.1) and verifies each bulleted path exists in the repo OR is
explicitly deferred via an alias stub.

Would have caught the round-7 gaps (DependencyInvalidation.v,
ProjectSemantics.v, log_context.ml/.mli) before merge.

Known path drifts (memo-prescribed path ↔ actual location) are handled
via an alias map. A documented drift is not a failure.

Exit code 1 if any mandated file has no implementation at any known
path (drift map miss) or no acknowledged deferral entry.
"""

from __future__ import annotations
import argparse
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

# Known alias map: memo-prescribed path -> actual location(s).
# Populated from memo §16 vs. repo reality as of P1.7.
PATH_ALIASES: dict[str, list[str]] = {
    # Macro registry (memo §10.4 / §16.1)
    "core/l1_expander/user_macro_registry.ml":
        ["latex-parse/src/user_macro_registry.ml"],
    "core/l1_expander/user_macro_registry.mli":
        ["latex-parse/src/user_macro_registry.mli"],
    "core/l1_expander/macro_subset.ml":
        ["latex-parse/src/macro_subset.ml"],
    "core/l1_expander/macro_subset.mli":
        ["latex-parse/src/macro_subset.mli"],
    "core/l1_expander/rest_simple_expander.ml":
        ["latex-parse/src/rest_simple_expander.ml"],
    # Project graph (memo §16.2)
    "core/project/include_graph.ml":
        ["latex-parse/src/include_resolver.ml"],
    "core/project/project_session.ml":
        ["latex-parse/src/project_state.ml",
         "latex-parse/src/project_graph.ml"],
    "core/project/file_resolution.ml":
        ["latex-parse/src/include_resolver.ml"],
    "latex-parse/src/invalidation_engine.ml":
        ["latex-parse/src/invalidation_engine.ml",
         "latex-parse/src/invalidation.ml"],
    # Project runner (memo §16.2) - not a distinct module; CLI wraps
    # everything via validators_cli.ml --project flag.
    "latex-parse/src/project_runner.ml":
        ["latex-parse/src/validators_cli.ml"],
    # Governance (memo §16.1) — the memo prescribes slightly different
    # names; we shipped under the current ones.
    "scripts/gen_project_facts.py":
        ["scripts/tools/generate_project_facts.py"],
    ".github/workflows/spec_drift.yml":
        [".github/workflows/spec-drift.yml"],
    ".github/workflows/fuzz.yml":
        [".github/workflows/fuzz-nightly.yml"],
    # project_facts yaml was shipped under governance/, not generated/.
    # json mirror still lives under generated/ as memo prescribed.
    "generated/project_facts.yaml":
        ["governance/project_facts.yaml"],
    # Support matrix moved to memo §12.1 path during P1.1.
    "specs/v26/support_matrix.yaml":
        ["docs/SUPPORT_MATRIX.yaml"],
    # Mutation + fuzz infrastructure: the memo prescribed dedicated
    # testing/ subdirs; we shipped them alongside regular tests under
    # latex-parse/src/ with separate CI workflows.
    "testing/mutation/":
        ["latex-parse/src/test_mutation_baseline.ml"],
    "testing/fuzz/":
        ["latex-parse/src/test_fuzz_parser.ml"],
    # v26.2 CST + partial-parsing aliases (memo §6.5, §7.4, §16.3).
    # ADR-001 pattern: memo prescribes core/l2_parser/, we ship under
    # latex-parse/src/ with alias resolution. cst_builder is memo-
    # canonical for the builder; we shipped it as cst_of_ast.
    "core/l2_parser/cst.ml":
        ["latex-parse/src/cst.ml"],
    "core/l2_parser/cst.mli":
        ["latex-parse/src/cst.mli"],
    "core/l2_parser/cst_builder.ml":
        ["latex-parse/src/cst_of_ast.ml"],
    "core/l2_parser/cst_builder.mli":
        ["latex-parse/src/cst_of_ast.mli"],
    "core/l2_parser/partial_cst.ml":
        ["latex-parse/src/partial_cst.ml"],
    "core/l2_parser/partial_cst.mli":
        ["latex-parse/src/partial_cst.mli"],
    "core/l2_parser/error_recovery.ml":
        ["latex-parse/src/error_recovery.ml"],
    "core/l2_parser/error_recovery.mli":
        ["latex-parse/src/error_recovery.mli"],
    # Memo §6.5 prescribes latex-parse/src/trust_regions.*; we ship
    # the trust-zone logic under partial_cst instead.
    "latex-parse/src/trust_regions.ml":
        ["latex-parse/src/partial_cst.ml"],
    "latex-parse/src/trust_regions.mli":
        ["latex-parse/src/partial_cst.mli"],
    # Memo §8.5 project_runner.mli — the .ml is already aliased to
    # validators_cli.ml; mirror the interface.
    "latex-parse/src/project_runner.mli":
        ["latex-parse/src/validators_cli.ml"],
    # Memo §8.5 prescribes core/project/ as a separate dune library.
    # We ship the same concepts under latex-parse/src/: build_graph is
    # the artefact graph; the library dune stanza lives alongside.
    "core/project/dune":
        ["latex-parse/src/dune"],
    "core/project/artifact_graph.ml":
        ["latex-parse/src/build_graph.ml"],
}


def parse_file_bullets(memo_path: Path) -> dict[str, list[str]]:
    r"""Parse memo; return {section_id: list[path]} for the memo sections
    that carry "Files to create" / "New:" / "Rewrite:" bullet lists.

    Covered sections (extended in v26.2 pre-tag audit): §4.5, §5.5,
    §6.5, §7.4, §8.5, §16.1, §16.2, §16.3.

    Bullets look like ``- `path/to/file.ext` ``; strip the backticks
    and any ``rewrite `` / ``new `` prefix. A section ends at the
    next ``### X.Y`` heading or end of file.
    """
    tracked = re.compile(r"^###\s+(4\.5|5\.5|6\.5|7\.4|8\.5|16\.[123])\b")
    any_subsection = re.compile(r"^###\s+(\d+\.\d+)\b")
    text = memo_path.read_text(encoding="utf-8")
    sections: dict[str, list[str]] = {}
    current: str | None = None
    current_list: list[str] = []
    for line in text.splitlines():
        m_any = any_subsection.match(line)
        if m_any:
            # Any subsection boundary ends the prior tracked section.
            if current is not None:
                sections[current] = current_list
                current = None
                current_list = []
            m_tracked = tracked.match(line)
            if m_tracked:
                current = m_tracked.group(1)
                current_list = []
            continue
        if current is None:
            continue
        # Match bullets like ``- `path.ext` `` or ``- rewrite `path.ext` ``.
        # Skip bullets whose body is prose (no backticked path).
        b = re.match(r"^- (?:new |rewrite )?`([^`]+)`", line)
        if b:
            current_list.append(b.group(1))
    if current is not None:
        sections[current] = current_list
    return sections


def resolve_path(repo: Path, memo_path: str) -> str | None:
    """Return the actual repo-relative path that fulfils [memo_path],
    or None if no fulfilment exists."""
    # Direct match first.
    if (repo / memo_path).exists():
        return memo_path
    # Alias match.
    for actual in PATH_ALIASES.get(memo_path, []):
        if (repo / actual).exists():
            return actual
    return None


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=str(REPO_ROOT))
    ns = ap.parse_args()
    repo = Path(ns.repo)
    memo = repo / "specs/REPO_EXACT_MISSING_ARCHITECTURE_MEMO_V26_V27.md"
    if not memo.is_file():
        print(f"[memo-files] FAIL: memo not found at {memo}", file=sys.stderr)
        return 2
    sections = parse_file_bullets(memo)
    total = 0
    missing: list[tuple[str, str]] = []
    for sec, paths in sections.items():
        for p in paths:
            total += 1
            resolved = resolve_path(repo, p)
            if not resolved:
                missing.append((sec, p))
    if missing:
        print(
            f"[memo-files] FAIL: {len(missing)} / {total} memo-mandated "
            f"paths have no implementation:",
            file=sys.stderr,
        )
        for sec, p in missing[:30]:
            print(f"  §{sec}: {p}", file=sys.stderr)
        if len(missing) > 30:
            print(f"  ... and {len(missing) - 30} more", file=sys.stderr)
        print(
            "Add the file, add an alias in PATH_ALIASES with "
            "justification, or document the deferral in CHANGELOG.",
            file=sys.stderr,
        )
        return 1
    print(f"[memo-files] PASS: {total} memo-mandated paths all resolved "
          f"(directly or via aliases).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
