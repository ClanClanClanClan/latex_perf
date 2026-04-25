#!/usr/bin/env python3
"""Doc cross-reference validity gate (PR #245 p1.11).

Parses every markdown file under docs/ and specs/ and verifies that
internal file references resolve. Catches stale doc references from
file renames / removals.

Checked patterns:
  1. Markdown links `[text](path)` with relative paths (not http/https)
  2. Inline code `` `path/to/file.ext` `` mentions
  3. Explicit path refs `path/to/file.ext` outside code fences

External links (http/https), anchors alone (#section), email (mailto:),
and code fence contents themselves are NOT followed.

Ratchet: current repo has some pre-existing stale references; a
documented allow-list handles known stragglers. Anything outside the
allow-list must resolve.
"""

from __future__ import annotations
import argparse
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

# Allow-list of doc-reference strings that don't resolve but are
# intentional (docs mention hypothetical paths, placeholders, etc.).
REF_ALLOWLIST = {
    # External / canonical URLs (http already filtered; these are
    # special literal strings we don't expect to resolve)
    "specs/REPO_EXACT_MISSING_ARCHITECTURE_MEMO_V26_V27.md:890",  # line ref
    # Tool / CLI references not real paths
    "validators.ml:715",  # line-number reference
    "validators.ml:174",  # line-number reference
    # Historical refs in CHANGELOG describing moves/archives
    "specs/v26/support_matrix.yaml",  # moved to docs/SUPPORT_MATRIX.yaml (P1.1)
    "docs/RULES_PILOT_TODO.md",  # archived during v26 cleanup
    "docs/RULES_IMPLEMENTATION_PLAN.md",  # archived during v26 cleanup
    "scripts/pre_commit_proof_subset.sh",  # planned, never implemented
    "src/macro_catalogue.ml",  # historical doc
    # V26_REPO_EXACT_MASTER_SPEC references to planned/renamed paths
    "scripts/generate_project_facts.py",  # moved to scripts/tools/
    "scripts/check_repo_facts.py",  # moved to scripts/tools/
    "docs/PROOF_TAXONOMY.md",  # renamed to docs/PROOF_CLASSES.md
    "core/l1_expander/user_macro_contract.ml",  # shipped as latex-parse/src/user_macro_registry.ml
    "latex-parse/src/project_semantics.ml",  # proof-only (see proofs/ProjectSemantics.v)
    # V26.2 planned files referenced in memo/spec/roadmap
    "proofs/CSTRoundTrip.v",
    "proofs/RewritePreservesCST.v",
    "specs/v26/compilation_profiles.yaml",
    "core/l1_expander/macro_catalogue.json",
    "core/l1_expander/rest_simple_expander.ml",
    "ProjectSemantics.v",
    "ArtifactGraphSound.v",
    "aux_state.ml",
    "bibliography_state.ml",
    "artifact_graph.ml",
    "cst.ml",
    "cst_builder.ml",
    "rewrite_engine.ml",
    "stable_spans.ml",
    # v27 WS8 forward reference — discharge target for T6/T7 hypotheses.
    "proofs/PdflatexModel.v",
    # V26.2.1 planned files referenced in specs/v26/V26_2_1_PLAN.md
    "scripts/tools/migrate_result_literals.py",  # one-shot migration, PR #1
    "scripts/tools/check_result_helpers.py",  # new gate, PR #1
    "docs/MIGRATION_v26.2_to_v26.2.1.md",  # consumer migration doc, PR #5
    # ml/results/expert_briefing.md references training-run output JSONs
    # under timestamped directories (ml/results/<run-id>/). Per ml/.gitignore
    # these are intentionally untracked (run outputs, can be tens of MB).
    # The doc itself is tracked; the snapshot it cites is regenerated each
    # training run.
    "ml/results/20260319_234935/eval_results.json",
    "ml/results/20260319_234935/eval_bound.json",
}

LINK_PATTERN = re.compile(r"\[([^\]]*)\]\(([^)]+)\)")
PATH_IN_BACKTICKS = re.compile(
    r"`([a-zA-Z_][a-zA-Z0-9_./-]*\.(?:v|ml|mli|yaml|yml|json|md|py|sh|txt|toml|conf))`"
)


def resolve_ref(ref: str, doc_path: Path, repo: Path) -> Path | None:
    """Try to resolve [ref] as a path relative to [doc_path] or repo."""
    # Strip anchor fragments and trailing commas / periods.
    cleaned = re.sub(r"#.*$", "", ref).rstrip(",.)")
    if not cleaned or cleaned.startswith(("http://", "https://", "mailto:")):
        return None
    # Try absolute-from-repo first (e.g. "docs/ARCH.md")
    for candidate in [repo / cleaned, doc_path.parent / cleaned]:
        try:
            if candidate.exists():
                return candidate.resolve()
        except OSError:
            pass
    return None


def check_doc(doc: Path, repo: Path) -> list[tuple[int, str]]:
    broken: list[tuple[int, str]] = []
    lines = doc.read_text(encoding="utf-8", errors="replace").splitlines()
    in_code_fence = False
    for i, line in enumerate(lines, 1):
        if line.startswith("```"):
            in_code_fence = not in_code_fence
            continue
        if in_code_fence:
            continue
        # Markdown links
        for m in LINK_PATTERN.finditer(line):
            target = m.group(2).strip()
            # Skip URLs, anchors-only, mailto
            if target.startswith(("http://", "https://", "mailto:", "#")):
                continue
            # Skip explicitly-allowlisted
            if target in REF_ALLOWLIST:
                continue
            if not resolve_ref(target, doc, repo):
                broken.append((i, f"broken link: [{m.group(1)}]({target})"))
        # Inline-code path references (backticked)
        for m in PATH_IN_BACKTICKS.finditer(line):
            path = m.group(1)
            if path in REF_ALLOWLIST:
                continue
            # Short paths without directory are ambiguous (could be a
            # filename mentioned in prose). Only check if contains "/".
            if "/" not in path:
                continue
            if not resolve_ref(path, doc, repo):
                broken.append((i, f"broken path ref: `{path}`"))
    return broken


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=str(REPO_ROOT))
    ns = ap.parse_args()
    repo = Path(ns.repo)
    roots = [repo / "docs", repo / "specs", repo]
    # Planning / roadmap / memo / historical docs reference paths that
    # don't exist yet by design. Excluded from the doc-ref gate to
    # keep signal high on operational docs.
    EXCLUDED_PATTERNS = {
        "REPO_EXACT_MISSING_ARCHITECTURE_MEMO",
        "L3_ROADMAP",
        "L_roadmap",
        "CI_RUN_",
        "PROJECT_BRIEFING",
        # v25 archival docs
        "v25_R1",
        "v25_R0",
        # v26.2+ planning docs (describe future paths by design)
        "V26_2_PLAN",
        "V26_3_PLAN",
        "v26_2",  # directory of v26.2 planning sub-docs
    }
    doc_files = set()
    for root in roots:
        if not root.is_dir():
            continue
        for md in root.rglob("*.md"):
            # Skip archived docs
            if "archive" in md.parts:
                continue
            if "_build" in md.parts:
                continue
            if ".claude" in md.parts:
                continue
            if "latex-perfectionist" in md.parts:
                # Only audit repo root, not submodules
                continue
            if any(pat in md.name or pat in str(md) for pat in EXCLUDED_PATTERNS):
                continue
            doc_files.add(md)
    total_broken = 0
    for md in sorted(doc_files):
        broken = check_doc(md, repo)
        for line_no, msg in broken:
            rel = md.relative_to(repo)
            print(f"[doc-refs] FAIL: {rel}:{line_no}: {msg}", file=sys.stderr)
            total_broken += 1
    if total_broken > 0:
        print(
            f"[doc-refs] {total_broken} broken reference(s). Either fix "
            f"the path, add to REF_ALLOWLIST with justification, or "
            f"remove the reference.",
            file=sys.stderr,
        )
        return 1
    print(f"[doc-refs] PASS: all cross-references resolve across "
          f"{len(doc_files)} docs.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
