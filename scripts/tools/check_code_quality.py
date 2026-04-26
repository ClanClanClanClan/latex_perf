#!/usr/bin/env python3
"""Code-quality gates (PR #245 p1.10).

Three lightweight gates bundled into one script:

  A. `Defined.` audit in load-bearing proofs. [Defined.] leaks proof
     terms into definitional equality — dangerous for larger developments.
     Load-bearing files should always close with [Qed.].

  B. Silent-exception-swallow in non-test OCaml. Patterns like
     `try ... with _ -> ()` or `with _ -> ""` discard error information
     and produce invisible data loss. Intentional uses should be
     marked with `(* EXN-OK: <reason> *)`.

  C. Test-assertion triviality. `expect true`, `expect (x = x)`,
     `expect (0 = 0)` etc. pass trivially without testing anything.

Each gate reports PASS / FAIL independently. All three must PASS for
the script to exit 0.
"""

from __future__ import annotations
import argparse
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

LOAD_BEARING_PROOFS = [
    "proofs/BuildLog.v",
    "proofs/LanguageContract.v",
    "proofs/ExecutionClasses.v",
    "proofs/RepairMonotonicity.v",
    "proofs/StableNodeIds.v",
    "proofs/UserMacroTermination.v",
    "proofs/UserMacroRegistrySound.v",
    "proofs/ValidatorGraphProofs.v",
    "proofs/PartialParseLocality.v",
    "proofs/DamageContainment.v",
    "proofs/UserExpand.v",
    "proofs/IncludeGraphSound.v",
    "proofs/InvalidationSound.v",
    "proofs/DependencyInvalidation.v",
    "proofs/ProjectSemantics.v",
]


def gate_defined_audit(repo: Path) -> list[str]:
    failures: list[str] = []
    files_scanned = 0
    for rel in LOAD_BEARING_PROOFS:
        path = repo / rel
        if not path.is_file():
            continue
        files_scanned += 1
        for i, line in enumerate(path.read_text().splitlines(), 1):
            if re.match(r"^\s*Defined\.\s*$", line):
                context_start = max(0, i - 5)
                preview = "\n".join(
                    path.read_text().splitlines()[context_start:i]
                )
                if "ANTI-TAUT-OK" in preview or "DEFINED-OK" in preview:
                    continue
                failures.append(
                    f"{rel}:{i}: [Defined.] in load-bearing proof. Use "
                    f"[Qed.] to keep proof term opaque, or mark with "
                    f"`(* DEFINED-OK: <reason> *)`."
                )
    # Silent-failure guard: refuse to report PASS if most LOAD_BEARING
    # files were missing (would mean the gate scanned almost nothing).
    min_required = max(1, (len(LOAD_BEARING_PROOFS) * 8) // 10)
    if files_scanned < min_required:
        failures.append(
            f"only {files_scanned} of {len(LOAD_BEARING_PROOFS)} "
            f"LOAD_BEARING_PROOFS files were found — update the list "
            f"in this script to match the current layout. Refusing "
            f"to silent-pass."
        )
    return failures


# Truly silent: wildcard `_` (not a named exception) discarded to a
# trivial value. Named exceptions like [Not_found] are idiomatic control
# flow and NOT flagged here.
SWALLOW_PATTERN = re.compile(
    r"with\s+_\s*->\s*(?:\(\s*\)|\"\"|None|false|\[\s*\])"
)

# Current tree has some legacy silent swallows. Ratchet: block new
# additions but permit existing count.
EXN_SWALLOW_CEILING = 0  # P1.10 baseline — enforce zero new.


def gate_exception_swallow(repo: Path) -> list[str]:
    failures: list[str] = []
    src_dir = repo / "latex-parse/src"
    files_scanned = 0
    for p in sorted(src_dir.glob("*.ml")):
        if (
            p.name.startswith("test_")
            or "conflicted" in p.name
            or p.name in {"fault_injection.ml"}
        ):
            continue
        files_scanned += 1
        lines = p.read_text().splitlines()
        for i, line in enumerate(lines, 1):
            # EXN-OK marker may be on this line or within the prior
            # 2 lines (common OCaml formatting puts the comment above).
            window = "\n".join(lines[max(0, i - 3): i + 1])
            if "EXN-OK" in window:
                continue
            m = SWALLOW_PATTERN.search(line)
            if m:
                failures.append(
                    f"{p.name}:{i}: silent exception swallow "
                    f"`{m.group(0)!s}` (wildcard `_`). Replace with "
                    f"explicit exception name or mark with "
                    f"`(* EXN-OK: <reason> *)`."
                )
    # Silent-failure guard: latex-parse/src has tens of .ml files at
    # any maturity. Empty glob means the directory moved/renamed.
    if files_scanned < 10:
        failures.append(
            f"only {files_scanned} non-test .ml files found under "
            f"latex-parse/src — has the layout changed? Refusing to "
            f"silent-pass."
        )
    return failures


# Patterns like:  expect true
#                 expect (true = true)
#                 expect (x = x)   -- but we can't know x statically
TRIVIAL_EXPECT_PATTERNS = [
    re.compile(r"\bexpect\s+true\s"),
    re.compile(r"\bexpect\s*\(\s*true\s*=\s*true"),
    re.compile(r"\bexpect\s*\(\s*false\s*=\s*false"),
    re.compile(r"\bexpect\s*\(\s*0\s*=\s*0"),
    re.compile(r"\bexpect\s*\(\s*1\s*=\s*1"),
    re.compile(r"\bexpect\s*\(\s*\[\]\s*=\s*\[\]"),
]


# Ratchet: legitimate smoke-test pattern is `expect true` after a
# computation that could raise. Blocking all would require
# distinguishing smoke-tests from trivially-passing ones. For now
# we only flag the constant-equality patterns (`x = x`-shaped) that
# are unambiguously useless; raw `expect true` is ratcheted.
TRIVIAL_EXPECT_CEILING = 40  # P1.10 baseline for `expect true` smoke tests


def gate_test_triviality(repo: Path) -> list[str]:
    failures: list[str] = []
    smoke_count = 0
    src_dir = repo / "latex-parse/src"
    files_scanned = 0
    for p in sorted(src_dir.glob("test_*.ml")):
        if "conflicted" in p.name:
            continue
        files_scanned += 1
        for i, line in enumerate(p.read_text().splitlines(), 1):
            for pat in TRIVIAL_EXPECT_PATTERNS[1:]:
                # Skip the first pattern (`expect true`) — it's the
                # smoke-test pattern we ratchet.
                if pat.search(line):
                    failures.append(
                        f"{p.name}:{i}: unambiguously trivial "
                        f"assertion `{line.strip()[:80]}`. "
                        f"Replace with a real test."
                    )
                    break
            if TRIVIAL_EXPECT_PATTERNS[0].search(line):
                smoke_count += 1
    # Silent-failure guard: the test_*.ml glob should match at least a
    # handful of files. Zero means the layout changed.
    if files_scanned < 5:
        failures.append(
            f"only {files_scanned} test_*.ml files found under "
            f"latex-parse/src — has the layout changed? Refusing to "
            f"silent-pass."
        )
    if smoke_count > TRIVIAL_EXPECT_CEILING:
        failures.append(
            f"`expect true` smoke-test count {smoke_count} exceeds "
            f"ceiling {TRIVIAL_EXPECT_CEILING}. Ratchet prevents "
            f"unbounded growth; tighten existing tests first."
        )
    return failures


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=str(REPO_ROOT))
    ns = ap.parse_args()
    repo = Path(ns.repo)
    any_failed = False
    for name, fn in [
        ("Defined. audit", gate_defined_audit),
        ("Exception swallow", gate_exception_swallow),
        ("Test triviality", gate_test_triviality),
    ]:
        failures = fn(repo)
        if failures:
            any_failed = True
            for f in failures[:10]:
                print(f"[code-quality] {name}: FAIL: {f}", file=sys.stderr)
            if len(failures) > 10:
                print(f"  ... and {len(failures) - 10} more")
        else:
            print(f"[code-quality] {name}: PASS")
    return 1 if any_failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
