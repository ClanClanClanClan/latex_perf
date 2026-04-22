#!/usr/bin/env python3
"""Unused-hypothesis gate (PR #245 p1.10).

Round-5 audit found the E2 theorem
[repair_restores_trust_outside_boundaries] had the body

    intros z old_errs new_errs deps [Hsub _] _ _ Htrust e Hin.
    apply Htrust. apply Hsub. exact Hin.

Three hypotheses were discarded via bare `_` tokens (strict_subset's
length component, errors_disjoint_from_boundaries, zone_disjoint_
from_all_boundaries). The theorem claimed boundary-awareness but the
proof didn't use boundary information — the claim was weaker than the
name. The existing [check_proof_substance.py] doesn't catch this
because the proof uses [apply] (which it treats as composition).

This gate counts bare `_` tokens in top-level [intros ...] statements
in load-bearing proof files. When the count exceeds a threshold (≥ 2
by default), it flags the theorem for review. The intent: either
the theorem has over-quantified hypotheses (rename or remove) or the
proof is ignoring constraints that should be load-bearing.

Rules:
  - `_` inside `[...]` patterns (destructuring) is fine — it extracts
    a component of a structure. Only bare top-level `_` positions count.
  - ANTI-TAUT-OK escape still applies.
  - Threshold: ≥ 2 bare underscores in a single `intros` call is
    suspicious.

Exit 1 if any load-bearing proof has a theorem that discards ≥2
hypotheses without justification.
"""

from __future__ import annotations
import argparse
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

LOAD_BEARING = [
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

THRESHOLD = 2  # 2+ bare underscores = suspicious


def extract_proof_blocks(text: str) -> list[tuple[int, str]]:
    """Return list of (line_number_of_Proof, proof_body)."""
    blocks: list[tuple[int, str]] = []
    lines = text.splitlines()
    i = 0
    while i < len(lines):
        m = re.match(r"^\s*Proof\.\s*(.*)", lines[i])
        if m:
            start = i + 1
            body_parts = []
            rem = m.group(1)
            if rem:
                term = re.search(r"(Qed\.|Defined\.|Admitted\.)", rem)
                if term:
                    body_parts.append(rem[: term.start()])
                    blocks.append((start, " ".join(body_parts)))
                    i += 1
                    continue
                body_parts.append(rem)
            i += 1
            while i < len(lines):
                l = lines[i]
                term = re.search(r"(Qed\.|Defined\.|Admitted\.)", l)
                if term:
                    body_parts.append(l[: term.start()])
                    blocks.append((start, " ".join(body_parts)))
                    i += 1
                    break
                body_parts.append(l)
                i += 1
        else:
            i += 1
    return blocks


def count_bare_underscores(intros_args: str) -> int:
    """Count `_` tokens NOT inside `[...]` destructuring patterns
    and NOT followed immediately by an identifier suffix (like `_foo`)."""
    # Strip bracketed destructuring patterns.
    stripped = re.sub(r"\[[^\]]*\]", "", intros_args)
    # Now count bare `_` tokens: underscore followed by whitespace or end.
    tokens = re.findall(r"(?:^|\s)(_)(?:\s|$|\.)", " " + stripped + " ")
    return len(tokens)


def find_discarding_intros(body: str) -> list[int]:
    """Return list of bare-underscore counts for each intros call in
    the body that has ≥ THRESHOLD discards."""
    if "ANTI-TAUT-OK" in body:
        return []
    # Strip comments
    clean = re.sub(r"\(\*[^*]*(?:\*[^)][^*]*)*\*\)", " ", body)
    # Find `intros` or `intro` followed by args up to `.` or `;`
    counts = []
    for m in re.finditer(r"\bintros?\b\s+([^.;]+)", clean):
        args = m.group(1)
        n = count_bare_underscores(args)
        if n >= THRESHOLD:
            counts.append(n)
    return counts


def check_file(path: Path) -> list[tuple[int, int, str]]:
    text = path.read_text(encoding="utf-8")
    blocks = extract_proof_blocks(text)
    flagged: list[tuple[int, int, str]] = []
    for line_no, body in blocks:
        discards = find_discarding_intros(body)
        if discards:
            n = max(discards)
            preview = body[:140].replace("\n", " ")
            flagged.append((line_no, n, preview))
    return flagged


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=str(REPO_ROOT))
    ns = ap.parse_args()
    repo = Path(ns.repo)
    any_flagged = False
    for rel in LOAD_BEARING:
        path = repo / rel
        if not path.is_file():
            continue
        for line_no, n, preview in check_file(path):
            any_flagged = True
            print(
                f"[unused-hyps] FAIL: {rel}:{line_no}: "
                f"{n} bare underscores in intros. Theorem discards "
                f"{n} hypotheses without justification. Either the "
                f"theorem is over-quantified (remove unused binders) "
                f"or the proof is ignoring a constraint that should "
                f"be load-bearing. Body preview: {preview!r}",
                file=sys.stderr,
            )
    if any_flagged:
        print(
            "[unused-hyps] Rename the unused hypotheses (make them "
            "load-bearing), drop them from the theorem statement, or "
            "mark the proof with `(* ANTI-TAUT-OK: <reason> *)` if the "
            "extra quantifiers are intentional scaffolding.",
            file=sys.stderr,
        )
        return 1
    print(
        f"[unused-hyps] PASS: no load-bearing proof discards ≥{THRESHOLD} "
        "hypotheses without justification."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
