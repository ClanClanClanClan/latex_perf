#!/usr/bin/env python3
"""Anti-tautology gate v2 (PR #245 p1.9).

The original anti-tautology gate only caught one-line
`Proof. auto. Qed.` / `Proof. trivial. Qed.` patterns. Round-4/5 audit
found three hypothesis-restatement tautologies those patterns missed:

  (A) `Proof. auto. Qed.` for `forall l, P l -> P l`  — BuildLog §6
  (B) `Proof. intros Hall z Hin Hdisj. exact (Hall z Hin Hdisj). Qed.`
      — PartialParseLocality E0; goal = hypothesis applied to its own
      universally-quantified args.
  (C) `Proof. exact Hnot_acyclic. Qed.` — ValidatorGraphProofs; goal
      is literally the hypothesis.
  (D) `Proof. exact (Hvalid u v Hin). Qed.` — ValidatorGraphProofs;
      goal is a direct hypothesis instantiation.

This script flags proof bodies matching precisely these
hypothesis-restatement shapes in the load-bearing proof files.

A proof is flagged if ALL of the following hold:
  1. The Proof body contains NO substantive tactic from a whitelist
     (lia, induction, destruct, rewrite, inversion, simpl, split,
      apply-with-lemma-name, left, right, constructor, f_equal,
      contradiction, exfalso, discriminate, subst, unfold, assert,
      pose, specialize, reflexivity-after-simpl, injection, etc.).
  2. The body's only load-bearing move is either:
       - `exact <simple_ident>` where simple_ident is a bound
         hypothesis name, OR
       - `exact (<simple_ident> <args>)` — hypothesis applied to its
         own universally-quantified args.
  3. The body does NOT destructure with `[...|...]` (case analysis
     IS substantive even without subst/destruct tokens).

Escape hatch: any Proof block containing `(* ANTI-TAUT-OK: <reason> *)`
is exempt.

Exit code: 1 if any flagged proof; 0 otherwise.
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
    # OPEN-055: the capstone files were outside this gate, exactly as they
    # were outside check_unused_hypotheses.py (OPEN-054). Two gates, one
    # blind spot.
    "proofs/CompileProgress.v",
    "proofs/PdflatexModel.v",
    "proofs/PdflatexFatalChannels.v",
    "proofs/CompileGuaranteeBridge.v",
    "proofs/CompileWellFormed.v",
    "proofs/LexerFaithfulStep.v",
]

# Tactic tokens that almost always imply non-trivial proof content.
SUBSTANTIVE_TOKENS = {
    "lia", "induction", "destruct", "rewrite", "inversion", "simpl",
    "split", "left", "right", "constructor", "f_equal", "contradiction",
    "exfalso", "discriminate", "subst", "case", "cbn", "compute",
    "unfold", "assert", "pose", "specialize", "injection", "refine",
    "transitivity", "symmetry", "eexists", "exists",
}


def extract_proof_blocks(text: str) -> list[tuple[int, str]]:
    """Return list of (starting_line_number, proof_body_text) tuples."""
    blocks: list[tuple[int, str]] = []
    lines = text.splitlines()
    i = 0
    while i < len(lines):
        line = lines[i]
        m = re.match(r"^\s*Proof\.\s*(.*)", line)
        if m:
            start_line = i + 1
            remainder = m.group(1)
            body_parts: list[str] = []
            if remainder:
                term = re.search(r"(Qed\.|Defined\.|Admitted\.)", remainder)
                if term:
                    body_parts.append(remainder[: term.start()])
                    blocks.append((start_line, " ".join(body_parts)))
                    i += 1
                    continue
                else:
                    body_parts.append(remainder)
            i += 1
            while i < len(lines):
                l = lines[i]
                term = re.search(r"(Qed\.|Defined\.|Admitted\.)", l)
                if term:
                    body_parts.append(l[: term.start()])
                    blocks.append((start_line, " ".join(body_parts)))
                    i += 1
                    break
                body_parts.append(l)
                i += 1
            else:
                pass
        else:
            i += 1
    return blocks


def strip_comments(body: str) -> str:
    return re.sub(r"\(\*[^*]*(?:\*[^)][^*]*)*\*\)", " ", body)


def is_hypothesis_restatement(body: str) -> bool:
    """Return True if the proof body matches one of the known
    hypothesis-restatement shapes. Intentionally narrow."""
    if "ANTI-TAUT-OK" in body:
        return False
    clean = strip_comments(body)
    # Bullet-based case splits `-`, `+`, `*` imply case analysis — always
    # substantive. Also `{` / `}` focus blocks.
    if re.search(r"(^|\s)-\s|(^|\s)\+\s|(^|\s)\*\s|\{|\}", clean):
        return False
    # Pattern-destructuring `[ ... | ... ]` in intros is substantive.
    if re.search(r"\[[^\]]*\|", clean):
        return False
    # Any substantive tactic word present => not a tautology.
    tokens = set(re.findall(r"\b([a-z][a-zA-Z_0-9]*)\b", clean))
    if tokens & SUBSTANTIVE_TOKENS:
        return False
    # If body uses `apply` (even `apply Hyp`), it's doing composition
    # of hypothesis applications — proof reduces the goal step by step.
    # The round-5 tautologies had NO apply; they were pure intros+exact.
    if "apply" in tokens:
        return False
    # Shape A: `auto` / `trivial` as the only load-bearing move.
    if re.search(r"\b(auto|trivial)\s*\.", clean) and not (
        tokens & SUBSTANTIVE_TOKENS):
        # already caught by existing simple grep; duplicate here for
        # safety but don't double-flag (escape clause above).
        return True
    # Shape B/C/D: `exact <ident>` or `exact (<ident> ...)` with
    # `<ident>` being a bare simple name (likely hypothesis). `exact I`
    # / `exact eq_refl` / `exact True_intro` etc. are fine (they use
    # capital-letter first char or contain `.`).
    m = re.search(
        r"exact\s+(\(\s*)?([A-Za-z_][A-Za-z_0-9']*)",
        clean,
    )
    if not m:
        return False
    exact_head = m.group(2)
    # Capital-letter heads followed by lowercase are usually Coq
    # constructors (I, Some, None, None_intro, etc.) — exempt.
    # Hypothesis convention in this project: H*, H_*, single letters.
    # Apply hypothesis heuristic: starts with H or is a single letter.
    if re.fullmatch(r"[a-z]", exact_head):
        is_hypothesis = True
    elif exact_head.startswith("H"):
        is_hypothesis = True
    else:
        is_hypothesis = False
    if not is_hypothesis:
        return False
    # If body ALSO contains `apply` with a long name (likely a lemma
    # name, snake_case), the proof is doing lemma composition, not pure
    # restatement.
    if re.search(r"apply\s+[a-z][a-zA-Z_0-9]*_[a-zA-Z_0-9]+", clean):
        return False
    return True


# ── OPEN-055: convertible-iff tautologies ─────────────────────────────
#
# `gates_pass_iff` stated `all_static_gates_pass p pf <-> <that same
# conjunction>` and was proved `split; intros H; exact H` in both directions.
# It shipped for months under a header calling it "load-bearing, with
# substantive content", and THIS GATE MISSED IT TWICE OVER: CompileProgress.v
# was not in LOAD_BEARING, and even once added, `is_hypothesis_restatement`
# exits early on bullets ("always substantive") and on `split` being in
# SUBSTANTIVE_TOKENS — which is precisely how one proves an X <-> X iff.
#
# This arm is deliberately narrow: an `<->` STATEMENT whose proof consists of
# nothing but intros / split / bullets / exact / assumption. A sweep of all 63
# proof files found exactly ONE such theorem, so the pattern does not
# false-positive on this codebase.
_STMT_RE = re.compile(
    r"^\s*(?:Lemma|Theorem|Corollary|Proposition)\s+([A-Za-z_][\w']*)\s*:"
    r"(.*?)(?=^\s*Proof\.)", re.S | re.M)
_PROOF_RE = re.compile(
    r"^\s*Proof\.(.*?)(?:Qed\.|Defined\.|Admitted\.)", re.S | re.M)
# A tactic HEAD is the first word of a tactic: at the start, or after `.`,
# `;`, or a bullet. Matching bare words instead would treat bound variables
# like `pf` as tactics — that mistake made an earlier version of this check
# report zero on a file containing the very theorem it was written for.
_HEAD_RE = re.compile(r"(?:^|[.;]|\s[-+*]\s)\s*([a-zA-Z_][\w']*)")
_TRIVIAL_HEADS = {"intros", "intro", "split", "exact", "assumption",
                  "reflexivity"}


def find_convertible_iffs(text: str) -> list[tuple[int, str]]:
    """Flag `X <-> X` statements proved only by intros/split/exact."""
    out: list[tuple[int, str]] = []
    for m in _STMT_RE.finditer(text):
        stmt = strip_comments(m.group(2))
        if "<->" not in stmt:
            continue
        pm = _PROOF_RE.search(text, m.end())
        if pm is None:
            continue
        body = strip_comments(pm.group(1))
        if "ANTI-TAUT-OK" in body:
            continue
        heads = set(_HEAD_RE.findall(body))
        if heads and heads <= _TRIVIAL_HEADS:
            out.append((text[: m.start()].count("\n") + 1, m.group(1)))
    return out


def check_file(path: Path) -> list[tuple[int, str]]:
    text = path.read_text(encoding="utf-8")
    blocks = extract_proof_blocks(text)
    flagged: list[tuple[int, str]] = []
    for line_no, body in blocks:
        if is_hypothesis_restatement(body):
            flagged.append((line_no, body.strip()))
    return flagged


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=str(REPO_ROOT))
    ns = ap.parse_args()
    repo = Path(ns.repo)
    any_flagged = False
    files_scanned = 0
    missing_files: list[str] = []
    for rel in LOAD_BEARING:
        path = repo / rel
        if not path.is_file():
            missing_files.append(rel)
            continue
        files_scanned += 1
        for line_no, name in find_convertible_iffs(
                path.read_text(encoding="utf-8")):
            any_flagged = True
            print(
                f"[proof-substance] FAIL: {rel}:{line_no}: {name} is an "
                f"`X <-> X` restatement — its two sides are convertible and "
                f"the proof is only intros/split/exact. Delete it, or restate "
                f"it over a non-definitional aggregate (OPEN-055).",
                file=sys.stderr,
            )
        for line_no, body in check_file(path):
            any_flagged = True
            preview = body[:140].replace("\n", " ")
            print(
                f"[proof-substance] FAIL: {rel}:{line_no}: "
                f"hypothesis-restatement pattern. Body: {preview!r}",
                file=sys.stderr,
            )
    # Silent-failure guard: if too many LOAD_BEARING files have moved
    # or been renamed, the gate reports PASS without checking anything.
    # Demand at least 80% of the declared files actually scanned.
    min_required = max(1, (len(LOAD_BEARING) * 8) // 10)
    if files_scanned < min_required:
        print(
            f"[proof-substance] FAIL: only {files_scanned} of "
            f"{len(LOAD_BEARING)} declared load-bearing files were "
            f"found. Missing: {missing_files[:5]}{'...' if len(missing_files) > 5 else ''}. "
            f"Update LOAD_BEARING in this script to match the current "
            f"layout, or restore the missing files. Refusing to "
            f"silent-pass.",
            file=sys.stderr,
        )
        return 2
    if any_flagged:
        print(
            "[proof-substance] Either add a substantive tactic "
            "(lia, induction, destruct, rewrite, inversion, simpl, "
            "split, apply <lemma_name>, etc.) or mark with "
            "`(* ANTI-TAUT-OK: <reason> *)` if the proof is a "
            "legitimate base case.",
            file=sys.stderr,
        )
        return 1
    print(
        f"[proof-substance] PASS: no hypothesis-restatement patterns "
        f"found across {files_scanned} load-bearing proof files."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
