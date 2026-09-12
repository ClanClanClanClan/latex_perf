#!/usr/bin/env python3
"""Regex-vs-AST parity gate (Tier 2 Stage 2, V27_2 plan T2-Stage2).

Thin wrapper around the OCaml parity checker [latex-parse/src/test_ast_parity.ml],
which runs BOTH the deprecated regex label/ref/cite extractors
(Validators_common.extract_labels_with_prefix / extract_refs_with_prefix and the
REF-008 @entry regex) and the new comment/verbatim-aware
Ast_semantic_state.labels / refs / cites extractors over corpora/lint, and
asserts they agree except on the intended false-match corrections (a token inside
a comment / verbatim / \\verb / url span, which the AST correctly drops).

This is the persistent gate that lets the regex label/env extractor path be
retired safely. Wired into scripts/tools/pre_release_check.py. Exit non-zero on
any UNexpected divergence; prints the enumerated corrections otherwise.
"""
import os
import subprocess
import sys

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
EXE = os.path.join(REPO, "_build/default/latex-parse/src/test_ast_parity.exe")


def main() -> int:
    # Build the checker (idempotent; pre_release_check already runs `dune build`,
    # but keep this self-contained for standalone invocation).
    # `--root .` pins dune to this repo's workspace (matters when the checkout is
    # itself nested inside another dune workspace, e.g. a git worktree under
    # .claude/); harmless in the normal top-level checkout.
    # dune may live in a repo-LOCAL opam switch and not on the bare PATH (that
    # is how this gate failed the first time it was ever wired into CI). Try it
    # directly, then via `opam exec`, and say WHICH failed rather than dying on
    # a bare FileNotFoundError that reads like the gate itself is broken.
    cmd = ["dune", "build", "--root", ".", "latex-parse/src/test_ast_parity.exe"]
    try:
        build = subprocess.run(cmd, cwd=REPO, capture_output=True, text=True)
    except FileNotFoundError:
        try:
            build = subprocess.run(["opam", "exec", "--", *cmd], cwd=REPO,
                                   capture_output=True, text=True)
        except FileNotFoundError:
            sys.stderr.write("[check_ast_parity] FAIL: neither `dune` nor "
                             "`opam exec -- dune` is available; this gate needs "
                             "the OCaml toolchain (it belongs in a job that has "
                             "run setup-ocaml-env, not in a pure job)\n")
            return 1
    if build.returncode != 0:
        sys.stderr.write("[check_ast_parity] FAIL: could not build parity checker\n")
        sys.stderr.write(build.stderr)
        return 1
    if not os.path.exists(EXE):
        sys.stderr.write(f"[check_ast_parity] FAIL: {EXE} not found after build\n")
        return 1
    run = subprocess.run([EXE], cwd=REPO, capture_output=True, text=True)
    sys.stdout.write(run.stdout)
    sys.stderr.write(run.stderr)
    if run.returncode != 0:
        sys.stderr.write("[check_ast_parity] FAIL: regex vs AST diverged beyond "
                         "the intended protected-region corrections\n")
        return 1
    print("[check_ast_parity] PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
