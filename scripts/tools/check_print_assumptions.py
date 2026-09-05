#!/usr/bin/env python3
"""check_print_assumptions.py — assert that every capstone theorem is axiom-free.

WHY THIS EXISTS
---------------
The project's headline verification claim is that the capstones rest on nothing but
the global context — no axioms, no admits, no unproved `Variable`/`Hypothesis`
leaking in through a Section. `Print Assumptions` is the only thing in Coq that can
establish that: the `grep`-based zero-admit gate in proof.yml checks *syntax* in the
proof files, but it cannot see an axiom inherited transitively from a dependency, and
it cannot see a Section hypothesis that was never discharged.

Before this gate, `Print Assumptions` was effectively decorative:

  - Exactly ONE executed site existed, `proofs/BodyTokenFrontEnd.v:1544`. It is a
    *printing* vernacular — it cannot fail a build, so it stayed green no matter what
    it printed. Nothing in CI ever read its output. The file itself conceded the
    point: "checked manually on every release".
  - The other three capstones had NO executed `Print Assumptions` at all — the claims
    at `CompileGuaranteeBridge.v:31`, `CompileGuaranteeExtract.v:15` and
    `LanguageContractExtract.v:20` are comments.

Additionally, `dune build proofs` caches: on a cache hit it prints nothing, so even
grepping the build log would silently pass. This gate therefore invokes `coqc`
directly, once per capstone, against the built theory — so the output is always
produced and always inspected.

WHAT IT CHECKS
--------------
For each capstone, `Print Assumptions` must print exactly "Closed under the global
context". Anything else — an axiom list, a Section variable, a missing constant — is
a failure, and the offending assumptions are echoed so the break is actionable.

USAGE
    python3 scripts/tools/check_print_assumptions.py [--repo .] [--build]

`--build` runs `dune build proofs` first; omit it in CI where the proofs were just
built (avoids a redundant multi-minute rebuild and any dune lock contention).

Exit 0 if every capstone is closed; exit 1 otherwise.
"""

from __future__ import annotations

import argparse
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

CLOSED = "Closed under the global context"


def resolve_tool(name: str, repo: Path) -> str:
    """Absolute path to an opam-installed binary.

    Resolved ONCE, from the repo root, because `opam exec` infers the switch from
    the CURRENT DIRECTORY. CI uses a repo-local switch (`_opam/`), so invoking
    `opam exec -- coqc` from a temp working directory fails with "No switch is
    currently set". Resolving here and calling the binary directly makes the
    later invocations cwd-independent (and skips an opam round-trip each time)."""
    r = subprocess.run(
        ["opam", "exec", "--", "which", name],
        cwd=repo, capture_output=True, text=True,
    )
    path = (r.stdout or "").strip().splitlines()
    if r.returncode == 0 and path and Path(path[-1]).exists():
        return path[-1]
    fallback = shutil.which(name)
    if fallback:
        return fallback
    raise SystemExit(
        f"[print-assumptions] FATAL: cannot locate `{name}`. Tried `opam exec -- which "
        f"{name}` from {repo} and PATH."
    )

# (theorem, module to Require, why it matters)
CAPSTONES = [
    (
        "BodyTokenFrontEnd.compile_safe_of_source",
        "LaTeXPerfectionist.BodyTokenFrontEnd",
        "bytes -> verdict: connects a body built by the EXTRACTED front-end to "
        "pdflatex_compile_safe. This is the theorem about the code that actually runs.",
    ),
    (
        "CompileGuaranteeBridge.project_wf_dec_compile_safe",
        "LaTeXPerfectionist.CompileGuaranteeBridge",
        "the decidable checker (project_closed_b && features && nodup) implies the "
        "model-level compile-safety theorem.",
    ),
    (
        "CompileGuaranteeBridge.project_wf_dec_compile_safe_modulo_label_uniqueness",
        "LaTeXPerfectionist.CompileGuaranteeBridge",
        "C1: the checker WITHOUT the nodup conjunct still implies the full "
        "compile-safety conclusion. This is the theorem that licenses certifying "
        "a document carrying duplicate \\label keys, so it must stay axiom-free "
        "for the shipped verdict to mean anything.",
    ),
    (
        "PdflatexModel.pdflatex_compile_safe",
        "LaTeXPerfectionist.PdflatexModel",
        "the headline model theorem: well-typed project + supported profile => "
        "pdflatex succeeds.",
    ),
    (
        "LanguageContract.classify_lp_core_sound",
        "LaTeXPerfectionist.LanguageContract",
        "the LP-Core tier decision is sound (feature-list -> tier step).",
    ),
]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=".")
    ap.add_argument(
        "--build", action="store_true", help="run `dune build proofs` before checking"
    )
    args = ap.parse_args()
    repo = Path(args.repo).resolve()

    coqc = resolve_tool("coqc", repo)

    if args.build:
        print("[print-assumptions] building proofs ...")
        r = subprocess.run(
            ["opam", "exec", "--", "dune", "build", "proofs"], cwd=repo
        )
        if r.returncode != 0:
            print("[print-assumptions] FAIL: `dune build proofs` failed", file=sys.stderr)
            return 1

    vodir = repo / "_build" / "default" / "proofs"
    gendir = vodir / "generated"
    if not vodir.is_dir():
        print(
            f"[print-assumptions] FAIL: {vodir} not found — build the proofs first "
            f"(`dune build proofs`, or pass --build).",
            file=sys.stderr,
        )
        return 1

    failures: list[str] = []

    with tempfile.TemporaryDirectory(prefix="print-assumptions-") as work:
        workdir = Path(work)
        for idx, (thm, module, why) in enumerate(CAPSTONES):
            src = workdir / f"PA{idx}.v"
            src.write_text(
                f"Require Import {module}.\nPrint Assumptions {thm}.\n",
                encoding="utf-8",
            )
            proc = subprocess.run(
                [
                    coqc,
                    "-R", str(vodir), "LaTeXPerfectionist",
                    "-Q", str(gendir), "LaTeXPerfectionist.Generated",
                    src.name,
                ],
                cwd=workdir,
                capture_output=True,
                text=True,
            )
            out = (proc.stdout or "") + (proc.stderr or "")

            if proc.returncode != 0:
                tail = "\n      ".join(out.strip().splitlines()[-12:])
                failures.append(
                    f"{thm}: coqc failed (exit {proc.returncode})\n      {tail}"
                )
                continue

            if CLOSED in out:
                print(f"[print-assumptions] OK   {thm}: {CLOSED}")
            else:
                # Echo whatever Coq reported instead — that IS the finding.
                reported = "\n      ".join(
                    ln for ln in out.strip().splitlines()
                    if ln.strip() and not ln.startswith("Warning")
                ) or "(no output)"
                failures.append(
                    f"{thm}: NOT closed under the global context.\n"
                    f"      why this theorem matters: {why}\n"
                    f"      Coq reported:\n      {reported}"
                )

    if failures:
        print("\n[print-assumptions] FAIL — capstone(s) depend on unproved assumptions:\n")
        for f in failures:
            print(f"  - {f}\n")
        return 1

    print(
        f"[print-assumptions] PASS — all {len(CAPSTONES)} capstones are closed under "
        f"the global context."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
