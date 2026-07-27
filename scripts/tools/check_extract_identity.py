#!/usr/bin/env python3
"""check_extract_identity.py — fail if a committed Coq→OCaml extract has drifted
from the proofs it claims to be extracted from.

WHY THIS EXISTS
---------------
Three generated files are compiled into the shipped binary:

    latex-parse/src/body_token_frontend_extracted.ml   (BodyTokenFrontEndExtract.v)
    latex-parse/src/compile_guarantee_extracted.ml     (CompileGuaranteeExtract.v)
    latex-parse/src/language_contract_extracted.ml     (LanguageContractExtract.v)

They are the ONLY link between the Coq proofs and the running code: the capstone
`compile_safe_of_source` is about `body_of_source`, and the thing that actually
runs is `Body_token_frontend_extracted.body_of_source`. If the committed .ml
stops corresponding to the .v, the proof still says Qed, CI still passes, and the
binary silently ships unverified behaviour.

Until this gate, NOTHING checked that correspondence. Building `…Extract.v`
re-runs extraction into `_build`, which dune's `coq.theory` stanza discards, so
CI only ever proved that extraction still *succeeds*. The three regen scripts'
headers each claimed "drift is caught by CI"; that claim was false, and this gate
is what makes it true. (Historical evidence that the risk is real, not theoretical:
`git log --numstat` on the front-end extract shows a −29,998-line swing in #501 and
a +27,591/−5,513 swing in #511, on changes that touched a handful of Coq lines.)

WHAT IT CHECKS
--------------
For each extract: re-run the project's own regen script (so the gate exercises the
real regeneration path, not a reimplementation of it), then compare the freshly
generated file against the committed one.

The comparison is on the PARSED AST, not raw bytes. Both sides are run through

    ocamlc -stop-after parsing -dsource

which is the OCaml compiler's own parser and pretty-printer. It discards the input's
formatting entirely and re-renders from the syntax tree, so two files that mean the
same thing produce identical output. That is what makes the gate immune to
ocamlformat: `.ocamlformat` pins no version, so a byte-compare would turn every
formatter upgrade into a spurious red build, and a gate that cries wolf gets turned
off. It also correctly collapses ocamlformat's syntactic normalisations, which a
whitespace-based comparison does NOT — e.g. `function true ->` vs `function | true ->`,
`function x, _ ->` vs `function (x, _) ->`, and `(||) a b` vs `a || b`. All three
appear in these files, and all three are the same AST.

The check remains exactly as strict as byte-identity with respect to *meaning*: any
added, removed, renamed or altered definition, and any changed numeric constant,
changes the AST and fails the gate.

Because the gate skips the regen scripts' formatting step (EXTRACT_SKIP_FMT=1 —
ocamlformat needs over an hour on the 90k-line front-end extract, where the AST
canonicalisation needs 0.3 s), the freshly generated side is unformatted and the
committed side is formatted. That difference is invisible to an AST comparison,
which is the whole point.

USAGE
    python3 scripts/tools/check_extract_identity.py [--repo .] [--only NAME]

Exit 0 if every committed extract matches its proofs; exit 1 otherwise.
Requires the Coq toolchain (this runs coqc via the regen scripts).
The working tree is restored on exit, including on failure.
"""

from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

EXTRACTS = [
    (
        "body_token_frontend",
        "scripts/tools/regen_body_token_frontend_extract.sh",
        "latex-parse/src/body_token_frontend_extracted.ml",
        "proofs/BodyTokenFrontEndExtract.v",
    ),
    (
        "compile_guarantee",
        "scripts/tools/regen_compile_guarantee_extract.sh",
        "latex-parse/src/compile_guarantee_extracted.ml",
        "proofs/CompileGuaranteeExtract.v",
    ),
    (
        "language_contract",
        "scripts/tools/regen_language_contract_extract.sh",
        "latex-parse/src/language_contract_extracted.ml",
        "proofs/LanguageContractExtract.v",
    ),
]

def resolve_tool(name: str, repo: Path) -> str:
    """Absolute path to an opam-installed binary, resolved ONCE from the repo root.

    `opam exec` infers the switch from the CURRENT DIRECTORY. CI uses a repo-local
    switch (`_opam/`), so `opam exec -- ocamlc` from a temp directory fails with
    "No switch is currently set"."""
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
        f"[extract-identity] FATAL: cannot locate `{name}`. Tried `opam exec -- which "
        f"{name}` from {repo} and PATH."
    )


def canonicalise(path: Path, label: str, ocamlc: str) -> str:
    """Re-render `path` from its parsed AST, discarding all formatting.

    `-dsource` writes to stderr, and `-stop-after parsing` means no typing, no
    dependencies and no output artefacts — just parse and print. Warnings are
    disabled because they share stderr with `-dsource` and quote the file path."""
    proc = subprocess.run(
        # -w -a: suppress warnings. `-dsource` shares stderr with the warning
        # stream, and warning text embeds the FILE PATH — which differs between
        # the committed copy and the regenerated one, so an unsuppressed warning
        # would make two identical ASTs compare unequal.
        [ocamlc, "-w", "-a", "-stop-after", "parsing", "-dsource", str(path)],
        capture_output=True,
        text=True,
        cwd=path.parent,
    )
    rendered = proc.stderr
    if proc.returncode != 0 or not rendered.strip():
        raise SystemExit(
            f"[extract-identity] FATAL: could not parse {label} ({path}).\n"
            f"  exit={proc.returncode}\n  {(proc.stdout or rendered).strip()[:600]}"
        )
    return rendered


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=".")
    ap.add_argument("--only", help="check a single extract by name")
    args = ap.parse_args()
    repo = Path(args.repo).resolve()

    targets = [e for e in EXTRACTS if not args.only or e[0] == args.only]
    if not targets:
        print(f"[extract-identity] no extract named {args.only!r}", file=sys.stderr)
        return 1

    ocamlc = resolve_tool("ocamlc", repo)
    failures: list[str] = []
    backups: dict[Path, Path] = {}
    tmp = Path(tempfile.mkdtemp(prefix="extract-identity-"))

    try:
        for name, script, dest_rel, source_rel in targets:
            dest = repo / dest_rel
            source = repo / source_rel
            if not dest.exists():
                failures.append(f"{name}: committed extract missing at {dest_rel}")
                continue
            if not source.exists():
                failures.append(f"{name}: extraction driver missing at {source_rel}")
                continue

            committed_text = dest.read_text(encoding="utf-8")
            backup = tmp / f"{name}.committed.ml"
            backup.write_text(committed_text, encoding="utf-8")
            backups[dest] = backup
            canon_committed = canonicalise(backup, f"{dest_rel} (committed)", ocamlc)

            print(f"[extract-identity] regenerating {name} from {source_rel} ...")
            # EXTRACT_SKIP_FMT=1: run the real extraction, skip only the
            # ocamlformat canonicalisation. Formatting cannot affect a canonical
            # comparison, and on the 90k-line front-end extract ocamlformat runs
            # for over an hour (superlinear on Coq's nested unary Peano numerals)
            # — with it, this gate could never fit in a CI timeout.
            env = dict(os.environ, EXTRACT_SKIP_FMT="1")
            proc = subprocess.run(
                ["bash", script],
                cwd=repo,
                capture_output=True,
                text=True,
                env=env,
            )
            if proc.returncode != 0:
                tail = (proc.stderr or proc.stdout or "").strip().splitlines()[-15:]
                failures.append(
                    f"{name}: regen script failed (exit {proc.returncode}):\n    "
                    + "\n    ".join(tail)
                )
                continue

            fresh_text = dest.read_text(encoding="utf-8")
            byte_identical = fresh_text == committed_text
            fresh_copy = tmp / f"{name}.regenerated.ml"
            fresh_copy.write_text(fresh_text, encoding="utf-8")
            canon_fresh = canonicalise(fresh_copy, f"{dest_rel} (regenerated)", ocamlc)

            if canon_committed == canon_fresh:
                note = "byte-identical" if byte_identical else (
                    "AST-identical; formatting differs (expected — the gate skips "
                    "the regen formatting step)"
                )
                print(f"[extract-identity] OK   {name}: {note}")
            else:
                # Locate the first divergence to make the failure actionable.
                a, b = canon_committed, canon_fresh
                lim = min(len(a), len(b))
                pos = next((k for k in range(lim) if a[k] != b[k]), lim)
                lo = max(0, pos - 120)
                failures.append(
                    f"{name}: committed extract DOES NOT match {source_rel}\n"
                    f"    committed len={len(a)}  regenerated len={len(b)}  "
                    f"first divergence at char {pos}\n"
                    f"    committed  ...{a[lo:pos + 120]!r}\n"
                    f"    regenerated ...{b[lo:pos + 120]!r}\n"
                    f"    Fix: run {script} and commit the result."
                )
    finally:
        # Always restore the working tree — this gate must have no side effects.
        for dest, backup in backups.items():
            shutil.copyfile(backup, dest)
        shutil.rmtree(tmp, ignore_errors=True)

    if failures:
        print("\n[extract-identity] FAIL — committed extract(s) drifted from the proofs:\n")
        for f in failures:
            print(f"  - {f}\n")
        print(
            "  These files are the only link between the Coq proofs and the shipped\n"
            "  binary. A mismatch means the proof does not describe the running code."
        )
        return 1

    print(
        f"[extract-identity] PASS — {len(targets)} committed extract(s) reproduce "
        f"exactly from their proofs."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
