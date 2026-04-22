# Compilation guarantee — user-facing summary

**For LaTeX Perfectionist v26.2+.**

This doc summarises what claims v26.2 makes about your project's
compilability, and what claims it explicitly does not make. Formal
details live in [specs/v26/compilation_guarantee_stack.md](../specs/v26/compilation_guarantee_stack.md)
and [specs/v26/compilation_profiles.yaml](../specs/v26/compilation_profiles.yaml).

---

## TL;DR

Run `latex_parse_cli --compile-check path/to/main.tex` before running
latexmk. If it says **Ready**, you can trust these properties (within
the declared profile):

- Your source parses cleanly.
- Your user-defined macros are in the bounded subset and don't cycle.
- Your multi-file project is closed (no missing `\input`, no cycles).
- Your selected engine supports every declared feature.
- No Error-level style rule still fires.

Everything else about compile success falls back on the toolchain
itself — v26.2 ships theorems **parametric on toolchain convergence**;
if pdflatex, xelatex, or lualatex does its job, you're good.

---

## What `--compile-check` runs

The CLI's `--compile-check` flag invokes `Compile_contract.check_ready_to_compile`
in `latex-parse/src/compile_contract.ml`. This checks five conditions
(T0 through T5 in the [theorem stack](../specs/v26/compilation_guarantee_stack.md)):

| Check | What it verifies | Failure reason kind |
|---|---|---|
| T0 Parse | `Parser_l2.parse` accepts the source | `T0_parse_fails` |
| T1 Expansion | User macros are in-subset + acyclic | `T1_expansion_fails` |
| T2 Project closed | All `\input`s resolve; no include-cycles | `T2_project_not_closed` |
| T3 Profile compat | Engine supports all declared features | `T3_profile_incompatible` |
| T4 Semantic coherence | Labels unique across files; refs resolve; counters/bib consistent | `T4_semantic_incoherent` |
| T5 Rule safety | No Error-level lint rule fires | `T5_rule_violations` |

If all five pass, `check_ready_to_compile` returns `Ready`. Otherwise a
list of structured reasons is returned.

---

## Theorems that are NOT runtime checks

- **T6 (compilation progress):** if T0–T5 hold AND the toolchain
  converges in bounded passes, compilation succeeds. v26.2 ships this
  as a **conditional** theorem (hypothesis-parametric). The toolchain
  itself is the "prover" at runtime — we trust pdflatex / xelatex /
  lualatex to converge.
- **T7 (output well-formedness):** if T6 holds AND the toolchain
  produces a well-formed artefact, the output satisfies the subset's
  output contract (valid PDF graph, refs resolved). Same parametric
  pattern.

Full discharge of T6/T7 (instantiating the toolchain model in Coq)
is [v27 WS8](../specs/v27/V27_REPO_EXACT_MASTER_SPEC.md) work.

---

## Per-profile coverage

| Profile | Status | T6/T7 discharge |
|---|---|---|
| pdflatex | GA | v26.2 hypothesis-parametric; v27 WS8 concrete |
| xelatex | beta | same; v26.3 adds xelatex aux-parser |
| lualatex | beta | same; \\directlua side effects out of scope |
| pTeX/upTeX | experimental | no T6/T7 claim in v26.2 |

Full profile metadata: [compilation_profiles.yaml](../specs/v26/compilation_profiles.yaml).

---

## What this is NOT

- **A replacement for latexmk.** Run `--compile-check` first for
  fast-fail; then run your real build. They're complementary.
- **A style checker.** The existing validators cover that.
  `--compile-check` only verifies compile-readiness, not style.
- **A guarantee against LaTeX bugs.** If pdflatex itself has a bug on
  your document, v26.2 can't catch it — T6 is parametric on toolchain
  correctness.
- **A Coq-extracted runtime.** v26.2's Coq theorems verify the
  abstract pipeline; the runtime OCaml is hand-written and tested,
  not mechanically extracted. v27 may ship an extracted variant.

---

## Example: CI usage

```yaml
# .github/workflows/my-paper.yml
- name: Check compile readiness
  run: latex_parse_cli --compile-check main.tex
- name: Build with latexmk
  if: success()
  run: latexmk -pdf main.tex
```

`--compile-check` exits 0 on Ready, non-zero on any failure reason.
Exit codes + structured stderr let CI fail fast before latexmk bills
you for compute on a document that can't possibly compile cleanly.

---

## Example: library usage

```ocaml
open Latex_parse_lib

let () =
  let project = Project_model.of_root "main.tex" in
  let profile = Build_profile.detect () in
  match Compile_contract.check_ready_to_compile project profile with
  | Ready -> print_endline "OK to compile"
  | NotReady reasons ->
      List.iter (fun r -> print_endline (reason_to_string r)) reasons
```

For formal reasoning, instantiate the Section-quantified theorems in
`proofs/CompileProgress.v` with your own toolchain model and discharge
the `compile_progress_rule` hypothesis.

---

## References

- [specs/v26/compilation_guarantee_stack.md](../specs/v26/compilation_guarantee_stack.md)  — T0–T7 formal detail
- [specs/v26/compilation_profiles.yaml](../specs/v26/compilation_profiles.yaml) — profile metadata
- [docs/v26_2/adr/ADR-007](v26_2/adr/ADR-007-compile-stack-ships-in-v26-2.md) — why this ships in v26.2
- [docs/SUPPORT_MATRIX.md](SUPPORT_MATRIX.md) — broader support matrix
