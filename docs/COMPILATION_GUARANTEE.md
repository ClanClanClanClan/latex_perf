# Compilation guarantee — user-facing summary

**For LaTeX Perfectionist v26.2+.**

This doc summarises what claims v26.2 makes about your project's
compilability, and what claims it explicitly does not make. Formal
details live in [specs/v26/compilation_guarantee_stack.md](../specs/v26/compilation_guarantee_stack.md)
and [specs/v26/compilation_profiles.yaml](../specs/v26/compilation_profiles.yaml).

---

## TL;DR

Run `latex_parse_cli --compile-check path/to/main.tex` before running
latexmk. If it says **READY**, these runtime preconditions genuinely
held (within the declared profile):

- Your source **parsed** with the real L2 parser (no unclosed
  math/environment/`\verb`) and is **not** in the LP-Foreign tier
  (no `\write18`, etc.).
- Your multi-file project is closed (no missing `\input`, no cycles).
- Your selected engine supports every **declared** feature.
- No **compile-blocking** lint rule fired (`DELIM-`/`ENC-`/`PRT-`) —
  including the `DELIM-001` unbalanced-brace check the parser itself
  does not catch.
- If a sibling `.aux` was present, its labels are unique.

**READY is a sound readiness PRE-CHECK, not a total "it will compile"
certificate.** It means every runtime precondition we check held; it does
**not** prove the document compiles. What is NOT verified at runtime: T1
macro-expansion (skipped), T4 without an `.aux` (skipped), and the
byte-for-byte connection from your source to the abstract model the T6/T7
compile-safety capstone is proved over (see the residual-gap note below).
Everything else about compile success falls back on the toolchain itself.

---

## What `--compile-check` runs (v27.1.52)

The CLI's `--compile-check <file.tex>` flag invokes
`Compile_contract.check_ready_to_compile` in
`latex-parse/src/compile_contract.ml`, with the same per-file context the
lint path sets up (file context, command spans, build profile, user
macros, language profile). It checks the T0–T5 conditions and prints
`READY` (exit 0) or `NOT-READY` + the failing reasons (exit 1). Here is
**exactly** what each check does at runtime today — no more, no less:

| Check | What it ACTUALLY runs now | Real / conservative |
|---|---|---|
| T0 Parse + profile | `Language_profile.classify_source` → NOT-READY on **LP-Foreign**; then `Parser_l2.parse_located` → NOT-READY with the first structural parse error (unclosed math/env/`\verb`, `\end` without `\begin`, nesting blow-up) + line/offset | **REAL** |
| T1 Expansion | *no-op* — not runtime-checked at this layer | conservatively skipped (never claims a T1 property) |
| T2 Project closed | `Build_graph` — every `\input`/`\include` resolves, no include cycle | **REAL** |
| T3 Profile compat | declared-feature × engine compatibility table | **REAL** (from *declared* features; v26.2 does not auto-detect) |
| T4 Semantic coherence | if a sibling `.aux` exists: duplicate-label detection | **REAL when `.aux` present**, else skipped |
| T5 Rule safety | `Validators.run_all`, then flags **compile-blocking** `Error` results only — rule families `DELIM-*`, `ENC-*`, `PRT-*` | **REAL** (narrowed on purpose; see below) |

If every check passes, `check_ready_to_compile` returns `Ready`; otherwise
a list of structured reasons is returned and printed one per line.

**Why T5 is narrower than "no Error rule fires".** Many `Error`-severity
rules are completeness/style faults that pdflatex compiles through anyway
(e.g. `DOC-001` "missing `\maketitle`"). Flagging every Error would make a
perfectly clean article NOT-READY. `--compile-check` therefore flags only
the `DELIM-`/`ENC-`/`PRT-` families — mismatched delimiters, byte/encoding
faults, and parse-reliability rules — which correspond to structural faults
the engine cannot recover from. This is intentionally conservative: a
false NOT-READY is safe; a false READY on a broken document is not.

**T0 and T5 are complementary.** The L2 parser is error-*recovering*, so
some structural faults it does not itself flag — most notably an unbalanced
brace group, which it silently closes at EOF — are caught by **T5's
`DELIM-001`**, not by T0. Neither check alone is a proof of well-formedness.

---

## Theorems that are NOT runtime checks

- **T6 (compilation progress):** if T0–T5 hold AND the toolchain
  converges in bounded passes, compilation succeeds. v26.2 shipped
  this hypothesis-parametric; **v27 WS8 discharges it concretely
  for pdflatex** in `proofs/PdflatexModel.v::pdflatex_T6_discharged`.
- **T7 (output well-formedness):** if T6 holds AND the toolchain
  produces a well-formed artefact, the output satisfies the subset's
  output contract (valid PDF graph, fatal-free log). v27 WS8
  discharges it concretely for pdflatex in
  `proofs/PdflatexModel.v::pdflatex_T7_discharged`.
- **Headline (v27 WS8 capstone):** `pdflatex_compile_safe` (Qed,
  Closed under the global context) — for any project_well_typed
  project and profile_supported profile, there exists an artefact
  such that pdflatex produces it, compilation succeeds, and the
  output is well-formed. Zero axioms, zero admits. As of v27.1.29–v27.1.39
  the capstone is proved against a **faithful operational pdflatex
  semantics** (token/aux/log/pass model, tight ≤2-pass convergence,
  warnings-iff-unresolved, PDF-artefact model) rather than the earlier
  abstract pass-iteration model; see
  [`specs/v27/V27_FAITHFUL_SEMANTICS_PLAN.md`](../specs/v27/V27_FAITHFUL_SEMANTICS_PLAN.md).
  Honest residuals: the T0/T1/T5 universal obligations and byte-exact PDF
  *structural* semantics stay conservative/deferred.

xelatex / lualatex remain hypothesis-parametric; concrete WS8-style
discharge for those engines is a future workstream.

---

## Residual gap — READY is not yet a total certificate

Be precise about what the capstone does and does not buy you:

- **`pdflatex_compile_safe` is proved over an ABSTRACT operational
  model.** The Coq capstone (`proofs/PdflatexModel.v`) reasons about a
  `body_token` document model and an operational pdflatex semantics. It is
  Qed with zero axioms/admits **within that model**.
- **The model is NOT yet connected byte-for-byte to the runtime parser.**
  There is no verified `bytes → body_token` extraction linking the real
  `Parser_l2` output (what `--compile-check`'s T0 runs) to the `body_token`
  the capstone quantifies over. So the theorem's `project_well_typed`
  hypothesis is not discharged from your actual source bytes at runtime.
- **Consequently `--compile-check` READY is a sound *readiness* result,
  not the capstone's conclusion.** It certifies that the T0–T5 runtime
  preconditions we check held; it does not mechanically instantiate the
  compile-safety theorem for your specific input. Closing the
  `bytes → body_token` gap (a verified extraction/refinement) is the
  remaining work that would upgrade READY toward a total "it will compile"
  certificate for arbitrary input.

Until that gap is closed, treat `--compile-check` as a fast, honest
fail-first gate: NOT-READY reliably means "do not bother running latexmk
yet"; READY means "no runtime precondition we check is violated" — then run
your real build.

---

## Per-profile coverage

| Profile | Status | T6/T7 discharge |
|---|---|---|
| pdflatex | GA | v27 WS8 concrete (`PdflatexModel.pdflatex_compile_safe`) |
| xelatex | beta | hypothesis-parametric; v26.3 adds xelatex aux-parser |
| lualatex | beta | hypothesis-parametric; `\directlua` side effects out of scope |
| pTeX/upTeX | experimental | no T6/T7 claim |

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
  match Project_model.of_root "main.tex" with
  | Error _ -> prerr_endline "could not load project"
  | Ok project ->
      let profile =
        Build_profile.create ~tex_path:"main.tex" ~base_dir:"."
      in
      (* [~source] lets T0/T5 run on the exact bytes you already hold;
         omit it and the root .tex is read from disk. *)
      match Compile_contract.check_ready_to_compile project profile with
      | Ready -> print_endline "OK to compile"
      | NotReady reasons ->
          List.iter
            (fun r -> print_endline (Compile_contract.reason_to_string r))
            reasons
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
