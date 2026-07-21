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
- **Decidable premise-bridge (v27.1.53):**
  `proofs/CompileGuaranteeBridge.v::project_wf_dec` + `project_wf_dec_sound`
  (Qed, 0 admits, Closed) make the capstone's premises a *computable* check,
  and `--compile-check`'s `MODEL-CONNECTED` line runs an OCaml mirror of it on
  the real document. See "Model-connected verdict" below for exactly what is
  proven vs tested vs unverified.

xelatex / lualatex remain hypothesis-parametric; concrete WS8-style
discharge for those engines is a future workstream.

---


## Differential validation against real pdflatex (measured, not asserted)

`scripts/tools/diff_compile_check.sh` runs `--compile-check` AND the real `pdflatex`
binary over a labeled corpus (`corpora/compile_check/`) and reports the confusion
matrix. This turns the readiness claim into a measured fact. Latest run:

| soundness direction | count | meaning |
|---|---|---|
| **FALSE-READY** (cc=READY, pdflatex FAILS) | **0** | the pre-check never falsely certifies a doc that fails — the direction that matters |
| false-not-ready (cc=NOT-READY, pdflatex COMPILES) | 1 | safe conservative over-rejection (a `\write18` doc pdflatex tolerates in restricted mode; shell-escape is genuinely LP-Foreign) |
| correct NOT-READY & FAILS | 4 | unclosed math / unclosed env / extra `}` / missing `\input` all caught |
| correct READY & COMPILES | 2 | clean docs |

The harness exits nonzero ONLY on a FALSE-READY (a dangerous regression), so it is a
usable local soundness guard (not a CI gate — CI has no TeX).

### Known limitations (measured, honestly out of scope)

- **Conservative over-rejection of auto-closeable groups.** An unclosed OPEN group
  (`{x\end{document}`) is reported NOT-READY, but pdflatex auto-closes it and compiles.
  This is a *safe* false-NOT-READY (the parser is stricter than the engine on sloppy
  groups — good for linting, conservative for compile-prediction). DELIM-001 is excluded
  from the T5 compile-blocking set; the residual over-rejection comes from the T0 parser
  itself flagging the unclosed group.
- **Undefined control sequences are NOT detected** (`\foobarbaz` → READY, but pdflatex
  FAILS). This is a genuine completeness limit: the pre-check does not model the full
  macro/package universe, so it cannot know a control sequence is undefined. This is a
  false-READY class, documented as out of scope — it is why READY is a *readiness
  pre-check*, not a total compile certificate.


## Model-connected verdict — the `MODEL-CONNECTED` line (v27.1.53)

`--compile-check` now emits an additional `MODEL-CONNECTED` line that
genuinely wires the runtime parse to the Coq capstone's *proven premise
logic*. It is built from three pieces:

1. **A DECIDABLE premise-checker + soundness lemma, in Coq**
   (`proofs/CompileGuaranteeBridge.v`). `project_wf_dec : pdflatex_project →
   pdflatex_profile → list node → bool` checks exactly the capstone's
   hypotheses — T2 (`project_closed`, via a witness topological order it
   certifies), T3 (`profile_admits` for the profile's declared features AND
   every feature the document body requires), and T4
   (`NoDup (body_label_defs)`). The lemma
   `project_wf_dec_sound : project_wf_dec p pf order = true → project_well_typed
   p ∧ profile_supported p pf ∧ pdflatex_T4_coherent p` is **Qed, zero
   admits/axioms**, and the corollary `project_wf_dec_compile_safe` discharges
   `pdflatex_compile_safe` from a `true` verdict. `Print Assumptions
   project_wf_dec_compile_safe` prints *Closed under the global context*.
   So a `true` from this checker **provably** implies the capstone's
   conclusion (compiles, ≤2-pass convergence, fatal-free, warns-iff-unresolved).

2. **An OCaml extractor** (`latex-parse/src/compile_evidence.ml`,
   `Compile_evidence`) that maps a real `.tex` to the abstract
   `pdflatex_project`/`pdflatex_profile` the checker consumes: it **reuses**
   `Ast_semantic_state.labels`/`refs` for `\label`→`BT_label_def`,
   `\ref`/`\eqref`→`BT_label_ref` (keys hashed to stable `nat` ids), detects
   T3-relevant features (`fontspec`→`Opentype_fonts`, `unicode-math`,
   `luacode`/`\directlua`→`Lua_scripting`, CJK, …)→`BT_needs_feature`, and
   builds the T2 graph + topological order from `Build_graph.of_project`.

3. **The wiring**: `--compile-check` runs the OCaml **mirror** of
   `project_wf_dec` on the extracted project and prints `MODEL-CONNECTED
   MODEL-READY` iff that mirror returns `true` (else `MODEL-NOT-READY` with the
   failing T2/T3/T4 obligation). Default (no-flag) output is byte-identical.

### What is PROVEN vs TESTED vs UNVERIFIED (be precise)

- **PROVEN (Coq, Qed, 0 admits, `Print Assumptions` Closed):** the
  premise-decision logic itself — that `project_wf_dec = true` is *sufficient*
  for `pdflatex_compile_safe`'s hypotheses and hence its full conclusion. This
  is the flagship connection: the READY decision now corresponds to a **proven**
  check of the theorem's premises, not an ad-hoc runtime heuristic.
- **TESTED (not proven), `test_compile_evidence.ml`:** (a) the OCaml extractor
  faithfully reflects the source — it flags a duplicate `\label` (T4) and a
  required-but-unsupported feature (T3) on real documents, accepts clean ones;
  (b) **mirror-equivalence** — the OCaml `project_wf_dec` returns the SAME
  boolean as the Coq `project_wf_dec` on the shared example projects (the Coq
  side proves those verdicts by `vm_compute` as `Example`s; we replay the same
  abstract projects in OCaml and assert agreement). The checker is
  re-implemented in OCaml, **not Coq-extracted**, so this equivalence is a test.
- **UNVERIFIED:** (i) `Parser_l2` byte→AST correctness — the extractor trusts
  the parser's structural read of your bytes; (ii) the OCaml mirror faithfully
  equalling the Coq `project_wf_dec` is TESTED, not machine-checked, because
  there is no Coq extraction of this module.

Net effect: the gap is **narrowed, not eliminated**. READY + `MODEL-READY`
means "for the abstract project we extracted from your source, a *proven*
checker certifies the capstone premises hold." It does **not** yet mean "your
exact bytes are certified to compile", because the extraction step (parser +
label/feature reading) is trusted/tested rather than verified end-to-end.

Treat `--compile-check` as a fast, honest fail-first gate: NOT-READY (or
`MODEL-NOT-READY`) reliably means "do not bother running latexmk yet"; READY +
`MODEL-READY` means "no runtime precondition we check is violated, and the
extracted project passes the proven premise-check" — then run your real build.

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
