# Compilation guarantee stack

This document defines the theorem stack required to move from
"verified analysis engine" to "compilation guarantees".

## Goal theorem family

The final target is not merely parser soundness. It is a family of theorems of the form:

> If project `P` belongs to `LP-Core(profile, engine)`, all mandatory assets resolve,
> all Error-level rules pass, and all build-coupled checks succeed, then the selected
> engine/toolchain compiles `P` to a well-formed target artefact.

This stack decomposes into the following theorem groups.

## T0. Language contract theorems

- Membership decision for LP-Core.
- Membership decision for LP-Extended.
- Rejection surface for LP-Foreign.
- Subset monotonicity (`LP-Core ⊆ LP-Extended`).
- Unsupported-feature detection soundness.

## T1. Parsing and syntax theorems

- Lexer determinism.
- Lexer totality.
- Parser soundness.
- Parser completeness for LP-Core.
- Parser unambiguity for LP-Core grammar.
- Concrete-syntax round-trip preservation (once CST exists).

## T2. Editing and partial-document theorems

- Well-formed partial state type.
- Local damage bound after edit.
- Stable unaffected-region semantics.
- Recovery monotonicity after repair.
- Incremental recomputation equivalence outside dirty boundary.

## T3. Macro semantics theorems

- Bounded user macro registry determinism.
- Termination / fuel monotonicity.
- Cycle detection correctness.
- Safe argument substitution.
- Supported-subset rejection correctness for unsupported macro constructs.

## T4. Project graph theorems

- Include graph acyclicity or explicit cycle diagnostics.
- File-resolution determinism.
- Global semantic projection correctness.
- Cross-file label/reference uniqueness and resolution.
- Build artefact dependency soundness.

## T5. Build profile / compile theorems

- Engine profile determinism (pdfLaTeX / XeLaTeX / LuaLaTeX subset).
- Toolchain profile closure (bibtex/biber/makeindex/etc. where supported).
- Build-pass convergence theorem or bounded-pass contract.
- Compile-log evidence soundness for build-coupled rules.

## T6. Validator theorems

- Rule-family soundness.
- Faithful vs conservative classification correctness.
- Statistical-threshold theorem family for ML-backed ambiguity rules.
- Fix preservation theorems for any auto-fix admitted into guaranteed mode.

## T7. Platform theorems (later)

- Tracked-change merge preservation for LP-Core.
- Comment anchoring stability under local edits.
- Waiver scoping correctness.
- Deterministic collaborative projection over accepted document state.

## Practical v26 theorem target

v26 should aim to complete:
- T0
- T2
- T3 (bounded subset)
- T4 (foundation)
- T5 partially (compile-log and profile contract)
while preserving all existing T1/T6 results.

v27 can then extend into platform-layer theorems and stronger build guarantees.

## Runtime readiness vs. proved capstone (honest status, v27.1.52)

Two distinct artefacts share the "T0–T5" naming and must not be conflated:

1. **The runtime readiness contract** (`Compile_contract.check_ready_to_compile`,
   surfaced as `latex_parse_cli --compile-check`). This runs T0–T5 *checks* on a
   real document at analysis time. As of v27.1.52:
   - **T0** genuinely runs `Language_profile.classify_source` (rejects
     LP-Foreign) and `Parser_l2.parse_located` (rejects hard parse errors).
   - **T5** genuinely runs `Validators.run_all` and flags **compile-blocking**
     `Error` diagnostics only — the `DELIM-`/`ENC-`/`PRT-` families — not every
     Error-severity style rule.
   - **T2/T3** are real (include-graph closure; declared-feature × engine).
   - **T4** is real when a sibling `.aux` is present (duplicate labels), else
     skipped. **T1** is a no-op at this layer (never claims a T1 property).
   See [../docs/COMPILATION_GUARANTEE.md](../docs/COMPILATION_GUARANTEE.md).

2. **The proved compile-safety capstone** (`proofs/PdflatexModel.v`,
   `pdflatex_compile_safe`, Qed). This is a theorem over an **abstract
   `body_token` operational model** of pdflatex, not over the runtime parser's
   bytes.

**The residual gap:** there is no verified `bytes → body_token` extraction
connecting artefact (1) to artefact (2). The runtime readiness pre-check is
therefore *sound* (a genuinely broken or LP-Foreign document returns NOT-READY)
but a READY result does **not** mechanically discharge the capstone's
`project_well_typed` hypothesis for the input bytes. Closing that extraction gap
is the outstanding work that would turn the readiness pre-check into a total
"it will compile" certificate.
