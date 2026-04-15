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
