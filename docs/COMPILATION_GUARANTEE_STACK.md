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

**The residual gap — CLOSED in v27.1.58 (modulo a small trusted base).** There is
now a **verified `bytes → body_token` front-end** connecting artefact (1) to
artefact (2): `proofs/BodyTokenFrontEnd.v` proves `compile_safe_of_source` (Qed, 0
admits, `Print Assumptions` Closed), which builds the `body_token` list from the
source bytes — token/key scanning, FNV-1a hashing of label keys, feature
detection, body assembly — and connects it to
`PdflatexModel.pdflatex_compile_safe`. It is Coq-extracted to
`latex-parse/src/body_token_frontend_extracted.ml` (byte-identical regen via
`scripts/tools/regen_body_token_frontend_extract.sh`) and **executed** by
`--compile-check` (`Compile_evidence.extract_body_verified`); a differential parity
gate (`test_body_token_frontend.ml`) proves it byte-identical to the retained hand
OCaml over 393 corpus files + 422 fixtures.

What remains **trusted** (a much smaller base than the whole extraction): the
protected-range oracle `Validators_common.find_verbatim_comment_url_ranges` (the
front-end is proven *relative to* that range set), the string→byte-list
conversion, build-graph construction, the 1:1 runtime→extracted-type conversion,
file I/O, and the OCaml compiler + Coq extraction toolchain. Two honest caveats on
the proof: (a) the `fnv_mul_bound (< 2^55)` lemma is asserted informally (a
Peano-`nat` kernel pathology), validated by the parity test rather than proved
in-kernel; (b) the extraction realizes `two30`/`fnv_basis`/`fnv_prime` as native
`int` literals, each provably equal to its Coq definition. So a READY +
`MODEL-READY` result now discharges the capstone's premises for the *extracted*
project via proven-and-executed code at both ends (front-end + premise-checker),
short of certifying the raw bytes against the trusted base above.
