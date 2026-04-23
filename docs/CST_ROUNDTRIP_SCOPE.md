# CST round-trip scope (v26.2 PR B2)

**Companion to** `latex-parse/src/cst.ml` (PR B1), `proofs/CSTRoundTrip.v`
(PR B2), and `latex-parse/src/test_cst_roundtrip.ml`.

v26.2 ships **two** round-trip guarantees at different strengths. This
document is the authoritative scope definition for each.

---

## 1. Byte-lossless (full scope, v26.2 GA)

**Claim.** For every source string `src` — valid LaTeX or not —

```
Cst.serialize (Cst_of_ast.of_source src) = src
```

**Enforcement.**
- Runtime: `latex-parse/src/test_cst_roundtrip.ml` sweeps the entire
  `corpora/` tree (currently 345 files) and asserts byte-equality on
  every file.
- Coq: `proofs/CSTRoundTrip.v` mechanises the abstract shape of the
  serializer (concatenation of span-slice strings) and proves that
  concatenating the slices covering `[0, n)` of any string `src`
  returns exactly `src`.

**Mechanism.** `Cst_of_ast.of_source` fills every byte of `src` with
either (a) a structural CST variant (`CToken`, `CTrivia`,
`CMathInline`, `CMathDisplay`, `CVerbatim`, `CEnvironment`), or
(b) the fallback `CUnparsed` variant. Adjacent nodes are joined at
byte boundaries — no gaps, no overlaps. `serialize` just concatenates
the raw bytes.

**Implication.** Users can convert LaTeX source to CST and back and
guarantee no edits are injected by the CST pipeline itself. This is
the foundation the rewrite engine (PR B3) builds on.

---

## 2. Structure-lossless (narrow scope, v26.2 alpha)

**Claim.** For every source `src` in the **declared subset** below,

```
Parser_l2.parse (Cst.serialize (Cst_of_ast.of_source src))
= Parser_l2.parse src
```

i.e., re-parsing the serialized CST produces the identical AST.

### 2.1 Declared subset

A source is in the structure-lossless subset if ALL of the following
hold:

1. **No unclosed constructs** — every `$`, `\(`, `\[`, `{`, and
   `\begin{…}` has a matching closer. Unclosed constructs serialize
   byte-losslessly via the `CUnparsed` fallback, so the AST equality
   may drift at the error site.
2. **No verbatim content that would be re-interpreted** — specifically,
   `\verb|…|` with `|` chosen such that re-parsing picks a different
   token boundary. Standard verbatim environments are in scope.
3. **ASCII command names** — custom commands use only `[A-Za-z*]` in
   their names. Commands with Unicode names or UTF-8 bytes in the
   identifier are out of scope for v26.2.
4. **Document size < 1 MB** — large documents are byte-lossless (via
   scope 1) but not exercised by the corpus-tested structure claim.
5. **No shell-escape / `\write18`** — these are out of LP-Core and
   therefore out of this claim.

### 2.2 Enforcement

- Runtime: a future `test_cst_structure.ml` (v26.3 deliverable) will
  load files matching the subset and assert AST equality. For v26.2,
  we corpus-test the byte-lossless invariant and rely on manual
  inspection that the curated subset files round-trip structurally.
- Coq: `proofs/CSTRoundTrip.v` scopes the structure-lossless theorem
  to a declared-subset predicate; discharging the predicate for real
  sources is v26.3 work.

### 2.3 Non-goals

- Round-tripping through multiple edits — that's PR B3 rewrite-engine
  scope. The structure-lossless claim here is a point-in-time claim
  on the initial parse ↔ CST roundtrip.
- Exact whitespace preservation inside command arguments: v26.2 keeps
  commands as `CUnparsed` so whitespace within `\cmd{  foo  bar  }` is
  preserved byte-wise. v26.3+ may structure arg bodies and at that
  point will need an extra whitespace-preservation clause.

---

## 3. What the corpus proves

The `corpora/` sweep currently covers ~330 lint fixtures
(from `corpora/lint/`) plus ~15 synthetic edge cases in
`corpora/roundtrip/`. The synthetic edge cases exercise:

- Empty / whitespace-only / single-character input
- Deeply nested groups (20 levels)
- Unclosed math, unclosed group, unclosed environment
- Verbatim with all special characters
- Unicode (composed/decomposed, emoji, CJK, RTL)
- Commands with many optional + mandatory args
- Trailing whitespace, mixed line endings
- Pure-comment files

All 345 files currently PASS byte-lossless. We treat any new corpus
failure as a regression gate.

---

## 4. Fallback posture (if CSTRoundTrip.v stalls)

Per plan §3.2 preregistered fallback:

- **B2a (shipped in v26.2):** runtime `test_cst_roundtrip.ml` proving
  byte-losslessness on the corpus.
- **B2b (shippable in v26.3 if the Coq proof is incomplete):** the
  Coq-level theorem `proofs/CSTRoundTrip.v`. The v26.2 `.v` file is
  the scaffold + the mechanised byte-lossless theorem at the
  abstract-serializer level; if the structure-lossless theorem needs
  more machinery than fits in PR B2, we document the gap here and
  cover it in v26.3.

---

## 5. References

- Memo `specs/REPO_EXACT_MISSING_ARCHITECTURE_MEMO_V26_V27.md` §16.3 —
  lossless CST foundation.
- ADR-005 (`docs/v26_2/adr/ADR-005-cst-round-trip-two-level.md`) —
  why two levels, not one.
- ADR-006 (`docs/v26_2/adr/ADR-006-cst-subset.md`) — structural
  subset scoping.
- `specs/v26/V26_2_PLAN.md` §3.2 — PR B2 scope and fallback.
