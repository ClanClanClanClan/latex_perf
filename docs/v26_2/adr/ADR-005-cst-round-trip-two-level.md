# ADR-005: CST round-trip is byte-lossless universally + structure-lossless on subset

- **Status:** Accepted (2026-04-22)
- **Context owner:** v26.2 architectural decisions (plan §2.5)

## Context

"Lossless CST" is one of memo §16.3's v26.2 deliverables. Many prior
projects promise "lossless" and ship with undocumented limitations
(verbatim blocks, catcode mutations, etc. break the promise). We need
a precise semantics that's achievable AND useful.

## Decision

**Two-level round-trip promise:**

1. **Byte-lossless (UNIVERSAL under precondition):** for any valid UTF-8
   string `s` with length ≤ `Sys.max_string_length`,
   `Cst.to_source (Cst.of_source s) = Ok s` — as bytes.
   Achieved via `Unparsed { text; span; reason }` nodes as fallback
   for any span the structured parser rejects.

2. **Structure-lossless (SUBSET):** for documents in the declared
   subset (ADR-006), the CST is fully structured — every token, group,
   env is a typed node. No `Unparsed` fallbacks.

## Alternatives considered

- **Option A: Promise "lossless" without precondition.**
  Can't be universally true (bit-flipped binary input is not
  representable). Rejected as dishonest.
- **Option B: Promise only structure-lossless (subset only).**
  Loses the user-friendly "bytes come back unchanged" guarantee for
  out-of-subset input. Rejected.
- **Option C: No fallback node; subset failures are errors.**
  Users feeding arbitrary LaTeX through the pipeline would get errors
  instead of round-trippable results. Bad UX. Rejected.

## Consequences

- CST type has an `Unparsed` variant as a first-class fallback.
- `Cst.of_source` never fails on valid UTF-8; at worst produces a CST
  dominated by `Unparsed`.
- `CSTRoundTrip.v` proves both levels: byte-lossless requires a lemma
  that `Unparsed { text; span; _ }` emits exactly `text`; subset-
  lossless requires a lemma for each structured variant.
- Rewrite engine can only target typed nodes; `Unparsed` regions are
  not editable via `Cst_edit`. Users who want to edit verbatim blocks
  must operate on the pre-CST source directly.
