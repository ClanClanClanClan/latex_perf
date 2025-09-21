# Token‑aware Validators (Design Notes)

This document outlines how we will introduce token‑aware validators once the L0 tokenizer rewire lands in the active runtime.

## Goals
- Run certain L0 validators against token streams instead of raw strings to reduce false positives and improve context sensitivity.
- Maintain performance budgets by processing only relevant token kinds (bucketing by token type).

## Integration Points
- Service: expose token spans in the Unix socket response (e.g., a compact binary frame or optional JSON for debugging).
- REST: plumb token summaries to the façade only when the feature flag is enabled (avoid payload bloat by default).
- Runtime: add a `Validators_token` module that accepts `token array` and returns validator results.

## Migration Plan
1. Token transport: add an experimental field to the service payload (off by default via feature flag) to carry a small sample of tokens.
2. Validator selection: enable token‑aware versions of high‑FP rules (quotes, bracket spacing, punctuation adjacency) first.
3. Consistency checks: double‑run string and token validators for a small canary subset and measure FP reduction.
4. Rollout: graduate token versions to default and deprecate overlapping string variants.

## Performance Considerations
- Keep token projections simple (kind, start, end), avoid copying text.
- Use buckets: process only text tokens for typography, command tokens for command rules, etc.
- Batch across windows to leverage cache locality.

## Testing
- Reuse existing golden corpora; add token snapshots for a subset to verify exact locations.
- Wire into CI as an optional job (feature‑flagged) until stabilized.

## Status
- Pending L0 tokenizer rewire; no code changes in this repository yet.

