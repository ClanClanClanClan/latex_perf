# Partial-document semantics (memo §6)

**Status.** v26.1 substrate, retroactively spec'd in the v26.2 pre-tag
audit. Runtime and proofs shipped in v26.0/v26.1; this document makes
the contract explicit.

**Authoritative sources.** `specs/REPO_EXACT_MISSING_ARCHITECTURE_MEMO_V26_V27.md`
§6. See also `specs/v26/partial_document_semantics.yaml` for the
machine-readable taxonomy.

---

## 1. Problem

An interactive LaTeX editor must keep rendering useful feedback while
the user is mid-edit. Naïve approaches either (a) refuse to parse
when input is ill-formed, discarding all feedback, or (b) swallow
errors and emit wrong feedback elsewhere. Memo §6 requires neither.

## 2. Contract

The partial-document contract has four invariants:

1. **Locality of damage (E0).** An unclosed construct at position `p`
   damages only the paragraph containing `p`; zones strictly outside
   that paragraph keep their prior trust level.
2. **Bounded damage radius (E1).** For any error, the damaged region
   is the `paragraph_bounds` interval — not the whole document.
3. **Monotonic repair (E2).** If a later edit strictly reduces the
   error set without crossing dependency boundaries, every zone's
   trust level is preserved or improved.
4. **Stable node IDs (E3).** Edits that leave a node's bytes
   unchanged leave its `Node_id.content_id` unchanged; edits that
   shift a node forward/backward by `Δ` shift only its offset by
   `Δ` without changing `content_id`.

## 3. Runtime counterpart

Runtime modules (all under `latex-parse/src/`, aliased under
`core/l2_parser/` per ADR-001):

| Module | Purpose |
|--------|---------|
| `Partial_cst` | Classifies a document by error-touching zones; emits `trust_zones : {Complete \| Partial \| Broken} list`. |
| `Error_recovery` | Bounded recovery points, `is_repaired` / `is_repaired_with_deps` predicates, `dependency_boundary` records for E2. |
| `Node_id` | Span + command-hash identifier; `of_located` constructs IDs from `Parser_l2.located_node`; stable under local edits per E3. |

## 4. Proof map

| Invariant | Proof file | Theorem |
|-----------|-----------|---------|
| E0 | `proofs/PartialParseLocality.v` | `partial_parse_locality`, `classify_invariant_under_distant_error` |
| E1 | `proofs/DamageContainment.v` | `damage_is_contained`, `is_strict_subset_transitive` |
| E2 | `proofs/RepairMonotonicity.v` | `repair_restores_trust_outside_boundaries`, `partial_cst_zone_trusted_under_bounded_repair` |
| E3 | `proofs/StableNodeIds.v` | `of_located_stable_under_local_edit`, `content_id_invariants` |

Zero admits, zero axioms across all four files.

## 5. Status taxonomy

Trust zones classify document regions by confidence:

- **Complete** — no error in the zone's paragraph; fully trusted.
- **Partial** — the zone is adjacent to an error paragraph; rules may
  fire but lower-confidence results are expected.
- **Broken** — the zone's paragraph contains an error; rules should
  treat the zone as un-parseable.

Runtime surface: `Partial_cst.partial_document.confidence` aggregates
to the worst zone classification. `trust_zones` preserves per-zone
detail.

## 6. Out of scope

- **Full incremental reparse.** We classify, we do not re-parse in place.
  Full incremental parsing is v26.3+ scope.
- **Editor-level optimistic rendering.** The editor may choose to
  continue showing stale ASTs for `Broken` zones; the contract says
  nothing about UI behaviour.
- **Multi-file propagation.** Zones are single-file; cross-file
  propagation is deferred to `Dependency_graph` + `Invalidation`
  (memo §9).

## 7. References

- ADR-001 — `core/l2_parser/` alias pattern.
- `docs/ARCH.md` — layered architecture.
- `proofs/ADMISSIBILITY_MAP.md` — what hypotheses (if any) the
  partial-document proofs leave open.
- Memo §6.1–§6.5 — original specification.
