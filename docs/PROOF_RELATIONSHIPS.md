# Proof relationships — v26.2

Map of the formal proof tree: which theorems depend on which, which
are hypothesis-parametric, and where v27 WS8 discharges the remaining
hypotheses.

## 1. T0–T7 compile-guarantee stack

```
              Parser_l2.parse
                    ▲
  T0 ────────────── │ (ParserSound.v: identity_parse_sound,
                    │  flatten_* totality lemmas)
                    │
                    ▼
               T0_wrapper.v
                    │
                    ▼
   UserExpand.v ────┐
       │            │
  T1 ──┤            │(merge_acyclic, user_expand_deterministic)
       │            │
       ▼            ▼
  T1_wrapper.v ◄────┘
                    │
                    ▼
   ProjectSemantics ─► ProjectClosure.v (T2)
       │                     │
       │                     ▼
       │               (closed_edges_resolve,
       │                topo_covers_edge_endpoints,
       │                two_node_cycle_not_closed)
       │
   LabelsUnique ─────► T4_wrapper.v (T4)
       │                     │
       │                     ▼
       │               (T4_labels_unique_packaged,
       │                T4_coherent_under_hypotheses)
       │
       ▼                     (counters_consistent, bib_entries_resolve
                              hypothesis-parametric; v27 WS8)

                      ┌────── T3_profile_compatible
                      │      (BuildProfileSound.v — decidable,
   T3  ───────────────┤       every_engine_has_compatible_feature,
                      │       monotone, pointwise ↔ bulk)
                      │
                      ▼

  rule_contracts/* ─► T5_wrapper.v
  per-rule QEDs      (all_pass_sublist, empty_all_pass;
   (~626 ▶ 629)     hypothesis-parametric rule_safety_rule)
                              │
                              │
                              ▼
     ┌──────────────────────────────────────────────────────┐
     │  CompileProgress.v  (hypothesis-parametric, ADR-004) │
     │  T6_compile_progress_under_bound                      │
     │     input: T0..T5 + bounded_build_terminates_for      │
     │     discharge: v27 WS8 PdflatexModel.v (etc.)         │
     └──────────────────────────────────────────────────────┘
                              │
                              ▼
     ┌──────────────────────────────────────────────────────┐
     │  CompileWellFormed.v (hypothesis-parametric, ADR-004)│
     │  T7_output_wellformed                                 │
     │     input: T6 + produces + output_format_well_formed  │
     │     discharge: v27 WS8                                │
     └──────────────────────────────────────────────────────┘
```

Runtime counterpart: `Compile_contract.check_ready_to_compile` runs
T2/T3/T4 at runtime. T6/T7 are proof-only (they say "if everything
holds, compile succeeds"); the user invokes the toolchain trusting
those theorems to match the toolchain's behaviour.

## 2. Editing-semantics proofs (E-series, memo §6)

```
 PartialParseLocality.v (E0)         ── WS5
       │
       ▼
 DamageContainment.v (E1)             ── WS5
       │
       ▼
 RepairMonotonicity.v (E2)            ── P1 (v26.1)
       │
       ▼
 StableNodeIds.v (E3)                 ── P1 (v26.1)
       │
       ▼
 RewritePreservesCST.v (E4, v26.2)    ── B3
       │
       ▼
 RewritePreservesSemantics.v (E5)     ── B3
       (v26.2, hypothesis-parametric;
        v26.3+ discharges over Parser_l2)
```

The E-series guarantees no edit poisons distant regions, repair is
monotonic, node IDs are stable, and the rewrite engine preserves both
byte-losslessness and (under ws-preserving edits) token streams.

## 3. CST round-trip proofs (PR B2)

```
 CSTRoundTrip.v
   ├── byte_lossless_partition_exists   (every src has a valid partition)
   ├── serialize_inverse_of_partition    (serialize undoes any partition)
   ├── partition_compose                 (concatenation of partitions)
   │
   └── Section Structure_lossless
        ├── builder_partitions (hypothesis)
        ├── parse_serialize_is_id_on_subset (hypothesis)
        ├── structure_lossless_on_subset  (theorem)
        └── byte_lossless_full            (corollary)
```

v26.2 discharges `builder_partitions` at the OCaml level via the
runtime `test_cst_roundtrip.ml` corpus-wide sweep (345/345 files).
`parse_serialize_is_id_on_subset` is discharged for the declared
subset in v26.3 when structure-lossless ships as a corpus gate.

## 4. Language contract + execution classes (v26.1, unchanged in v26.2)

```
 LanguageContract.v        ── P1 (v26.1)
   ├── tier_membership_total
   ├── tier_eq_dec
   ├── lp_core_subset_of_extended
   ├── classify_lp_core_no_forbidden
   └── classify_sound_unsupported_features

 ExecutionClasses.v         ── P1 (v26.1)
   ├── class_a_reads_only_hot_path
   ├── class_c_requires_build_profile
   ├── class_d_advisory_only
   ├── hot_path_excludes_cd
   ├── class_cd_not_keystroke_safe
   └── exec_class_eq_dec
```

Runtime enforcement: `language_profile.ml` + `execution_class.ml`.
Anti-tautology CI gate (PR #242 p1.5) keeps the proof bodies
substantive.

## 5. Validator DAG proofs (v26.1, unchanged in v26.2)

```
 ValidatorGraphProofs.v
   ├── kahn_complete
   ├── cycle_detection_sound
   ├── empty_graph_acyclic
   ├── topo_order_respects_edge
   ├── conflicts_detected_antisymmetric
   ├── dependency_respects_topo_order
   ├── provides_unique_under_dag
   └── find_by_id_unique
```

## 6. ML proofs (v25-era, still live)

```
 proofs/ML/SpanExtractorSound.v
   (F1=0.9799 ByteClassifier bounds)
```

## 7. v27 WS8 discharge targets

v26.2 leaves the following hypotheses to be discharged by v27 WS8
(`proofs/PdflatexModel.v`, etc.):

- `CompileProgress.compile_progress_rule`
- `CompileWellFormed.output_wellformed_rule`
- `T4_wrapper.counters_consistent` + `bib_entries_resolve`
- `CSTRoundTrip.Structure_lossless` section hypotheses

See [`proofs/ADMISSIBILITY_MAP.md`](../proofs/ADMISSIBILITY_MAP.md)
for the precise discharge checklist.

## 8. Proof counts at v26.2.0

| Class | v26.1 | v26.2 | delta |
|-------|-------|-------|-------|
| Faithful (per-rule + substrate) | varies | varies | +~12 (T0–T7, CST, rewrite) |
| Conservative | varies | varies | 0 |
| Formal conditional | 3 | 3 | 0 |
| Hypothesis-parametric | 3 | 7 | +4 (T6, T7, structure-lossless, rewrite-semantics) |

Exact final numbers regenerated in `governance/project_facts.yaml`
at PR C merge time.

## 9. References

- Memo `specs/REPO_EXACT_MISSING_ARCHITECTURE_MEMO_V26_V27.md` —
  definitive spec for T0–T7.
- `specs/v26/compilation_guarantee_stack.md` — per-theorem Coq
  signature sketches.
- `docs/v26_2/adr/ADR-004-hypothesis-parametric-t6-t7.md` — rationale
  for the parametric pattern.
- `docs/v26_2/adr/ADR-005-cst-round-trip-two-level.md` — two-level
  CST scope.
- `proofs/ADMISSIBILITY_MAP.md` — v27 WS8 discharge checklist.
