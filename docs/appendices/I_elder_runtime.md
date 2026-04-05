# Appendix I — Incremental "Elder" Runtime Architecture

Per v25 master plan §15, Table I (72 pages).

## I.1 Overview

The Elder runtime is the incremental analysis engine that manages document state across edits. It orchestrates the five-layer pipeline (L0-L4), maintains cross-layer consistency via version vectors, and enables sub-millisecond response times on keystroke edits.

## I.2 Core Components

### I.2.1 Layer Sync (`layer_sync.ml`)

**Purpose**: Ensure validators observe consistent snapshots across layers.

**Mechanism**: Each artefact carries `{ gen : int; parent_gen : int }`. Layer N accepts deltas iff `parent_gen = Layer(N-1).gen`.

```ocaml
type version_vector = { gen : int; parent_gen : int }
type snapshot = { generation : int; data : string }
```

**Atomic generation counter**: `Atomic.make 0` — incremented on each successful layer update. Validators read snapshots by `Atomic.get`, never observe partial state.

**Proof**: `proofs/SnapshotConsistency.v` — snapshot reads are consistent (either old or new, never interleaved).

### I.2.2 Event Bus (`event_bus.ml`)

**Purpose**: Pub/sub event dispatch for semantic deltas.

**Events**:
- `LabelDefined of string * loc` — a `\label{...}` was found
- `RefUsed of string * loc` — a `\ref{...}` was used
- `SectionStarted of int * string` — section at level with title
- `EnvironmentOpened of string` — `\begin{env}`
- `EnvironmentClosed of string` — `\end{env}`

**Subscribers**: 3 registered in `run_all`:
1. Label counter — tracks label definitions
2. Ref counter — tracks reference uses
3. Environment counter — tracks open/close balance

**Transport**: `lockfree_queue.ml` — MPMC ring buffer using OCaml 5.x Atomic. Target: 8M events/sec.

### I.2.3 Dirty-Region Detection

**Suffix Array** (`suffix_array.ml`): O(n log²n) build, O(log n) search.

**Dirty Region** (`parser_l2.ml:find_dirty_region`): Computes minimal `[start, end)` byte range that differs between old and new source. Only the dirty region needs re-parsing.

**Algorithm**:
1. Scan forward from start: find first differing byte
2. Scan backward from end: find last differing byte
3. Return `{ dr_start; dr_end }`

### I.2.4 Cache System (`cache_key.ml`)

**Hash**: DJB2 over `(source, validator_count, language)`.

**TTL**: Configurable time-to-live for cached results.

**Integration**: `run_all` checks cache before running validators. On hit, returns cached results immediately.

## I.3 Execution Flow

```
Edit event (keystroke)
  │
  ├─ find_dirty_region(old_src, new_src)
  │     → { dr_start = 142; dr_end = 156 }
  │
  ├─ cache_key.compute(new_src, validators, lang)
  │     → hash = 0x7F3A2B1C
  │     → cache miss (source changed)
  │
  ├─ layer_sync.new_snapshot()
  │     → generation = 47
  │
  ├─ L0 tokenize (full document, < 3ms for 1MB)
  ├─ L1 expand (macro catalogue, deterministic)
  ├─ L2 parse (PEG recursive descent)
  ├─ run_all validators
  │     ├─ semantic_state: extract labels/refs
  │     ├─ event_bus: publish semantic deltas
  │     ├─ evidence_scoring: assign confidence
  │     └─ collect results
  │
  ├─ cache_key.store(hash, results)
  │
  └─ Return diagnostics
```

## I.4 Dependency DAG (`validator_dag.ml`)

**Construction**: Kahn's topological sort at startup.

**Input**: Each validator declares `{ id; requires; conflicts }`.

**Output**: Execution order respecting dependencies.

**Cycle detection**: If topological sort fails to consume all nodes, a cycle exists → bootstrap failure.

**Proof**: `proofs/ValidatorGraphProofs.v` — acyclicity given successful sort.

## I.5 Cross-Layer Consistency Protocol

**Resolves**: Moderate Concern #1 from spec audit.

| Concept | Decision |
|---------|----------|
| Version Vector | `{ gen; parent_gen }` per artefact |
| Memory Barrier | `Atomic` generation counter; swap-and-publish |
| Rollback | On error, roll back child layer only |
| Consistency Window | At most one generation |

**Proof**: `proofs/ElderProofs.v` — `update_preserves_length`, `update_at_correct`.

## I.6 Semantic State (`semantic_state.ml`)

**Per-document state**: Labels, refs, duplicates, undefined refs, forward refs.

**Thread-local**: `set_state`/`get_state` via thread-local storage.

**Consumers**: REF-001 (duplicate labels), REF-002 (undefined refs), REF-009 (forward refs).

**Integration**: Wired into `run_all` — semantic state is built before validators execute.

## I.7 Float Tracking (`float_tracking.ml`)

**Purpose**: Track distance between `\begin{figure}` and corresponding `\ref{fig:...}`.

**Used by**: FIG-018 (float distance > 3 pages).

**Algorithm**: Extract figure positions and ref positions, compute char/line distance.

## I.8 Performance Characteristics

| Operation | Target | Measured |
|-----------|--------|----------|
| Full document (1.1 MB) p95 | < 25 ms | 3.25 ms |
| Edit window (4 KB) p95 | < 1 ms | 0.075 ms |
| First-token p95 | < 350 µs | 27 µs |
| Cache hit | O(1) | < 1 µs |
| Dirty-region detection | O(n) | < 0.1 ms |

## I.9 Error Handling

**Error propagation**: Each `apply_delta` returns `(Result<'a, Error.t> * delta_out)`. Errors bubble without committing partial state.

**Recovery**: On validator crash, the specific validator is disabled for the current run. Other validators continue.

**Logging**: Errors are collected in `document.errors` list with source location.
