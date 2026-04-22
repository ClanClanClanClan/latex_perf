# ADR-003: Four graphs (not three) — distinct modules

- **Status:** Accepted (2026-04-22, corrected from v3 plan which said three)
- **Context owner:** v26.2 architectural decisions (plan §2.3)

## Context

V26.1 shipped `project_graph.ml` and `dependency_graph.ml`. V26.2
introduces `build_graph.ml`. The v3 plan treated these as "three graphs"
and proposed `docs/THREE_GRAPHS.md`. The v4 audit caught a miss:
`Validator_dag` in `validator_dag.ml` (shipped v26.0) is also a
runtime graph. So there are four.

## Decision

**Four distinct graph modules. Documented in `docs/FOUR_GRAPHS.md`** (to be
written during PR A1).

| Module | Nodes | Edges | Purpose |
|---|---|---|---|
| `Validator_dag` | rule IDs | `consumes`/`provides` deps + `conflicts_with` | rule execution ordering + conflict detection |
| `project_graph` | .tex files | `\input` / `\include` edges | multi-file project structure |
| `dependency_graph` | chunks | semantic edits that invalidate consumers | incremental re-validation |
| `build_graph` | artefacts (tex / aux / bbl / pdf) | produce-from edges | build-pipeline order + .aux/bbl readiness |

## Alternatives considered

- **Option A: Unified graph with edge-type tagging.**
  Conceptually elegant; in practice, the four use cases have different
  node types (string ID vs file path vs chunk index vs artefact) and
  different algorithms (Kahn's topo-sort vs BFS reachability vs fixpoint).
  Unifying would create a weakly-typed abstraction and complicate every
  specific consumer. Rejected for v26.2; re-evaluate in v27.
- **Option B: Rename for clarity.**
  E.g. `Validator_dag` → `rule_dag`. Breaking change to a shipped API.
  Rejected.

## Consequences

- `docs/FOUR_GRAPHS.md` becomes a mandatory onboarding read.
- Each graph has its own test file, proofs (where applicable), and
  invalidation semantics. No cross-contamination.
- Future unified-graph refactor is a v27 consideration.
