# Architecture diagram — v26.2

High-level map of the new subsystems added in v26.2 and how they
relate to the existing v26.1 substrate. Paths are repo-relative.

## 1. Layered view

```
                     ┌──────────────────────────────────────────────┐
                     │            CLI / REST / IDE clients          │
                     └──────────────┬───────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────┐
│                       latex-parse/src/validators.ml                │
│              (run_all, run_with_policy, run_advisory)              │
└──────────────┬──────────────────────────────────────┬──────────────┘
               │                                      │
               ▼                                      ▼
┌──────────────────────────────────────┐  ┌──────────────────────────────┐
│           PROJECT LAYER (v26.2)      │  │        CST LAYER (v26.2)     │
│                                      │  │                              │
│ project_model  ─► Build_graph        │  │  Parser_l2 ─► Cst_of_ast     │
│     │                                │  │      │            │          │
│     ▼                                │  │      ▼            ▼          │
│ Aux_state ◄───── file I/O            │  │   located_node  Cst.t list   │
│     │                                │  │                   │          │
│     ▼                                │  │                   ▼          │
│ Compile_contract (T2/T3/T4 gate)     │  │   Rewrite_engine ──► source' │
│     │                                │  │        ▲                     │
│     ▼                                │  │        │                     │
│  Ready | NotReady reasons            │  │    Cst_edit.t list           │
└──────────────────────────────────────┘  └──────────────────────────────┘
               │                                      │
               └────────────────┬─────────────────────┘
                                ▼
                ┌──────────────────────────────────┐
                │      Parser_l2 / catcode / L0    │
                │           (shared substrate)     │
                └──────────────────────────────────┘
```

## 2. Compile-guarantee theorem stack

```
                    +---- T0 Parser accepts  (ParserSound.v + T0_wrapper)
                    |
                    +---- T1 Expansion admissible (UserExpand.v + T1_wrapper)
                    |
   user calls       +---- T2 Project closed (ProjectClosure.v)
check_ready_to_..───┼
                    +---- T3 Profile compatible (BuildProfileSound.v)
                    |
                    +---- T4 Semantic coherent (LabelsUnique.v + T4_wrapper)
                    |
                    +---- T5 Rules pass (per-rule QEDs + T5_wrapper)
                           │
     if Ready  ───────────►│ invoke pdflatex / xelatex / lualatex
                           │
                           ▼
   T6 Compile progress  ── CompileProgress.v (hypothesis-parametric)
              │            (v27 WS8 discharges against toolchain model)
              ▼
   T7 Output well-formed ─ CompileWellFormed.v (hypothesis-parametric)
                           (v27 WS8 discharges against PDF/DVI validators)
```

Runtime counterpart: `Compile_contract.check_ready_to_compile` runs
T2/T3/T4 live and returns `Ready | NotReady reasons`. See
[`specs/v26/compilation_guarantee_stack.md`](../specs/v26/compilation_guarantee_stack.md).

## 3. CST round-trip flow

```
 source string (str)
        │
        ▼
 Parser_l2.parse_located ──► located_node list
        │                       │
        │                       ▼
        │                   Cst_of_ast.of_source
        │                       │
        │                       ▼
        │                   Cst.t list
        │                       │
        │                       ▼
        │                   Cst.serialize ───► src' (byte-lossless iff src)
        │                       │
        │                       ▼
        │                  Rewrite_engine.apply
        │                       │
        │                       ▼
        │                   src_rewritten
        │                       │
        ▼                       ▼
    <unchanged>              <new bytes>
```

Byte-lossless invariant (`CSTRoundTrip.v`):
`serialize (of_source src) = src` for arbitrary `src`.

## 4. Four graphs (ADR-003)

```
 project graph         build graph           dependency graph       invalidation graph
 (Project_graph)       (Build_graph)         (Dependency_graph)     (Invalidation)

 files + \input edges  artefacts + producer  validator DAG          zone → validator
                       /consumer edges        (rule_contracts)      re-run edges
 ── T2 source ──       ── T2 artefacts ──     ── v26.1 P1 ──         ── v26.1 WS4 ──
```

## 5. Module inventory additions in v26.2

Code (canonical paths):
- `latex-parse/src/project_model.{ml,mli}`
- `latex-parse/src/build_graph.{ml,mli}`
- `latex-parse/src/aux_state.{ml,mli}`
- `latex-parse/src/compile_contract.{ml,mli}`
- `latex-parse/src/stable_spans.{ml,mli}`
- `latex-parse/src/cst.{ml,mli}`
- `latex-parse/src/cst_of_ast.{ml,mli}`
- `latex-parse/src/cst_edit.{ml,mli}`
- `latex-parse/src/rewrite_engine.{ml,mli}`

Proofs (`proofs/`):
- `ProjectClosure.v`, `BuildProfileSound.v`, `CompileProgress.v`,
  `CompileWellFormed.v`, `T0_wrapper.v`, `T1_wrapper.v`,
  `T4_wrapper.v`, `T5_wrapper.v`, `ADMISSIBILITY_MAP.md`,
  `CSTRoundTrip.v`, `RewritePreservesCST.v`,
  `RewritePreservesSemantics.v`.

Specs / docs:
- `specs/v26/compilation_guarantee_stack.md`
- `specs/v26/compilation_profiles.yaml`
- `docs/COMPILATION_GUARANTEE.md`
- `docs/CST_ROUNDTRIP_SCOPE.md`
- `docs/PARSER_L2_AUDIT.md`
- `specs/v26/V26_2_PLAN.md` + 5 docs in `docs/v26_2/` + 8 ADRs

Corpora:
- `corpora/roundtrip/` — 15 synthetic round-trip edge cases

## 6. Dependencies between v26.2 modules

```
 stable_spans ──► cst ──► cst_of_ast ──► cst_edit ──► rewrite_engine
                                                   (uses cst_of_ast)

 project_model ──► build_graph
      │                │
      ▼                ▼
    aux_state ─────► compile_contract
```

No circular dependencies. `compile_contract` only dispatches to the
project / build / aux modules; it does not depend on the CST layer.
