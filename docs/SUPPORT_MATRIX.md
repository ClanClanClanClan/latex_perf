# Repo-exact support matrix

> **Source of truth:** `docs/SUPPORT_MATRIX.yaml`. This document is a narrative wrapper — please keep both in sync (CI enforces agreement via `scripts/tools/check_repo_facts.py`).
>
> **Memo reference:** `specs/REPO_EXACT_MISSING_ARCHITECTURE_MEMO_V26_V27.md` §12.

## Release state taxonomy

- **GA**: supported for external users; part of the product contract.
- **Beta**: available but still allowed to change in non-breaking ways.
- **Alpha**: available but feature-incomplete; interface may change.
- **Experimental**: feature-flagged; excluded from strongest proof/perf claims.
- **Planned**: scoped for a future release; not available yet.
- **Deferred**: acknowledged need but no committed schedule.
- **Research**: not part of supported product behaviour.

## Engines

| Engine | Status | Tier | Notes |
|---|---|---|---|
| pdfLaTeX | GA | LP-Core | Primary target for v26 deterministic support. **The compile-guarantee verdict is pdflatex-computed today**: the runtime defaults every project to pdflatex and the differential harness runs pdflatex only. |
| XeLaTeX | Planned | LP-Extended | **Not yet a distinct engine at runtime.** The compile-guarantee capstone `xelatex_compile_safe` is currently a **proof-alias** (`:= pdflatex_compile_safe`); `--compile-check` defaults the engine to pdflatex, so the verdict is pdflatex-computed. Real per-engine coverage (distinct Unicode/font semantics) is planned under roadmap Track **S-ENGINE**. |
| LuaLaTeX | Planned | LP-Extended | **Not yet a distinct engine at runtime.** `lualatex_compile_safe` is likewise a **proof-alias** (`:= pdflatex_compile_safe`) and the runtime resolves to pdflatex; real per-engine coverage is planned under roadmap Track **S-ENGINE**. |
| pTeX / upTeX | Experimental | LP-Extended | CJK compatibility shim exists; not part of strongest guarantees. Verdict is pdflatex-computed today (see S-ENGINE). |

## Document/project modes

| Mode | Status | Notes |
|---|---|---|
| Single-file article/report/book | GA | Current strongest support boundary. |
| Single-file with compile-log checks | Beta | Build-coupled; Class C rules isolated from keystroke-critical path. |
| Multi-file `\input` / `\include` project | Planned | **`--compile-check` reads the ROOT `.tex` only at present**: T0 parses the root source and T2 checks that `\input`/`\include` targets *resolve* (existence + no cycle), but content inside `\input`ed children is **not** parsed or linted. Full project/include-expansion (linting expanded child content, cross-file labels/refs on the lint path) is planned under roadmap Track **S-PROJ**. |
| Beamer | Deferred | Pilot only after the project-graph substrate stabilises (roadmap S-PROJ). |

## Macro support

| Macro class | Status | Notes |
|---|---|---|
| Built-in macro catalogue | GA | 520 entries (441 symbol + 79 argsafe) in `core/l1_expander/macro_catalogue.json`. |
| Bounded `\newcommand` / `\renewcommand` / `\providecommand` subset | GA | Terminating, argument-safe, cycle-detected. Shipped in v26.0 (WS2). |
| Arbitrary `\def`, catcode mutation, macro metaprogramming | Unsupported in guaranteed mode | Detected by `Unsupported_feature.detect` — classifies document as LP-Extended or LP-Foreign. |

## Language contract tiers (memo §4)

| Tier | Status | Contract | Proof |
|---|---|---|---|
| LP-Core | GA | Fully guaranteed subset; see `specs/v26/language_contract.md`. | `proofs/LanguageContract.v` |
| LP-Extended | Beta | Practical but weaker contracts; bounded LP-Foreign feature detection. | Partial (conservative). |
| LP-Foreign | GA (detection) | Explicit rejection domain; surfaced via `--profile` banner. | `LanguageContract.classify_lp_foreign_sound`. |

## Rule proof classes (memo §9)

Canonical counts live in `governance/project_facts.yaml` (regenerated per
release). Current ship state:

| Class | Status | Rule count | Meaning |
|---|---|---|---|
| Formal / faithful | GA | 637 | Rule logic matches formal model closely enough to justify strong soundness claims. |
| Formal / conservative | GA | 20 | Rule covered by theorem via a conservative wrapper (`check = false`) for external binary checks. |
| Formal / conditional | GA | 3 | Sound given log predicate. LAY-025/026/027 compile-log-derived rules. |
| Statistically validated (overlay) | GA | 8 | v2 ByteClassifier precision/recall bounds in `proofs/ML/SpanExtractorSound.v`. Overlay on faithful proofs for 8 ambiguous TYPO rules. |
| Heuristic / advisory | Avoid | 0 | Kept empty if possible; otherwise surfaced clearly. |

## Execution classes (memo §11)

| Class | Name | Budget | Permitted state reads | Proof |
|---|---|---|---|---|
| A | keystroke-critical | p95 ≤ 1.2 ms | hot-path only | `proofs/ExecutionClasses.v class_a_reads_only_hot_path` |
| B | debounce background | p95 ≤ 100 ms | hot-path only | (same file) |
| C | build-coupled | async (save/build/request) | hot-path + build-log + external-binary | `class_c_requires_build_profile` |
| D | optional heuristic | async | hot-path + ML confidence | `class_d_advisory_only` |

Hot path excludes C and D: `hot_path_excludes_cd` + runtime `Execution_class.is_keystroke_safe`.

## Interfaces

| Interface | Status | Notes |
|---|---|---|
| CLI | GA | Primary external interface; `--profile`, `--log`, `--layer`, `--project` flags. |
| REST | GA | `POST /tokenize`, `/expand`. Env gates: `L0_VALIDATORS`, `L0_PROFILE_OVERRIDE`. |
| gRPC streaming | Deferred | Not the primary capability blocker; no committed schedule (see roadmap `docs/v27/ROADMAP.md`). |
| IDE/LSP-grade interaction | Planned | Requires lossless CST + rewrite substrate (now shipped); scheduled per roadmap `docs/v27/ROADMAP.md`, memo §7. |

## Collaboration/editorial platform

| Capability | Status | Target release |
|---|---|---|
| Comments / review threads | Parked (ADR-010) | pending product decision |
| Tracked changes / accept-reject | Parked (ADR-010) | pending product decision |
| Project permissions / roles | Parked (ADR-010) | pending product decision |
| Institutional deployment / audit logs | Parked (ADR-010) | pending product decision |
| House-style profiles / waivers | Parked (ADR-010) | pending product decision |

Per memo §13 (editorial policy) and §14 (collaboration). The WS10 (collaboration) and
WS11 (platform / multi-user) workstreams are **PARKED pending a product decision
(ADR-010)** — they are not scheduled for a v27 release. Not in scope for any v26 release.
