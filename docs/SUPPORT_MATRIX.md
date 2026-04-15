# Repo-exact support matrix

## Release state taxonomy

- **GA**: supported for external users; part of the product contract.
- **Beta**: available but still allowed to change in non-breaking ways.
- **Experimental**: feature-flagged; excluded from strongest proof/perf claims.
- **Research**: not part of supported product behaviour.

## Engines

| Engine | Status | Notes |
|---|---|---|
| pdfLaTeX | GA | Primary target for v25/v26 deterministic support. |
| XeLaTeX | Beta | Supported where Unicode/font handling is already covered. |
| LuaLaTeX | Beta | Accepted with tighter package/profile boundaries. |
| pTeX / upTeX | Experimental | CJK compatibility shim exists; not part of strongest guarantees. |

## Document/project modes

| Mode | Status | Notes |
|---|---|---|
| Single-file article/report/book | GA | Current strongest support boundary. |
| Single-file with compile-log checks | Beta | Build-coupled, not keystroke-critical. |
| Multi-file `\input` / `\include` project | Planned for v26 | Requires project graph and dependency invalidation. |
| Beamer | Deferred | Pilot only after project graph substrate exists. |

## Macro support

| Macro class | Status | Notes |
|---|---|---|
| Built-in macro catalogue | GA | Existing catalogue remains core mechanism. |
| Bounded `\newcommand` / `\renewcommand` / `\providecommand` subset | Planned for v26 | Must be terminating, argument-safe, cycle-detected. |
| Arbitrary `\def`, catcode mutation, macro metaprogramming | Unsupported in guaranteed mode | Explicitly outside LP-Core. |

## Rule proof classes

| Class | Status | Meaning |
|---|---|---|
| Formal / faithful | GA | Rule logic matches formal model closely enough to justify strong soundness claims. |
| Formal / conservative | GA | Rule is covered by a theorem, but via a conservative wrapper or contract boundary. |
| Statistically validated | GA where explicitly marked | Formal theorem about metric threshold, not semantic equivalence. |
| Heuristic / advisory | Avoid | Keep empty if possible; otherwise surface clearly. |

## Interfaces

| Interface | Status | Notes |
|---|---|---|
| CLI | GA | Primary external interface. |
| REST | GA | Current service interface. |
| gRPC streaming | Deferred to late v26/v27 | Not the primary blocker for capability. |
| IDE/LSP-grade interaction | Planned | Requires partial-document semantics and CST/rewrite substrate. |

## Collaboration/editorial platform

| Capability | Status |
|---|---|
| Comments / review threads | Planned for v27 |
| Track changes / accept-reject | Planned for v27 |
| Project permissions / roles | Planned for v27 |
| Institutional deployment / audit logs | Planned for v27 |
| House-style profiles / waivers | v26 |
