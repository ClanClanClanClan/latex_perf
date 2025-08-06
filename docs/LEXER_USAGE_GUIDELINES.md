# Lexer Usage Guidelines

**LaTeX Perfectionist v25** - Production Lexer Selection and Usage

## Executive Summary

Following the reconciled L0 Lexer specification (V3-2025-08-04), the lexer architecture is being revised with realistic performance targets. The optimized L0 lexer will become the primary implementation with a mandatory scalar performance target of ≤20ms for 1.1MB documents.

## Performance Targets (Revised)

Based on the new L0 Lexer specification:

| Implementation | Target | Status | Notes |
|----------------|--------|--------|-------|
| **L0 Scalar (Optimized)** | **≤20ms** | **In Development** | **Mandatory for v25 GA** |
| L0 SIMD (Optional) | ≤8ms | Future | Optional enhancement |
| Current Insane_fast_lexer | 21.8ms | Working | Temporary solution |
| Current L0_lexer | 48.1ms | Working | To be optimized |

## Current State (Transitional)

Until L0 lexer optimization is complete (Week 39), continue using:

### 🏆 TEMPORARY: Insane Fast Lexer
```ocaml
(* Use until L0 optimization complete *)
let tokens = Core.Insane_fast_lexer.lex_insane latex_string
```
- **Performance**: 21.8ms for 1.1MB
- **Status**: ✅ Production ready (temporary)
- **Migration**: Will transition to optimized L0

### 🔄 IN DEVELOPMENT: L0 Lexer (Being Optimized)
```ocaml
(* Current implementation - optimization in progress *)
let tokens = Core.L0_lexer.tokenize latex_string
```
- **Current Performance**: 48.1ms (to be improved to ≤20ms)
- **Target Performance**: ≤20ms (2.4x speedup required)
- **Timeline**: Week 39 completion

## Optimization Plan

Per the L0 Lexer specification, optimization techniques include:
- `Bytes.unsafe_get` to eliminate bounds checks
- Bigarray ring buffer for token output
- Arena allocation to reduce GC pressure
- Branch-free catcode lookup table
- Single-pass state machine

## Core Types (Stable)

All lexers use the v25 token specification:

```ocaml
type token =
  | TChar of Uchar.t * Catcode.catcode
  | TMacro of string  
  | TParam of int
  | TGroupOpen
  | TGroupClose
  | TEOF

type located_token = {
  token: token;
  loc: Location.t;
}
```

**Note**: These types are stable and will NOT change in v25.

## Migration Timeline

1. **Now - Week 38**: Use Insane_fast_lexer for production
2. **Week 39**: L0 scalar optimization complete (≤20ms target)
3. **Week 40+**: Transition to optimized L0 as primary lexer
4. **Week 48**: Optional SIMD enhancement (≤8ms stretch goal)

## Integration Example

```ocaml
(* Future-proof implementation *)
let process_latex_file filename =
  let ic = open_in filename in
  let content = really_input_string ic (in_channel_length ic) in
  close_in ic;
  
  (* Use module alias for easy migration *)
  let module Lexer = Core.Insane_fast_lexer in (* Will change to L0_lexer *)
  let tokens = Lexer.lex_insane content in (* Method name may differ *)
  
  (* Process tokens... *)
  List.iter (fun tok -> 
    Printf.printf "%s\n" (Core.Lexer_v25.token_to_string tok.token)
  ) tokens
```

## Performance Validation

New performance targets based on empirical measurements:
- **Hardware**: Apple M2-Pro, Intel i7-12700H
- **Test File**: perf_big.tex (1,118,944 bytes)
- **Method**: 200 warmup + 100 measured runs

| Path | Median | p95 | Throughput |
|------|--------|-----|------------|
| Baseline | 81ms | 83ms | 13.6 MB/s |
| Current best | 40ms | 42ms | 27.5 MB/s |
| **Target (scalar)** | **≤20ms** | **≤21ms** | **≥55 MB/s** |
| Stretch (SIMD) | ≤7ms | ≤8ms | ≥157 MB/s |

## Archived Implementations

Moved to `archive/broken-lexers/`:
- Original `lexer_v25.ml` with O(n²) bug
- Experimental chunk/layer implementations

## Key Changes from Previous Guidelines

1. **Performance Target**: Changed from 42ms end-to-end SLA to 20ms lexer-specific target
2. **Primary Lexer**: L0_lexer will become primary after optimization
3. **SIMD Path**: Now optional, not required for v25 GA
4. **Type Stability**: Guaranteed no breaking changes

## References

- Canonical Specification: `specs/L0_LEXER_SPEC.md`
- Performance Tests: `test/test_production_lexers.ml`
- Optimization Tracking: Week 39 gate in CI

---
*Last updated: 2025-08-04*  
*Reflects L0 Lexer Specification V3*