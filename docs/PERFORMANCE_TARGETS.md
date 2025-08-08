# LaTeX Perfectionist v25 - Standardized Performance Targets
**Last Updated: August 7, 2025**

## 🎯 OFFICIAL PERFORMANCE TARGETS

### L0 Lexer Performance
- **Target**: ≤20ms for 1.1MB files
- **Status**: ✅ **ACHIEVED** - Arena implementation: 17.7ms P95
- **Throughput**: 55 MB/s minimum (achieved: 62.1 MB/s)

### Overall System Performance (Future)
- **Total Processing Time**: <42ms for complete validation pipeline
- **Component Breakdown**:
  - L0 Lexing: ≤20ms (✅ achieved: 17.7ms)
  - L1 Expansion: ≤10ms (pending)
  - L2 Parsing: ≤8ms (pending)
  - L3-L4 Validation: ≤4ms (pending)

### Orchestrator Latency
- **P95 Target**: 40μs per edit operation
- **Hard Cutoff**: 80μs (triggers warning)
- **Purpose**: Cross-layer coordination overhead

## 📊 MEASUREMENT METHODOLOGY

### Standard Test File
- **Size**: 1.1MB (1,100,000 bytes)
- **Location**: `corpora/perf/perf_smoke.tex`
- **Content**: Representative academic paper

### Measurement Protocol
1. **Warmup**: 1 run discarded
2. **Iterations**: 5 runs minimum
3. **Metric**: P95 (95th percentile)
4. **Environment**: OCaml 5.1.1+jst with alternative build system

## ⚠️ DEPRECATED/INCORRECT REFERENCES

The following performance claims found in various files are **INCORRECT**:
- ~~"<1ms p99"~~ - Unrealistic for 1.1MB files
- ~~"132.61ms"~~ - Old measurement before arena optimization
- ~~"Week 39/48 gates require C/SIMD"~~ - Arena achieved target with pure OCaml

## ✅ CURRENT STATUS

**L0 Lexer**: Performance target ACHIEVED
- Arena-based implementation delivers 17.7ms P95
- No C/SIMD required for Week 39 gate
- Pure OCaml solution with GC pressure eliminated

**Next Focus**: L1-L4 implementation to meet overall 42ms target

---

*This document is the single source of truth for performance targets.*
*All other performance references should defer to this document.*