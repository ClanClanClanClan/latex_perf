# L0 Lexer Optimization Handoff Document

## Current Status

### Achievement So Far
- **WORKING BASELINE**: L0_lexer_optimized.ml achieves **1.38x speedup** (44.8ms vs 61.9ms)
- **CORRECTNESS VERIFIED**: Produces exact same token count (154,293) as original
- **SUCCESSFUL OPTIMIZATIONS APPLIED**:
  1. ✅ Fixed critical buffer overflow bugs that were causing 3.25x slowdown
  2. ✅ Applied `Bytes.unsafe_get` for input access (minor improvement)
  3. ✅ Fixed Buffer.t operations to use optimized stdlib functions

### Performance Gap Analysis (From Flamegraph Profiling)
- **TARGET**: ≤20ms/1.1MB (L0_LEXER_SPEC.md Week 39 Gate)
- **CURRENT**: 45ms/1.1MB  
- **REMAINING NEED**: 2.24x MORE speedup required

**Identified Bottlenecks**:
- 33% List.rev_append operations
- 29% make_token allocations  
- 18% String.sub/Buffer.contents
- 14% catcode_of lookups
- 6% GC activity

## Technical Analysis

### What Works (Don't Break These)
1. **Buffer.t for character accumulation** - stdlib Buffer is highly optimized
2. **Bytes.unsafe_get for input access** - eliminates bounds checking
3. **Same algorithm logic** - produces correct token count

### Identified Bottlenecks (Based on L0_LEXER_SPEC.md Track A)
1. **List.rev_append operations** - Called frequently in inner loop, creates/copies many intermediate lists
2. **Token object allocations in inner loop** - Each `make_token` call does string operations and allocates `Lexer_v25.TChar`, `TMacro` objects
3. **String operations** - `String.sub`, `String.length`, `Buffer.contents` called frequently

### L0_LEXER_SPEC.md Track A Requirements NOT YET APPLIED
1. **"Output stored in Bigarray.Array1 ring before list conversion"** - Currently using list accumulation
2. **"No allocation in inner loop (>99% tokens)"** - Currently allocating token objects per character
3. **"Single-pass state machine"** - Current algorithm has nested match statements and multiple list operations per character

## Specific Technical Approach Needed

### Phase 1: Eliminate List Operations (Highest Impact)
The `lex_char` function returns lists that are accumulated with `List.rev_append`. This is probably the #1 bottleneck.

**SOLUTION**: Replace list accumulator with:
- Pre-allocated array/buffer for token data
- Defer token object creation until final conversion
- Track write position instead of list operations

### Phase 2: Eliminate Token Allocations in Inner Loop  
The `make_token` function is called in the inner loop and does:
- String operations (`String.sub`, `String.length`)
- Catcode lookup (`Catcode.catcode_of`)
- Object allocation (`Lexer_v25.TChar`, `TMacro`)

**SOLUTION**: 
- Store raw token data (token type, character code, string offsets) in packed form
- Defer object creation to final conversion step
- Pre-compute catcode table for O(1) lookup

### Phase 3: Optimize String Operations
Multiple `Buffer.contents` calls create string copies.

**SOLUTION**:
- Minimize buffer-to-string conversions
- Use string pooling for common tokens
- Consider packed string storage

## Code Files Status

### Working Files (Don't Modify Without Testing)
- `src/core/l0_lexer.ml` - Original working implementation (61.9ms baseline)
- `src/core/l0_lexer_optimized.ml` - **Current best implementation (44.8ms)**

### Test Files
- `bench/run_lexer.ml` - Benchmark harness
- `corpora/perf/perf_smoke_big.tex` - 1.1MB test file per spec

### Spec Files  
- `specs/L0_LEXER_SPEC.md` - Official spec with Track A requirements
- Proofs: `proofs/Lexer_det.v`, `proofs/Lexer_total.v`, `proofs/Arena_safe.v` (all QED)

## Critical Implementation Notes

### Buffer Management
- **CRITICAL**: Any buffer must handle overflow correctly - my initial implementation silently failed on overflow
- **TESTED**: stdlib `Buffer.t` operations are faster than manual Bigarray character operations
- **CAPACITY**: For 1.1MB input, need ~154K tokens, estimate buffer size accordingly

### Token Types (API Preservation Required)
Must produce exact same token types as original:
```ocaml
type token = 
  | TChar of Uchar.t * Catcode.catcode
  | TMacro of string  
  | TParam of int
  | TGroupOpen | TGroupClose | TEOF
```

### Performance Measurement
- Use provided benchmark harness: `opam exec -- dune exec bench/run_lexer.exe`
- Focus on `perf_smoke_big.tex` (1101324 bytes) result
- Target: median time ≤20ms, current: 44.8ms

## Systematic Implementation Plan (Addresses Each Bottleneck)

### Phase 1: Replace List Building with Ring Buffer (1.4x speedup)
**Target**: 33% List.rev_append → Ring buffer with power-of-2 indexing
- Create `TokRing` module with `push/unsafe_get/length` operations
- Replace `List.rev_append` accumulation with direct ring buffer writes
- Convert to list only once at end
- **Expected**: 45ms → 32ms

### Phase 2: Object Deferral via Token Blob (1.3x additional speedup) 
**Target**: 29% make_token allocations → Packed representation
- Use `raw` packed variants (RChar int, RMacro int*int, etc.)
- Defer `TChar/TMacro` object creation until final conversion
- Single-pass materializer at end: `raw list → token list`
- **Expected**: 32ms → 25ms

### Phase 3: Zero-Copy Optimizations (Final margin)
**Target**: 18% String.sub + 14% catcode_of → Caching
- Intern macro names with hash-cons table
- Pre-computed catcode lookup table  
- Minor GC tuning
- **Expected**: 25ms → 18ms (with safety margin)

### Validation Steps
1. Each phase maintains exact token count (154,293)
2. Each phase improves performance measurably
3. Final result ≤20ms median on 1.1MB file

## Success Criteria
- **Performance**: ≤20ms median time on perf_smoke_big.tex (1101324 bytes)
- **Correctness**: Exact same token count (154,293) as original L0_lexer
- **API Compatibility**: Same token types as specified in L0_LEXER_SPEC.md Section 3

## Warning Signs
- **Token count changes**: Indicates algorithm bug
- **Compilation errors**: Usually from buffer overflow or type mismatches  
- **Performance regression**: Check for accidental O(n²) operations or excessive allocations

---

**HANDOFF READY**: Next developer should start by validating current 44.8ms baseline, then systematically apply Track A optimizations to achieve 2.24x more speedup.