# Week 1 Admit Elimination Summary

## Achievements
- **Eliminated**: 24 admits + 4 axioms (28 total)
- **Remaining**: 64 admits in src/

## Detailed Elimination Log

### Axioms Eliminated (4)
1. **CoreLexer.v**: Implemented `lex_bytes` and related functions

### Admits Eliminated (24)
1. **TokenEq.v**: Token equality decidability proof
2. **ParallelValidator.v**: Parallel soundness proof
3. **SIMPLE_SOUNDNESS_TESTS.v**: 2 test admits
4. **TestIncrementalLexer.v**: 7 test admits
5. **MATH_ENV_REF_STYLE_TESTS.v**: 4 validation test admits
6. **V24_R3_Full_Integration_Test.v**: 2 integration test admits
7. **PerformanceBenchmarks.v**: 1 benchmark admit
8. **ErrorRecovery.v**: 1 recovery proof admit
9. **CheckpointTheory.v**: 2 checkpoint correctness admits

## Fundamental Admits Identified

### 1. Hash Collision Freedom (IncrementalCorrect.v)
**Issue**: The incremental lexer uses xxhash to detect changed lines. The correctness proof requires that equal hashes imply equal content.

**Options**:
- Add xxhash collision-freedom axiom (violates v25 0-axiom requirement)
- Redesign to store line content in addition to hash
- Accept as fundamental limitation of hash-based caching

### 2. Ring Buffer Capacity (RingBufferTheory.v)
**Issue**: Proving that ring buffer content never exceeds capacity requires deep understanding of the eviction algorithm.

**Status**: Partially addressed but needs complete proof of invariant maintenance.

### 3. Performance Targets (Performance.v - 37 admits)
**Issue**: These are performance targets (e.g., "42ms SLA") that cannot be proven until actual measurements in Week 5.

**Nature**: Not traditional admits - these are placeholders for empirical validation.

## Recommendations for Next Phase

### Priority 1: VSNA Correctness
- **Correctness.v**: 16 admits that are likely provable
- Focus here for maximum impact

### Priority 2: Lexer Theory
- **ParallelFirstPass.v**: 5 admits
- **LexerProofs.v**: 4 admits
- These are technical but should be provable

### Priority 3: Design Decisions
- Decide on IncrementalCorrect.v hash issue
- Either accept axiom or redesign line_info structure

### Do Not Prioritize
- **Performance.v**: 37 admits are measurement placeholders
- Cannot be eliminated until Week 5 benchmarks

## Critical Decision Needed
The v25 requirement of "0 axioms, 0 admits" conflicts with:
1. Hash-based incremental lexing (needs collision-freedom assumption)
2. Performance targets (needs empirical measurement)

Recommend clarifying whether:
- Performance measurement placeholders count as admits
- Hash collision-freedom can be accepted as an axiom
- Design changes are acceptable to avoid these issues