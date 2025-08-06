# Catcode Module Development Plan (Week 2-3)

## Overview
Per PLANNER.yaml Section 14.2, Week 2-3 focus: **Catcode module + proofs (Lexer)**

## Current Status
- **Existing file**: `src/core/lexer/LatexCatcodes.v` ✅ (foundation exists)
- **Proof file**: `proofs/Catcode.v` ✅ (scaffolded)
- **Target**: Complete with 0 admits, SIMD table stub

## Development Tasks

### Week 2 Tasks
1. **Catcode Core Implementation**
   - Review existing `src/core/lexer/LatexCatcodes.v`
   - Extend catcode classification functions
   - Add SIMD table preparation hooks

2. **Proof Development**  
   - Work on `proofs/Catcode.v` completeness
   - Eliminate any remaining scaffolded admits
   - Ensure catcode classification correctness

3. **SIMD Infrastructure**
   - Create SIMD table stub (per specification)
   - Prepare for Week 4 xxHash scalar implementation
   - Performance measurement integration

### Week 3 Tasks
1. **Proof Completion**
   - All catcode proofs QED 
   - 0 admits maintained
   - Integration testing

2. **Performance Preparation**
   - Catcode table optimization for SIMD
   - Benchmark catcode classification speed
   - Prepare for Week 4 chunk infrastructure

## Success Criteria

### Functional Requirements
- [ ] Catcode classification working correctly
- [ ] All proofs complete with 0 admits
- [ ] SIMD table stub implemented
- [ ] Integration with existing lexer

### Performance Requirements  
- [ ] Catcode classification not regressing performance
- [ ] SIMD infrastructure ready for Week 4
- [ ] Measurement harness integration

### Proof Requirements
- [ ] proofs/Catcode.v fully proven (0 admits)
- [ ] Catcode correctness theorems complete
- [ ] Classification soundness proven

## Integration Points

### With Lexer
- `src/core/lexer/LatexCatcodes.v` → `src/core/lexer/LatexLexer.v`
- Catcode classification in tokenization pipeline
- Performance impact measurement

### With Performance Gates
- Catcode speed critical for Week 4 <4ms target
- SIMD table preparation for Week 5 <2ms target
- Performance regression testing

## Files to Work On

### Primary
- `src/core/lexer/LatexCatcodes.v` - Core implementation
- `proofs/Catcode.v` - Formal verification

### Secondary  
- `src/core/lexer/LatexLexer.v` - Integration point
- Performance measurement integration
- SIMD table generation scripts

## Risk Management

### Technical Risks
- Catcode complexity may impact performance
- SIMD table generation complexity
- Proof obligations for classification correctness

### Timeline Risks
- Week 4 gate dependency on completion
- Performance optimization pressure from 14.07ms → <4ms need
- Integration complexity with existing lexer

This plan ensures Week 2-3 catcode work supports both formal verification requirements AND critical performance optimization path.