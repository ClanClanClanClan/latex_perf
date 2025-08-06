# Week 2+ Development Roadmap

## Current Status (Week 1 Complete ✅)
- **Formal Verification**: 0 admits achieved (exceeded target of ≤63)
- **Repository**: Ultra-audit complete, perfectly organized
- **Performance**: 14.07ms (CRITICAL optimization needed for gates)
- **Tagged**: v25-R0-2025-07-28-ground-truth

## CRITICAL PATH: Performance Optimization

### Reality Check
- **Current**: 14.07ms
- **Week 4 target**: <4ms ❌ (need 71% improvement) 
- **Week 5 target**: <2ms ❌ (need 86% improvement)
- **Performance gates are BLOCKING** - must be solved

### Optimization Strategy (per v25_master.yaml)
1. **Pure OCaml optimization**: Target 15ms (we're at 14.07ms)
   - Already achieved via bigarray, unsafe_gets, domain_parallelism
2. **C Extension required**: Target 2ms for Week 5 gate
   - AVX2 kernels, zero-alloc, runtime fallback
   - SIMD: AVX-512, NEON, portable scalar fallback

## Week 2-3 Development (per PLANNER.yaml)

### Primary: Catcode Module + Proofs
- **Location**: `src/core/lexer/LatexCatcodes.v` (exists)
- **Goal**: Complete Catcode.v QED proofs
- **Deliverables**: SIMD table stub implementation
- **Timeline**: Weeks 2-3 per specification

### Secondary: Performance Infrastructure  
- **Week 4**: Chunk infra, xxHash scalar (p95 < 4ms target)
- **Week 5**: 🎯 Performance α gate (p95 < 2ms) - CRITICAL

## Implementation Priorities

### Immediate (Week 2)
1. Set up Catcode development environment
2. Create performance measurement harness 
3. Begin C extension research (required for 2ms target)
4. Maintain 0-admit status throughout

### Week 3-4 
1. Complete Catcode proofs
2. Implement chunk infrastructure
3. SIMD optimization implementation
4. Performance gate preparation

### Week 5 Gate Preparation
- Performance measurement automation
- C extension with AVX2 kernels
- Runtime feature detection
- 2ms target achievement verification

## Success Metrics
- [ ] Catcode module complete with 0 admits
- [ ] Performance measurement harness functional
- [ ] Path to <2ms clearly established
- [ ] Week 5 gate preparation complete

This roadmap addresses both timeline requirements AND the critical performance challenge for upcoming gates.