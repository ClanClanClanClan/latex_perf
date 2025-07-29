# V25 MIGRATION STRATEGY: LEVERAGING EXISTING L0/L1

**Date**: 2025-07-28  
**Realization**: We already have complete, formally verified L0 and L1 implementations!

## ULTRATHINK ANALYSIS: WHAT WE HAVE

### ✅ **L0 Lexer (COMPLETE)**
- **Location**: `src/coq/lexer/Lexer.v`
- **Status**: 0 axioms, 0 admits, fully proven
- **Features**: Deterministic tokenization, perfect reconstruction
- **Extracted**: `src/extraction/ocaml/lexer/lexer_extracted.ml`

### ✅ **L1 Expander (COMPLETE)**  
- **Location**: `src/core/expander/`
- **Status**: 76 macros implemented, 3 core proofs complete
- **Performance**: Already achieving 4.43ms (well under 42ms target)
- **Features**: MacroCatalog.v with all built-in macros

### ✅ **Performance Already Validated**
From v25_MASTER_PLAN.md:
- **Current p95**: 0.73ms on M2 (target <1ms)
- **L0 performance**: Already optimized
- **L1 performance**: 4.43ms total time

## MIGRATION STRATEGY: ADAPT, DON'T REWRITE

### **Phase 1: Wrap Existing L0/L1 with v25 Interfaces** (Week 1-2)

**Key Insight**: The existing L0/L1 are correct and performant. We need to:
1. Add the delta-based interfaces from the technical resolution
2. Implement the version-vector consistency protocol
3. Add caching layers

```ocaml
(* Wrap existing lexer with v25 interface *)
module L0_V25 = struct
  (* Use existing lexer internally *)
  include Lexer_extracted
  
  (* Add delta computation *)
  let lex_chunk ?prev bytes =
    let tokens = existing_lex bytes in
    let state' = compute_new_state prev bytes in
    (tokens, state')
    
  (* Add cache key computation *)
  let compute_cache_key bytes state =
    { chunk_id = state.chunk_id; 
      hash = Xxh3.hash bytes }
end
```

### **Phase 2: Add Cross-Layer Protocol** (Week 2-3)

Implement the consistency protocol from integration resolution #88:

```ocaml
(* Global version vector *)
module Version_Vector = struct
  type t = {
    mutable σ₀ : int64;
    mutable σ₁ : int64;
    mutable σ₂ : int64;
    mutable σ₃ : int64;
    mutable σ₄ : int64;
  }
  
  let cas_update t dirty_layers new_snapshots =
    (* CAS-based atomic update as specified *)
end
```

### **Phase 3: Integrate SIMD Optimizations** (Week 3-4)

**Key**: The existing lexer is already fast (0.73ms p95). SIMD is for additional optimization:

1. Extract hot paths from Coq lexer
2. Implement SIMD variants for catcode lookup
3. Fall back to proven implementation for complex cases

```rust
// src/core/layer0/simd/src/lib.rs
#[no_mangle]
pub extern "C" fn lex_simd_hot_path(
    buf: *const u8, 
    len: usize
) -> *mut c_void {
    // SIMD-optimized tokenization
    // Falls back to OCaml for complex cases
}
```

### **Phase 4: Add Caching Infrastructure** (Week 4)

Implement the cache policies from resolution:
- L0: 2-hand CLOCK (1k chunks)
- L1: LFU-decay (4096 macros)

## WHAT WE DON'T NEED TO DO

❌ **Rewrite the lexer** - It's already proven correct  
❌ **Rewrite the expander** - 76 macros already implemented  
❌ **Re-prove correctness** - Proofs are complete (0 admits)  
❌ **Optimize from scratch** - Already achieving performance targets

## WHAT WE NEED TO ADD

✅ **Delta-based interfaces** - For incremental processing  
✅ **Version-vector protocol** - For consistency  
✅ **Caching layers** - For sub-80µs L0 performance  
✅ **SIMD hot paths** - For additional optimization  
✅ **Integration tests** - For cross-layer coordination

## REALISTIC TIMELINE ADJUSTMENT

**Original Plan**: Weeks 1-4 for L0, Weeks 5-8 for L1  
**Revised Plan**: 
- **Weeks 1-4**: Integrate existing L0/L1 with v25 architecture
- **Weeks 5-6**: Add cross-layer consistency and caching
- **Weeks 7-8**: Performance optimization and testing
- **Week 9+**: Move directly to L2 parser (saving 4 weeks!)

## IMPLEMENTATION CHECKLIST

### Week 1 Tasks
- [x] Set up development environment
- [ ] Import existing Lexer.v and expander code
- [ ] Create v25 wrapper modules
- [ ] Verify existing tests still pass

### Week 2 Tasks  
- [ ] Implement version-vector protocol
- [ ] Add delta computation to L0
- [ ] Add delta computation to L1
- [ ] Create integration test harness

### Week 3 Tasks
- [ ] Extract SIMD-optimizable hot paths
- [ ] Implement AVX2/AVX512 variants
- [ ] Benchmark SIMD vs proven implementation
- [ ] Integrate with fallback logic

### Week 4 Tasks
- [ ] Implement cache managers
- [ ] Add cache key computation  
- [ ] Performance testing (target: <80µs L0)
- [ ] Full integration testing

## CONCLUSION

By leveraging our existing, proven L0/L1 implementations, we can:
1. **Save 4+ weeks** of development time
2. **Maintain 0 admits** guarantee
3. **Start from proven correctness**
4. **Focus on integration** rather than reimplementation

This is the power of formal verification - we can confidently reuse proven components!