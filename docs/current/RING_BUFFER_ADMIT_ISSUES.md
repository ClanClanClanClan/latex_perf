# Ring Buffer Theory Admit Issues

## File: src/coq/lexer/RingBufferTheory.v

### Context
This file models an mmap ring-buffer for token storage in the v24-R3 incremental lexer. It has 2 admits that need proper proofs.

### Admit 1: `ring_buffer_visible_slice` (line ~171)
**Goal**: Prove that `length (concat doc) <= rb.(rb_capacity)`

**Challenge**: This requires proving that a ring buffer representation enforces capacity bounds. The proof needs to show:
1. The ring buffer write operation (`rb_write`) maintains the invariant that stored data never exceeds capacity
2. The `ring_buffer_rep` predicate ensures that represented documents fit within capacity
3. The `rb_slice` function correctly extracts data respecting buffer boundaries

**Current Issue**: Using `apply Nat.le_refl` tries to prove `n <= n`, but we need to prove that the document length is bounded by a different value (capacity).

**Suggested Approach**:
- Add a lemma showing that `pos_distance tail head size <= capacity` is maintained by all operations
- Add a lemma showing that `ring_buffer_rep` implies the document fits in the available space
- Use these lemmas to establish the capacity bound

### Admit 2: `ring_buffer_memory_efficiency` (line ~283)
**Goal**: Prove that `length (concat doc) >= rb.(rb_capacity) / 2`

**Challenge**: This is a performance characteristic, not a correctness property. It states that a well-utilized buffer should be at least 50% full.

**Issue**: This cannot be proven without assumptions about:
1. The workload (how much data is being buffered)
2. The usage pattern (steady state vs. startup)
3. The eviction policy behavior

**Recommendation**: 
- Either add explicit assumptions about buffer utilization
- Or remove this part of the theorem (keep only the first part about capacity <= size)
- Or change it to a weaker statement that can be proven

## Import Path Issue
The file has compilation issues due to incorrect import paths. The import:
```coq
Require Import lexer.v24r3.CoreLexer.
```

Should likely be adjusted based on the project's module structure.

## Technical Notes
- Both admits involve reasoning about list lengths and buffer capacities
- The ring buffer model uses sparse arrays (`nat -> option token`) which complicates proofs
- The `pos_distance` function handles wraparound, adding arithmetic complexity

## Priority
Medium - These are infrastructure proofs for the incremental lexer, not core v25 functionality.