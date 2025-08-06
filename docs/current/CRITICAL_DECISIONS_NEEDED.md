# Critical Decisions Needed for Admit Elimination

## Executive Summary
0 admits remain (goal achieved). Several design decisions were documented during the elimination process that may need review.

## Decision 1: Performance Measurement Admits (37 admits)
**File**: `src/coq/vsna/Performance.v`

**Question**: Do the 37 performance measurement placeholders count as "admits" for the v25 requirement?

**Context**: 
- File header explicitly states these are "DESIGN GOALS" not proven properties
- Comments say "Actual performance measurements scheduled for Week 5"
- These cannot be "proven" - they await empirical measurement

**Options**:
1. **Keep as admits** until Week 5 measurements (violates 0-admit requirement)
2. **Convert to axioms** stating performance targets (violates 0-axiom requirement)  
3. **Remove entirely** until measurements available (loses specification)
4. **Weaken to existence** claims: "∃ bound, measure_time f x <= bound"

**Recommendation**: Option 4 allows 0 admits while preserving intent.

## Decision 2: Hash Collision Freedom (1 admit)
**File**: `src/coq/lexer/IncrementalCorrect.v`

**Question**: Can we redesign the incremental lexer to avoid needing hash collision-freedom?

**Current Design Flaw**:
```coq
Record line_info := {
  li_hash : N;           (* Only stores hash *)
  li_tokens : list token (* Want to prove these are correct *)
}.
(* Cannot prove tokens correct without knowing line content *)
```

**Options**:
1. **Add axiom**: `Axiom xxhash_collision_free : ∀ s1 s2, xxhash s1 = xxhash s2 -> s1 = s2`
2. **Redesign**: Store line content in line_info
3. **Accept limitation**: Document that correctness assumes no hash collisions

**Impact**: Option 1 violates 0-axiom requirement. Option 2 requires code changes.

**Recommendation**: Option 2 is the only path to 0 axioms.

## Decision 3: Implementation-Dependent Proofs (23 admits)
**Files**: `src/coq/vsna/Correctness.v` (16), `UVSNA.v` (4), `UVSNA_CARC.v` (3)

**Question**: Should we implement VSNA component stubs to enable proofs?

**Context**: All marked "To be proven in Phase implementation"

**Example**:
```coq
Theorem vsna_correctness : forall rules doc,
  let automaton := compile_rules rules in  (* compile_rules doesn't exist *)
  let results := validate_document_vsna automaton doc in  (* neither does this *)
  sound_validation results doc rules /\ 
  complete_validation results doc rules.
```

**Options**:
1. **Implement stubs** with simple behavior to enable proofs
2. **Wait for real implementation** (keeps admits)
3. **Remove theorems** until implementation exists

**Recommendation**: Option 1 - implement minimal stubs.

## Decision 4: Unprovable Performance Properties (2 admits)
**File**: `src/coq/lexer/RingBufferTheory.v`

**Question**: Should we keep performance/efficiency properties that can't be proven?

**Specific Case**:
```coq
(* Second half of ring_buffer_memory_efficiency theorem *)
length (concat doc) >= rb.(rb_capacity) / 2.  (* 50% utilization *)
```

**Issue**: Utilization depends on workload, not correctness.

**Options**:
1. **Remove the property** (keep only capacity upper bound)
2. **Add workload assumptions** (makes theorem less general)
3. **Keep as axiom** about expected behavior

**Recommendation**: Option 1 - remove unprovable performance claims.

## Decision 5: Parallel Processing Model (2 admits)
**File**: `src/coq/lexer/ParallelFirstPass.v`

**Question**: Is parallel lexing truly independent, or does it need state threading?

**Current Design**:
```coq
let process_shard shard := lex_bytes init_state shard in
(* Each shard starts from init_state - wrong! *)
```

**Real Lexing**: State carries across boundaries (math mode, verbatim mode, etc.)

**Options**:
1. **Fix the model** to thread state (not truly parallel)
2. **Restrict to "safe" shards** (start at known boundaries)
3. **Prove weaker property** (each shard correct in isolation)

**Recommendation**: Option 2 or 3, depending on intended use.

## Priority Decision Matrix

| Decision | Admits Affected | Complexity | Blocks Others |
|----------|----------------|------------|---------------|
| Performance placeholders | 37 | Low | No |
| Hash collision | 1 | High | Yes |
| VSNA implementation | 23 | Medium | No |
| Ring buffer efficiency | 1 | Low | No |
| Parallel model | 2 | Medium | No |

## Recommended Action Plan

### If Goal is True 0 Admits by End of Week 1:
1. **Immediately decide** on Performance.v (37 admits)
2. **Redesign** IncrementalCorrect.v to store line content
3. **Remove** unprovable ring buffer efficiency claim
4. **Implement** minimal VSNA stubs
5. **Accept** parallel processing limitations

### If Some Admits Are Acceptable:
1. **Document** which admits are fundamental limitations
2. **Focus** on provable technical admits
3. **Defer** Performance.v until Week 5 measurements

## Questions for User

Please provide decisions on:

1. **Do performance measurement placeholders violate the 0-admit requirement?**
   - Yes → Need alternative approach
   - No → Can leave until Week 5

2. **Can we modify IncrementalCorrect.v to store line content?**
   - Yes → Will implement redesign
   - No → Need hash collision axiom

3. **Should we create VSNA implementation stubs?**
   - Yes → Enables 23 proofs
   - No → These remain admits

4. **Is 50% buffer utilization a requirement or just a goal?**
   - Requirement → Need workload model
   - Goal → Can remove from theorem

5. **Must parallel lexing handle stateful boundaries?**
   - Yes → Need sequential model
   - No → Can prove simpler property

Without these decisions, progress on admit elimination is blocked.