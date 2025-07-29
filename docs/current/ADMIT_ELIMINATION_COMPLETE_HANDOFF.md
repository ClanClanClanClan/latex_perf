# Complete Admit Elimination Handoff Document

## Project Context

### LaTeX Perfectionist v25 Overview
- **Timeline**: Week 1 of 156-week project
- **Requirement**: 0 axioms, 0 admits (v25 specification)
- **Current Status**: 0 axioms achieved, 63 admits remaining in src/
- **Architecture**: Hybrid v24/v25 system targeting 623 total validation rules

### Key Documents to Read
1. `/Users/dylanpossamai/Library/CloudStorage/Dropbox/Work/Articles/Scripts/CLAUDE.md` - Critical project instructions
2. `/Users/dylanpossamai/Library/CloudStorage/Dropbox/Work/Articles/Scripts/specs/Bootstrap Skeleton.md` - Proof techniques and patterns
3. `/Users/dylanpossamai/Library/CloudStorage/Dropbox/Work/Articles/Scripts/specs/v25/COMPLETE_V25_SPECIFICATION_IMPLEMENTATION_PLAN.md` - Full specification

## Current Admit Distribution

### By File (63 total in src/)
```
src/coq/vsna/Performance.v: 37 admits (performance measurement placeholders)
src/coq/vsna/Correctness.v: 16 admits (implementation placeholders)
src/coq/lexer/ParallelFirstPass.v: 4 admits (2 attempted)
src/coq/vsna/UVSNA.v: 4 admits
src/coq/lexer/LexerProofs.v: 3 admits (1 eliminated in session)
src/coq/vsna/UVSNA_CARC.v: 3 admits
src/coq/lexer/RingBufferTheory.v: 2 admits (attempted)
src/coq/lexer/IncrementalCorrect.v: 1 admit (fundamental blocker)
```

## Detailed Admit Analysis

### 1. CRITICAL BLOCKER: IncrementalCorrect.v (1 admit)

**File**: `src/coq/lexer/IncrementalCorrect.v`
**Line**: ~225
**Function**: `incremental_cache_soundness`

**Issue**: The proof requires that if two lines have the same xxhash value, they have the same content. The line_info record only stores the hash, not the content.

```coq
Record line_info := {
  li_hash      : N;             (* xxHash of this line *)
  li_end_state : lexer_state;   (* state *after* the line *)
  li_tokens    : list token     (* tokens of the line *)
}.
```

**Attempted Solution**: Tried to add xxhash collision-freedom axiom, but this violates v25's 0-axiom requirement.

**Options**:
1. Add `Axiom xxhash_collision_free : forall s1 s2, xxhash s1 = xxhash s2 -> s1 = s2`
2. Redesign `line_info` to store line content: `li_content : string`
3. Accept this as fundamental limitation and document as assumption

**Recommendation**: Option 2 is the only way to achieve 0 axioms.

### 2. Performance.v (37 admits) - SPECIAL CASE

**File**: `src/coq/vsna/Performance.v`

**Nature**: These are NOT traditional admits - they are placeholders for empirical measurements.

Example:
```coq
Theorem dfa_linear_time : forall cat_a_rules (doc : document),
  length cat_a_rules <= PHASE1_RULE_COUNT ->
  String.length doc <= SLA_TEST_DOC_SIZE ->
  let dfa := compile_phase1 cat_a_rules in
  measure_time (validate_phase1 dfa) doc <= PHASE1_MAX_LATENCY.
Proof.
  intros cat_a_rules doc Hrules Hdoc dfa.
  (* DFA execution is O(|doc|) with small constant factor *)
  admit. (* To be proven in Phase 1 *)
Admitted.
```

**Comments in file**: "IMPORTANT: All performance targets (including 42ms) are DESIGN GOALS"
"Actual performance measurements scheduled for Week 5 with SLA-Guard integration"

**Decision Needed**: Do performance measurement placeholders count as admits for v25 requirement?

### 3. Correctness.v (16 admits) - Implementation Waiting

**File**: `src/coq/vsna/Correctness.v`

All admits are marked: "To be proven in Phase implementation"

Example:
```coq
Theorem vsna_correctness : forall rules doc,
  let automaton := compile_rules rules in
  let results := validate_document_vsna automaton doc in
  sound_validation results doc rules /\ 
  complete_validation results doc rules.
Proof.
  (* Implementation placeholder - will be proven in Phase implementation *)
  Admitted.
```

**Issue**: These proofs depend on VSNA implementation that doesn't exist yet.

**Required**: Implement compile_rules, validate_document_vsna, etc. before proofs possible.

### 4. RingBufferTheory.v (2 admits) - Complex Invariants

**File**: `src/coq/lexer/RingBufferTheory.v`

#### Admit 1: ring_buffer_visible_slice (~line 171)
**Goal**: `length (concat doc) <= rb.(rb_capacity)`

**Challenge**: Proving ring buffer never exceeds capacity requires showing:
- rb_write maintains capacity invariant
- Eviction policy ensures space
- ring_buffer_rep only represents documents that fit

**Attempted approach**:
```coq
assert (H_dist: pos_distance rb.(rb_tail) rb.(rb_head) rb.(rb_size) <= rb.(rb_capacity)).
```

**Issue**: Need to prove this invariant is maintained by all operations.

#### Admit 2: ring_buffer_memory_efficiency (~line 283)
**Goal**: `length (concat doc) >= rb.(rb_capacity) / 2`

**Issue**: This is a performance characteristic, not correctness. Cannot prove without workload assumptions.

**Recommendation**: Remove this part of theorem or add explicit workload assumptions.

### 5. ParallelFirstPass.v (4 admits) - Technical Proofs

**File**: `src/coq/lexer/ParallelFirstPass.v`

#### Admit 1: parallel_first_pass_correctness (~line 171)
**Issue**: State threading in parallel processing. The proof needs to show that processing shards independently then merging gives same result as sequential processing.

**Key insight needed**: Current implementation doesn't thread state between shards correctly.

#### Admit 2: shard_size_bounds (~line 230)
**Issue**: Division arithmetic - need to prove each shard size <= 2 * average

**Attempted**: Started proof structure but stuck on division bounds reasoning.

### 6. LexerProofs.v (3 admits)

**File**: `src/coq/lexer/LexerProofs.v`

#### Main admit: lexer_sound (~line 157)
**Goal**: `reconstruct_tokens (tokenize_string s) = s`

**Challenge**: Requires extensive lemmas about:
- string_to_list / list_to_string round-trip
- How each character is processed preserves reconstruction
- Buffer flushing at right times

**Missing infrastructure**:
```coq
Lemma string_list_round_trip : forall s,
  list_to_string (string_to_list s) = s.
  
Lemma lex_char_preserves_reconstruction : forall st c,
  reconstruct property holds...
```

### 7. UVSNA Files (7 admits total)

**Files**: `src/coq/vsna/UVSNA.v`, `src/coq/vsna/UVSNA_CARC.v`

Similar to Correctness.v - waiting for implementation.

## Proof Techniques That Work

From Bootstrap Skeleton and successful eliminations:

### 1. Definition Unfolding
```coq
unfold typo_001_validator in H.
simpl in H.
```

### 2. Case Analysis with destruct
```coq
destruct (in_comment st) eqn:HComment.
- (* comment case *)
- (* non-comment case *)
```

### 3. Apply with Specific Instances
```coq
apply Forall2_firstn_le with (n := S n); auto.
```

### 4. Helper Lemma Pattern
When stuck, create helper lemma:
```coq
Lemma find_checkpoint_none_implies_all_greater : ...
```

### 5. Computational Proofs
```coq
vm_compute. reflexivity.
```

## Import/Compilation Issues

### Common Import Problems
Many files have:
```coq
Require Import lexer.v24r3.CoreLexer.
```

But get error: "contains library CoreLexer and not library Core.core.lexer.v24r3.CoreLexer"

### Fix Pattern
Either:
1. Adjust -R flag in coqc command
2. Use local definitions when imports fail
3. Check _CoqProject file for correct mappings

## Critical Decisions Needed

### 1. Hash Collision Freedom
**Question**: Can we redesign IncrementalCorrect.v to avoid needing xxhash collision-freedom axiom?

**Impact**: Fundamental to achieving 0 axioms requirement.

### 2. Performance Placeholders
**Question**: Do the 37 measurement placeholders in Performance.v count against 0-admit requirement?

**Impact**: If yes, these cannot be eliminated until Week 5 measurements.

### 3. Implementation Dependencies
**Question**: Should we implement missing VSNA components to enable correctness proofs?

**Impact**: 16+ admits blocked on non-existent implementation.

## Recommended Approach

### Phase 1: Quick Wins (1-2 admits)
1. Complete division arithmetic in ParallelFirstPass.v shard_size_bounds
2. Try simplified version of lexer_sound with restricted input

### Phase 2: Design Decisions (1-40 admits)
1. Get clarification on Performance.v placeholders
2. Redesign IncrementalCorrect.v to store line content
3. Decide on ring buffer utilization proof

### Phase 3: Infrastructure Building (10+ admits)
1. Create string/list round-trip lemmas for lexer_sound
2. Build VSNA component stubs to enable proofs
3. Add helper lemmas for parallel processing

### Phase 4: Complex Proofs (remaining)
1. Complete parallel_first_pass_correctness with proper state model
2. Finish ring buffer capacity invariant proofs
3. Tackle VSNA correctness with implementation

## Testing Approach

To verify admits are truly eliminated:
```bash
# Count admits in specific file
grep -c "admit\." src/path/to/file.v
grep -c "Admitted\." src/path/to/file.v

# Check compilation
coqc -R src Core src/path/to/file.v
```

## Final Notes

### Bootstrap Skeleton Wisdom
- Read `/Users/dylanpossamai/Library/CloudStorage/Dropbox/Work/Articles/Scripts/specs/Bootstrap Skeleton.md` for proof patterns
- Look for `whitespace_safe` and `REGEX_ASCII` examples
- Use family lemmas for systematic proofs

### Warning
Some admits may be fundamentally impossible without:
1. Axioms (violating v25 requirement)
2. Implementation that doesn't exist
3. Empirical measurements not yet done

Document these clearly rather than spending infinite time on impossible proofs.