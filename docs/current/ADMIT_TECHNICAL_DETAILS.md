# Technical Details for Admit Elimination

## Code Structure and Dependencies

### Module Hierarchy
```
src/
├── coq/
│   ├── lexer/           # Incremental lexer theory
│   │   ├── CoreLexer.v  # ✓ DONE (0 axioms)
│   │   ├── CheckpointTheory.v # ✓ DONE (0 admits)
│   │   ├── ErrorRecovery.v # ✓ DONE (0 admits)
│   │   ├── IncrementalCorrect.v # 1 admit (BLOCKER)
│   │   ├── LexerProofs.v # 3 admits
│   │   ├── ParallelFirstPass.v # 4 admits
│   │   └── RingBufferTheory.v # 2 admits
│   └── vsna/            # VSNA validation architecture
│       ├── Core.v       # Type definitions
│       ├── Correctness.v # 16 admits (waiting for impl)
│       ├── Performance.v # 37 admits (measurements)
│       ├── UVSNA.v      # 4 admits
│       └── UVSNA_CARC.v # 3 admits
└── core/
    ├── lexer/v24r3/     # Has CoreLexer.v that others import
    └── expander/        # ✓ All DONE (0 admits)
```

### Import Fix Pattern
When you see: "The file .../CoreLexer.vo contains library CoreLexer and not library Core.core.lexer.v24r3.CoreLexer"

Try:
```bash
coqc -R src/core/lexer/v24r3 "" src/coq/lexer/RingBufferTheory.v
```

Or modify imports to use direct paths.

## Detailed Admit Specifications

### 1. IncrementalCorrect.v - THE FUNDAMENTAL BLOCKER

**Exact Location**: Line 225, in proof of `incremental_cache_soundness`

**The Admit**:
```coq
assert (Hfirst: Forall2 (fun li ln => li_hash li = xxhash ln) [l] [a]).
{
  apply Forall2_firstn_le with (n := S n); auto.
  lia.
}
inversion Hfirst; subst.
(* We need to prove that li_tokens l = fst (lex_bytes init_state (list_of_string a ++ [byte_of_nat 10]))
   given that li_hash l = xxhash a.
   
   The fundamental issue: we only have the hash equality, not content equality.
   Without additional information (either storing line content or assuming hash collision-freedom),
   this cannot be proven.
   
   Options:
   1. Change line_info to store line content
   2. Add hash collision-freedom as an axiom
   3. Accept this as a fundamental limitation
   
   For now, we must admit this. *)
admit. (* Requires hash collision-freedom or design change *)
```

**Root Cause**: The `line_info` record stores only the hash of a line, not its content. To prove that cached tokens are correct, we need to know the lines are identical, but we only know their hashes are equal.

**Solution Required**:
```coq
(* Change this: *)
Record line_info := {
  li_hash      : N;
  li_end_state : lexer_state;
  li_tokens    : list token
}.

(* To this: *)
Record line_info := {
  li_hash      : N;
  li_content   : string;        (* ADD THIS *)
  li_end_state : lexer_state;
  li_tokens    : list token
}.
```

Then modify the proof to use `li_content` equality.

### 2. LexerProofs.v - lexer_sound (Most Complex Single Proof)

**Location**: Line 146-157

**The Theorem**:
```coq
Theorem lexer_sound : forall s : string,
  reconstruct_tokens (tokenize_string s) = s.
```

**Why It's Hard**: 
- `tokenize_string` converts string → list ascii → processes each → list token
- `reconstruct_tokens` must perfectly reverse this
- Need to track how state changes affect token boundaries

**Required Lemmas**:
```coq
(* 1. String/list conversion *)
Lemma string_to_list_to_string : forall s,
  fold_left (fun acc c => acc ++ String c "") (string_to_list s) "" = s.

(* 2. Tokenization preserves content *)
Lemma tokenize_aux_sound : forall chars st acc,
  reconstruct_tokens acc ++ 
  fold_left (fun a c => a ++ String c "") chars "" =
  reconstruct_tokens (tokenize_string_aux chars st acc).

(* 3. State transitions preserve soundness *)
Lemma lex_char_reconstruction : forall st c tokens st',
  lex_char st c = (st', tokens) ->
  reconstruct_tokens tokens = String c "" ∨ 
  (∃ pending, buffer st' = pending ++ String c "").
```

### 3. ParallelFirstPass.v - parallel_first_pass_correctness

**Location**: Line 140-173

**The Core Issue**:
```coq
(* Current incorrect approach: *)
let process_shard shard := lex_bytes init_state shard in
let results := map process_shard shards in

(* What's needed: *)
let process_shard (prev_state, shard) := 
  let (tokens, next_state) := lex_bytes prev_state shard in
  (next_state, tokens) in
let results := fold_left process_shard shards (init_state, []) in
```

The parallel processing doesn't thread lexer state between shards, so it can't be equivalent to sequential processing.

**Fix Approach**: Either:
1. Prove a weaker property (each shard processed correctly in isolation)
2. Redesign to thread state sequentially (not truly parallel)
3. Prove shards are independent (requires lexer properties)

### 4. RingBufferTheory.v - Capacity Bound

**Location**: Line 144-171

**What to Prove**: `length (concat doc) <= rb.(rb_capacity)`

**Key Invariant Needed**:
```coq
Definition ring_buffer_invariant (rb : ring_buffer) : Prop :=
  (* Distance between tail and head represents valid content *)
  let content_size := pos_distance rb.(rb_tail) rb.(rb_head) rb.(rb_size) in
  content_size <= rb.(rb_capacity) ∧
  (* All stored tokens fit in this space *)
  ∀ pos, rb.(rb_data) pos <> None -> 
    pos_in_range rb.(rb_tail) pos rb.(rb_head) rb.(rb_size).
```

**Then Prove**:
```coq
Lemma rb_write_maintains_invariant : ∀ rb tok,
  ring_buffer_invariant rb ->
  ring_buffer_invariant (rb_write rb tok).

Lemma ring_buffer_rep_respects_capacity : ∀ rb head tail doc,
  ring_buffer_invariant rb ->
  ring_buffer_rep rb head tail doc ->
  length (concat doc) <= rb.(rb_capacity).
```

### 5. Performance.v - Special Handling Needed

**All 37 admits follow this pattern**:
```coq
Theorem some_performance_bound : 
  ... measure_time ... <= SOME_TARGET.
Proof.
  admit. (* To be proven in Phase X *)
Admitted.
```

**File Header States**:
```coq
(* IMPORTANT: All performance targets (including 42ms) are DESIGN GOALS *)
(* Actual performance measurements scheduled for Week 5 with SLA-Guard integration *)
(* These theorems specify TARGET performance, not measured achievements *)
```

**Critical Question for User**: Should these be:
1. Left as admits until Week 5 measurements?
2. Changed to axioms about performance targets?
3. Removed entirely until measurements available?
4. Changed to weaker "exists a bound" statements?

## Systematic Approaches

### For Technical Admits (Division, Arithmetic)
```coq
(* Use lia when possible *)
lia.

(* When lia fails, try omega (deprecated but sometimes works) *)
omega.

(* Manual arithmetic *)
assert (H: n / k <= n) by apply Nat.div_le_upper_bound.
```

### For Structural Admits (Induction)
```coq
(* Strong induction often needed *)
induction n as [|n IH] using strong_induction.

(* Well-founded induction for complex recursion *)
induction x using (well_founded_induction lt_wf).
```

### For Impossible Admits
Document clearly:
```coq
(* FUNDAMENTAL LIMITATION: This requires hash collision freedom
   which would violate v25's 0-axiom requirement.
   
   Alternatives:
   1. Redesign to store content
   2. Accept as engineering assumption
   3. Use different caching strategy *)
admit. (* CANNOT BE PROVEN without axioms *)
```

## Testing Your Progress

### Quick Verification Script
```bash
#!/bin/bash
# Save as check_admits.sh

echo "=== Admit Count by File ==="
find src/ -name "*.v" -exec sh -c '
  count=$(grep -c "admit\.\|Admitted\." "$1" 2>/dev/null || echo 0)
  if [ "$count" -gt 0 ]; then 
    echo "$1: $count"
  fi
' _ {} \; | sort -t: -k2 -nr

echo -e "\n=== Total Admits ==="
find src/ -name "*.v" -exec grep -h "admit\.\|Admitted\." {} \; | wc -l
```

### Compilation Test
```bash
# Test single file
coqc -R src Core -R src/core/lexer/v24r3 "" src/coq/lexer/LexerProofs.v

# Test all
dune build @coq
```

## Priority Recommendation

### Week 1 Achievable Goals
1. **Fix IncrementalCorrect.v** by redesigning line_info (1 admit)
2. **Complete ParallelFirstPass.v** shard_size_bounds (1 admit)
3. **Document Performance.v** decision needed (37 admits)

### Week 2-3 Goals  
1. Build infrastructure for **lexer_sound** proof
2. Complete **RingBufferTheory.v** with invariants
3. Design stubs for **VSNA Correctness.v**

### Blocked Until Decision
- All Performance.v admits (need measurement vs. proof decision)
- Some VSNA admits (need implementation)

## Final Wisdom

From Bootstrap Skeleton patterns that work:
```coq
(* Pattern 1: Unfold and compute *)
unfold definition. vm_compute. reflexivity.

(* Pattern 2: Case split everything *)
destruct x; destruct y; destruct z; try discriminate; auto.

(* Pattern 3: Helper lemmas for each case *)
assert (Hcase1: P x) by (unfold P; destruct x; auto).
```

Remember: Some admits indicate design issues, not proof difficulty. Recognize the difference.