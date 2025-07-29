# Admit Elimination Workflow Guide

## Initial Setup

### 1. Check Current Status
```bash
# Get exact count of remaining admits
find src/ -name "*.v" -exec grep -c "admit\.\|Admitted\." {} + | awk '{sum += $1} END {print "Total admits:", sum}'

# List files with admits
find src/ -name "*.v" -exec grep -l "admit\.\|Admitted\." {} \; | sort
```

### 2. Read Critical Documents
```bash
# In this order:
cat /Users/dylanpossamai/Library/CloudStorage/Dropbox/Work/Articles/Scripts/CLAUDE.md
cat /Users/dylanpossamai/Library/CloudStorage/Dropbox/Work/Articles/Scripts/docs/current/CRITICAL_DECISIONS_NEEDED.md
cat /Users/dylanpossamai/Library/CloudStorage/Dropbox/Work/Articles/Scripts/docs/current/ADMIT_TECHNICAL_DETAILS.md
```

### 3. Understand Bootstrap Skeleton Patterns
```bash
# Search for proof patterns that work
grep -A5 -B5 "Proof\." /Users/dylanpossamai/Library/CloudStorage/Dropbox/Work/Articles/Scripts/specs/Bootstrap\ Skeleton.md
```

## Workflow for Each Admit

### Step 1: Locate and Understand
```bash
# Find exact location
grep -n "admit\." src/path/to/file.v

# Read context
cat src/path/to/file.v | sed -n 'START,ENDp'  # Replace START,END with line range
```

### Step 2: Check Dependencies
```coq
(* In Coq, check what's available *)
Print SYMBOL_NAME.
Check FUNCTION_NAME.
Search "lemma_pattern".
```

### Step 3: Try Standard Patterns

#### Pattern A: Computational Proof
```coq
unfold definition1, definition2.
simpl.
vm_compute.
reflexivity.
```

#### Pattern B: Case Analysis
```coq
destruct x eqn:Hx.
- (* case 1 *) ...
- (* case 2 *) ...
```

#### Pattern C: Arithmetic
```coq
lia.  (* Tries linear integer arithmetic *)
```

#### Pattern D: Helper Lemma
```coq
assert (Hhelper: PROPERTY).
{ (* prove helper *) }
(* use helper in main proof *)
```

### Step 4: Test Your Solution
```bash
# Compile single file
coqc -R src Core src/path/to/file.v

# If import errors, try:
coqc -R src/core/lexer/v24r3 "" -R src Core src/path/to/file.v
```

## Specific File Strategies

### For IncrementalCorrect.v
1. First check user decision on hash collision
2. If redesign approved:
```coq
(* Modify line_info to include content *)
Record line_info := {
  li_hash : N;
  li_content : string;  (* ADD THIS *)
  li_tokens : list token;
  li_end_state : lexer_state
}.
```

### For Performance.v  
1. Check user decision on measurement placeholders
2. If weakening to existence approved:
```coq
(* Change from: *)
measure_time f x <= SPECIFIC_BOUND
(* To: *)
exists bound, measure_time f x <= bound
```

### For LexerProofs.v (lexer_sound)
1. Build helper lemmas first:
```coq
(* Start with string/list conversion *)
Lemma string_to_list_inv : forall s,
  fold_left (fun acc c => acc ++ String c "") (string_to_list s) "" = s.
Proof.
  induction s.
  - reflexivity.
  - simpl. f_equal. apply IHs.
Qed.
```

### For RingBufferTheory.v
1. Define missing invariant:
```coq
Definition ring_buffer_invariant (rb : ring_buffer) : Prop :=
  pos_distance rb.(rb_tail) rb.(rb_head) rb.(rb_size) <= rb.(rb_capacity).
```

2. Prove it's maintained:
```coq
Lemma rb_write_maintains_invariant : forall rb tok,
  ring_buffer_invariant rb ->
  ring_buffer_invariant (rb_write rb tok).
```

### For Correctness.v and VSNA files
If implementation stubs approved:
```coq
(* Create minimal implementations *)
Definition compile_rules (rules : list rule) : vsna_automaton :=
  mk_vsna_automaton dummy_dfa dummy_vpa dummy_symbol_table.

Definition validate_document_vsna (a : vsna_automaton) (doc : document) : validation_result :=
  []. (* Empty results for now *)
```

## Progress Tracking

### Use TodoWrite Tool
```
1. Update completed admits count
2. Mark specific theorems as complete
3. Note any new blockers discovered
```

### Document Blockers
For each unsuccessful attempt:
```coq
(* BLOCKED: This proof requires [specific missing piece]
   Attempted: [what you tried]
   Issue: [why it failed]
   Needs: [what would unblock it] *)
admit. (* BLOCKED - see above *)
```

## Common Pitfalls

### 1. Import Errors
```
Error: The file X.vo contains library X and not library path.to.X
Fix: Adjust -R flags or use direct paths
```

### 2. Missing Lemmas
```
Error: The reference Y was not found
Fix: Search for similar lemmas or create your own
```

### 3. Proof Script Breaks
```coq
(* If proof script has errors, try: *)
Proof.
  (* Remove everything and start fresh *)
  (* Build incrementally, checking each step *)
Admitted.
```

## Final Checklist

Before marking an admit as "impossible":

- [ ] Did you try vm_compute?
- [ ] Did you try breaking into helper lemmas?
- [ ] Did you check Bootstrap Skeleton for patterns?
- [ ] Did you verify all definitions are unfolded?
- [ ] Did you document exactly what's missing?
- [ ] Is this truly unprovable or just hard?

## Quick Reference

### Most Useful Tactics
```coq
reflexivity.      (* When both sides identical *)
lia.             (* Linear integer arithmetic *)
discriminate.    (* When constructors differ *)
injection H.     (* Extract from constructor equality *)
induction x.     (* Structural induction *)
destruct x eqn:Hx. (* Case analysis *)
unfold def.      (* Expand definition *)
simpl.           (* Simplify *)
vm_compute.      (* Full computation *)
auto.            (* Try simple things *)
```

### When Stuck
1. Check Bootstrap Skeleton for similar proofs
2. Print the goal clearly: `idtac "Goal:"; idtac goal.`
3. Look for simpler lemmas to prove first
4. Ask: "What would make this obvious?"
5. Document why it's hard for the next person