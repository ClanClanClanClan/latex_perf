# 🏗️ Checkpoint Architecture
## Core Algorithm Design

### Overview

The checkpoint-based incremental lexer achieves dramatic performance improvements by saving lexer state at line boundaries and resuming from these checkpoints when edits occur.

---

## Core Concepts

### 1. Checkpointing

**Definition**: A checkpoint is a saved lexer state at a specific position (typically end of line).

```coq
Record checkpoint := {
  cp_offset : nat;      (* Byte offset in document *)
  cp_line : nat;        (* Line number *)
  cp_state : lexer_state (* Complete lexer state *)
}.
```

**Key Properties**:
- Checkpoints are immutable once created
- State includes all context (math mode, comments, etc.)
- Stored at natural boundaries (line ends)

### 2. Early Termination

**The Key Optimization**: Stop processing when both:
1. Line content hasn't changed (hash match)
2. Incoming lexer state matches previous run

```python
if hash(line) == old_hash[line] and state == old_state[line-1]:
    break  # Everything downstream is guaranteed identical
```

### 3. State Management

**Per-Line Storage**:
- Line content hash (64-bit xxh3)
- End-of-line lexer state
- Cached tokens (optional, LRU)

---

## Algorithm Details

### Change Detection

```python
def detect_changes(old_doc, new_doc, edit):
    # Fast path: localized edit
    if edit.is_localized():
        return range(edit.start_line, edit.end_line + 1)
    
    # Full diff for complex changes
    changed = []
    for i, (old, new) in enumerate(zip(old_doc.lines, new_doc.lines)):
        if hash(old) != hash(new):
            changed.append(i)
    return changed
```

### Incremental Processing

```python
def incremental_tokenize(document, edit):
    # 1. Detect what changed
    changed_lines = detect_changes(document, edit)
    if not changed_lines:
        return  # Nothing to do
    
    # 2. Find resumption point
    start_line = min(changed_lines)
    checkpoint = get_checkpoint(start_line - 1) or initial_state
    
    # 3. Process forward with early termination
    current_state = checkpoint
    for line_num in range(start_line, document.line_count):
        line_content = document.lines[line_num]
        line_hash = xxh3_hash(line_content)
        
        # Early termination check
        old_hash = hash_table.get(line_num)
        old_state = state_table.get(line_num - 1)
        
        if line_hash == old_hash and states_equal(current_state, old_state):
            # State convergence - downstream identical
            break
        
        # Process line
        tokens, new_state = lex_line(current_state, line_content)
        
        # Update tables
        hash_table[line_num] = line_hash
        state_table[line_num] = new_state
        token_cache[line_num] = tokens
        
        current_state = new_state
```

### State Comparison

```python
def states_equal(s1, s2):
    """Compare lexer states for early termination"""
    return (s1.math_mode == s2.math_mode and
            s1.in_comment == s2.in_comment and
            s1.buffer == s2.buffer and
            s1.context_stack == s2.context_stack)
```

---

## Data Structures

### Line Hash Table
```
LineNum -> Hash (64-bit)
-------------------
0       -> 0x1234...
1       -> 0x5678...
2       -> 0x9abc...
...
```

### State Checkpoint Table
```
LineNum -> LexerState
-------------------
0       -> {math_mode: false, in_comment: false, ...}
1       -> {math_mode: true, in_comment: false, ...}
2       -> {math_mode: true, in_comment: false, ...}
...
```

### Token Cache (LRU)
```
(LineNum, Hash) -> TokenList
----------------------------
(0, 0x1234...) -> [TEXT("Hello"), SPACE, ...]
(1, 0x5678...) -> [MATH_START, TEXT("x^2"), ...]
...
```

---

## Performance Characteristics

### Time Complexity

| Operation | Complexity | Typical Case |
|-----------|------------|--------------|
| Single edit | O(k) | k ≈ 1-10 lines |
| Find checkpoint | O(1) | Hash lookup |
| State comparison | O(1) | Fixed fields |
| Cache lookup | O(1) | LRU average |

### Space Complexity

| Structure | Per Line | 100k lines |
|-----------|----------|------------|
| Hash table | 8 bytes | 800 KB |
| State table | ~32 bytes | 3.2 MB |
| Token cache | Variable | ~30 MB (bounded) |
| **Total** | ~48 bytes | ~34 MB |

---

## Why It Works

### 1. Locality of Reference
- Most edits are localized (typing, small changes)
- Early termination typically triggers within 10-20 lines
- Cache hit rate >95% for interactive editing

### 2. Deterministic Lexing
- Same state + same input = same output
- State comparison guarantees downstream equivalence
- No need to process unchanged suffix

### 3. Natural Boundaries
- Lines are natural units in text editing
- LaTeX commands rarely span many lines
- State changes often align with line boundaries

---

## Edge Cases

### Multi-Line Constructs
```latex
\begin{align}
  x &= y \\    % State carries across
  z &= w       % Must track align environment
\end{align}
```

**Solution**: State includes environment stack

### Long Comments
```latex
Start of paragraph % This comment affects
                  % multiple lines that
                  % need reprocessing
Next paragraph starts here
```

**Solution**: Comment state in checkpoint triggers reprocessing

### Verbatim Blocks
```latex
\begin{verbatim}
% Not a comment
$ Not math $
\end{verbatim}
```

**Solution**: Verbatim mode in state disables normal processing

---

## Implementation Notes

### Memory Efficiency
- States are immutable (share common structure)
- Hash table uses primitive arrays
- Token cache has hard memory limit

### Cache Invalidation
- Line edits invalidate single cache entry
- Multi-line edits invalidate range
- Memory pressure triggers LRU eviction

### Error Recovery
- Missing checkpoint: reprocess from start
- State corruption: clear and rebuild
- Hash collision: fall back to full comparison

---

## Future Optimizations

### 1. Hierarchical Checkpoints
- Paragraph-level checkpoints
- Section-level checkpoints
- Faster resumption for large jumps

### 2. Parallel Processing
- Process independent sections concurrently
- Merge results at synchronization points

### 3. Incremental Hashing
- Rolling hash for insertions/deletions
- Avoid full line rehashing

---

**The checkpoint architecture transforms O(n) batch processing into O(k) incremental processing, where k << n for typical edits.**