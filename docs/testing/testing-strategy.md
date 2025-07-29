# 🧪 Testing Strategy
## Comprehensive Validation Plan

### Overview

The testing strategy ensures both **mathematical correctness** and **real-time performance** through multiple layers of validation, from formal proofs to production monitoring.

---

## Testing Pyramid

```
                 ┌─────────────────┐
                 │   E2E Tests     │ ← Full system validation
                 └────────┬────────┘
              ┌───────────┴───────────┐
              │  Integration Tests    │ ← Component interaction
              └───────────┬───────────┘
          ┌───────────────┴───────────────┐
          │     Performance Tests         │ ← Speed & memory
          └───────────────┬───────────────┘
      ┌───────────────────┴───────────────────┐
      │           Unit Tests                  │ ← Individual functions
      └───────────────────┬───────────────────┘
  ┌───────────────────────┴───────────────────────┐
  │         Equivalence Testing (Fuzzing)         │ ← Mathematical validation
  └───────────────────────┬───────────────────────┘
┌─────────────────────────┴─────────────────────────┐
│           Formal Verification (Coq)               │ ← Proof foundation
└───────────────────────────────────────────────────┘
```

---

## Layer 1: Formal Verification

### What We Test
- Mathematical correctness of algorithms
- Proof completeness (no admits)
- Theorem dependencies

### How We Test
```bash
# Automated proof checking
#!/bin/bash
cd src/coq/lexer
make clean && make
ADMITS=$(grep -r "admit\|Admitted" *.v)
if [ -n "$ADMITS" ]; then
    echo "FAIL: Unproven admits found"
    exit 1
fi
```

### Key Verifications
- [ ] `incremental_correctness` theorem compiles
- [ ] `checkpoint_equivalence` proven
- [ ] `codec_roundtrip` verified
- [ ] No axioms beyond hash assumption

---

## Layer 2: Equivalence Testing (Fuzzing)

### What We Test
Mathematical equivalence: `incremental(doc, edits) = batch(apply(doc, edits))`

### Implementation

```python
class EquivalenceFuzzer:
    def fuzz_single_edit(self):
        doc = self.generate_random_latex()
        edit = self.generate_random_edit()
        
        # Apply edit
        new_doc = apply_edit(doc, edit)
        
        # Compare methods
        batch_tokens = batch_tokenize(new_doc)
        incr_tokens = incremental_tokenize(doc, edit)
        
        assert tokens_equal(batch_tokens, incr_tokens)
    
    def fuzz_multi_edit_sequence(self):
        doc = self.generate_random_latex()
        edits = [self.generate_random_edit() for _ in range(100)]
        
        # Apply all edits
        final_doc = doc
        for edit in edits:
            final_doc = apply_edit(final_doc, edit)
            
        # Compare final results
        batch_tokens = batch_tokenize(final_doc)
        
        # Incremental processing
        lexer = IncrementalLexer()
        lexer.load_document(doc)
        for edit in edits:
            lexer.apply_edit(edit)
        incr_tokens = lexer.get_all_tokens()
        
        assert tokens_equal(batch_tokens, incr_tokens)
```

### Test Data Generation

```python
def generate_random_latex():
    """Generate realistic LaTeX documents"""
    components = [
        r"\documentclass{article}",
        r"\begin{document}",
        random_sections(),
        random_math_blocks(),
        random_environments(),
        random_comments(),
        r"\end{document}"
    ]
    return '\n'.join(components)

def generate_random_edit():
    """Generate realistic edit operations"""
    edit_types = [
        CharacterInsert,     # Type single character
        WordInsert,          # Type word
        LineInsert,          # Add line
        BlockPaste,          # Paste multiple lines
        CharacterDelete,     # Delete character
        SelectionReplace,    # Replace selection
    ]
    return random.choice(edit_types).generate()
```

### Fuzzing Targets
- **1M single edits**: Basic equivalence
- **100k edit sequences**: Multi-edit correctness
- **10k documents**: Document variety
- **Edge cases**: Empty docs, huge docs, special chars

---

## Layer 3: Unit Tests

### Coq Unit Tests

```coq
(* File: tests/coq/test_checkpoint.v *)

Example checkpoint_split_example :
  let text := "Hello\nWorld" in
  let (part1, part2) := split_at_newline text in
  part1 = "Hello" /\ part2 = "World".
Proof. reflexivity. Qed.

Example codec_bool_roundtrip :
  decode_bool (encode_bool true) = Some true.
Proof. reflexivity. Qed.
```

### OCaml Unit Tests

```ocaml
(* File: tests/ocaml/test_incremental.ml *)

let test_hash_computation () =
  let line = "\\section{Test}" in
  let hash1 = hash_line line in
  let hash2 = hash_line line in
  assert (hash1 = hash2);  (* Deterministic *)
  
  let different = "\\section{Different}" in
  let hash3 = hash_line different in
  assert (hash1 <> hash3)  (* Collision resistant *)

let test_state_checkpoint () =
  let state = create_initial_state () in
  let checkpoint = checkpoint_state state in
  let restored = restore_checkpoint checkpoint in
  assert (state_equal state restored)
```

### Python Unit Tests

```python
# File: tests/python/test_ffi_bridge.py

def test_lexer_creation():
    lexer = IncrementalLexer()
    assert lexer.lexer_id >= 0
    assert lexer.get_memory_usage() >= 0

def test_document_loading():
    lexer = IncrementalLexer()
    doc = "\\documentclass{article}\n\\begin{document}\nHello\n\\end{document}"
    assert lexer.load_document(doc) == True
    assert lexer.current_document == doc

def test_single_edit():
    lexer = IncrementalLexer()
    lexer.load_document("Hello world")
    result = lexer.apply_edit(0, 5, " beautiful")
    assert result.processing_time_ms < 10
    assert len(result.tokens) > 0
```

---

## Layer 4: Performance Tests

### Benchmark Suite

```python
class PerformanceBenchmark:
    def __init__(self):
        self.test_files = {
            'small': self.create_file(100_000),    # 100KB
            'medium': self.create_file(1_000_000), # 1MB
            'large': self.create_file(3_000_000),  # 3MB
            'huge': self.create_file(10_000_000),  # 10MB
        }
    
    def benchmark_single_char_edit(self, size_name):
        lexer = IncrementalLexer()
        lexer.load_document(self.test_files[size_name])
        
        # Measure single character insertion
        times = []
        for i in range(1000):
            start = time.perf_counter()
            lexer.apply_edit(
                line=random.randint(0, 1000),
                column=random.randint(0, 50),
                content='x'
            )
            elapsed = time.perf_counter() - start
            times.append(elapsed * 1000)  # Convert to ms
        
        return {
            'mean': statistics.mean(times),
            'p95': percentile(times, 95),
            'p99': percentile(times, 99),
            'max': max(times),
        }
```

### Performance Requirements Matrix

| Test Case | Target | Measurement | Pass Criteria |
|-----------|---------|-------------|---------------|
| 3MB single char | <1ms | Mean time | Mean < 1ms |
| 3MB line edit | <5ms | P95 time | P95 < 5ms |
| 3MB paragraph | <100ms | P99 time | P99 < 100ms |
| 10MB memory | <100MB | Peak usage | Peak < 100MB |

### Memory Testing

```python
def test_memory_usage():
    lexer = IncrementalLexer()
    
    # Load large document
    large_doc = create_document(10_000_000)  # 10MB
    lexer.load_document(large_doc)
    
    initial_memory = lexer.get_memory_usage()
    assert initial_memory < 100 * 1024 * 1024  # <100MB
    
    # Perform many edits
    for i in range(10000):
        lexer.apply_edit(i % 1000, 0, f"edit{i}")
    
    final_memory = lexer.get_memory_usage()
    assert final_memory < 150 * 1024 * 1024  # <150MB with cache
    
    # Test cache eviction
    lexer.clear_caches()
    cleared_memory = lexer.get_memory_usage()
    assert cleared_memory < initial_memory * 1.1
```

---

## Layer 5: Integration Tests

### Cross-Language Integration

```python
def test_coq_to_ocaml_to_python():
    """Test full pipeline integration"""
    
    # Load test document
    test_doc = load_test_file('integration_test.tex')
    
    # Process through full pipeline
    lexer = IncrementalLexer()
    lexer.load_document(test_doc)
    
    # Apply realistic edit sequence
    edits = load_edit_sequence('edit_sequence.json')
    for edit in edits:
        result = lexer.apply_edit(**edit)
        assert result.processing_time_ms < 100
        assert not result.error
```

### Error Handling

```python
def test_error_recovery():
    lexer = IncrementalLexer()
    
    # Test invalid operations
    with pytest.raises(IncrementalLexerError):
        lexer.apply_edit(0, 0, "test")  # No document
    
    # Test recovery
    lexer.load_document("Valid document")
    result = lexer.apply_edit(0, 0, "test")
    assert len(result.tokens) > 0  # Should work
```

---

## Layer 6: End-to-End Tests

### Editor Simulation

```python
def test_realistic_editing_session():
    """Simulate real user editing LaTeX"""
    
    editor = RealTimeLaTeXLexer()
    editor.set_document(load_test_file('thesis.tex'))
    
    # Simulate typing
    for char in "\\section{Introduction}\n":
        tokens = editor.on_text_change(
            line=10, 
            column=0, 
            content=char
        )
        assert response_time() < 50  # <50ms for typing
    
    # Simulate paste
    tokens = editor.on_text_change(
        line=20,
        column=0,
        content=load_snippet('methodology.tex')
    )
    assert response_time() < 200  # <200ms for paste
```

---

## Continuous Integration

### CI Pipeline

```yaml
name: Incremental Lexer CI

on: [push, pull_request]

jobs:
  formal-verification:
    runs-on: ubuntu-latest
    steps:
      - name: Verify Coq Proofs
        run: |
          cd src/coq/lexer
          make clean && make
          ./verify_no_admits.sh

  equivalence-testing:
    runs-on: ubuntu-latest
    steps:
      - name: Run Fuzzing
        run: |
          python tests/fuzz_equivalence.py \
            --iterations 100000 \
            --timeout 3600

  performance-testing:
    runs-on: ubuntu-latest
    steps:
      - name: Run Benchmarks
        run: |
          python tests/benchmark_performance.py
          python tests/check_regression.py

  integration-testing:
    runs-on: ubuntu-latest
    steps:
      - name: Full Integration Tests
        run: |
          pytest tests/integration/ -v
```

---

## Test Metrics & Monitoring

### Coverage Requirements
- Coq proofs: 100% (all theorems proven)
- OCaml code: >95% line coverage
- Python code: >90% line coverage
- Integration paths: 100% critical paths

### Performance Tracking

```python
def track_performance_over_time():
    """Track performance across commits"""
    
    results = run_benchmark_suite()
    
    # Store in database
    store_metrics({
        'commit': get_current_commit(),
        'timestamp': datetime.now(),
        'results': results
    })
    
    # Check for regression
    baseline = get_baseline_metrics()
    for metric, value in results.items():
        if value > baseline[metric] * 1.1:  # >10% slower
            raise PerformanceRegression(
                f"{metric} degraded: {value} vs {baseline[metric]}"
            )
```

---

## Failure Protocol

### When Tests Fail

1. **Formal Verification Failure**
   - STOP all development
   - Fix proofs before proceeding
   - No commits with admits

2. **Equivalence Failure**
   - Log complete failure case
   - Minimize reproduction case
   - Add to regression suite
   - Fix root cause

3. **Performance Failure**
   - Identify slow operation
   - Profile implementation
   - Optimize without breaking correctness
   - Update benchmarks if needed

4. **Integration Failure**
   - Check API compatibility
   - Verify error handling
   - Update integration tests

---

## Summary

The comprehensive testing strategy ensures:
- **Mathematical correctness** through formal proofs and fuzzing
- **Performance guarantees** through continuous benchmarking
- **Production reliability** through integration and E2E tests
- **Regression prevention** through CI/CD automation

**Result**: A verified, fast, and reliable incremental lexer.