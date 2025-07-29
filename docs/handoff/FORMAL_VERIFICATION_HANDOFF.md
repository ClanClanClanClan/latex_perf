# 🎯 FORMAL SPECIFICATION: REAL-TIME INCREMENTAL LATEX TOKENIZER
## LaTeX Perfectionist v24-R3: Complete Implementation Handoff Document

### 📋 DOCUMENT PURPOSE

This document provides **complete specifications** for implementing a real-time incremental LaTeX tokenizer that maintains our **formal verification guarantees** while achieving **sub-100ms response times** for files up to 3MB+.

**Target Audience**: AI assistant implementing this system  
**Criticality**: MAXIMUM - This must maintain mathematical correctness  
**Performance Requirement**: <100ms response for ANY file size  
**Quality Standard**: Formal verification compatible, production-ready  

---

## 🎯 PROBLEM STATEMENT

### Current Situation
- **Batch processing approach**: Re-tokenizes entire file on each change
- **Performance**: 43ms for 91KB → 1,452ms for 3MB (unusable for real-time)
- **User Experience**: 1.5 second delays make editing impossible

### Target Solution  
- **Incremental processing**: Only re-tokenize changed lines + context
- **Performance**: <0.1ms for single character edits (100,000x speedup)
- **User Experience**: Sub-100ms response for any edit to any size file

### Mathematical Verification Requirement
**CRITICAL**: The incremental tokenizer must produce **identical results** to the formally verified Coq lexer. This is NON-NEGOTIABLE.

---

## 📊 PERFORMANCE REQUIREMENTS SPECIFICATION

### Real-Time Response Targets
| Scenario | Response Time | User Experience |
|----------|---------------|-----------------|
| Single character edit | <1ms | Instantaneous |
| Single line edit | <5ms | Immediate |
| Paragraph edit (20 lines) | <50ms | Smooth |
| Section edit (100 lines) | <100ms | Real-time threshold |
| Large edit (1000+ lines) | <500ms | Acceptable for large changes |

### File Size Capabilities
| File Size | Lines (Est.) | Target Response | Implementation Priority |
|-----------|--------------|-----------------|------------------------|
| 100KB | 3,000 | <10ms | Phase 1 |
| 1MB | 30,000 | <50ms | Phase 1 |
| 3MB | 100,000 | <100ms | Phase 2 |
| 10MB | 300,000 | <200ms | Phase 3 |

### Accuracy Requirements
- **100% tokenization accuracy**: Must match Coq-verified lexer exactly
- **0% false positives**: Maintain comment handling perfection  
- **Complete LaTeX support**: All constructs supported by original lexer
- **State consistency**: Lexer state must be preserved across incremental updates

---

## 🏗️ ARCHITECTURAL SPECIFICATION

### High-Level Architecture

```
┌──────────────┐    ┌─────────────────┐    ┌──────────────────┐
│  Text Editor │───▶│  Change Detector │───▶│  Incremental     │
│  (User Input)│    │  (Line Diffs)   │    │  Tokenizer       │
└──────────────┘    └─────────────────┘    └──────────────────┘
                           │                         │
                           ▼                         ▼
                    ┌─────────────────┐    ┌──────────────────┐
                    │   Line Cache    │◀───│  Token Stream    │
                    │  (Hash + State) │    │  (Real-time Out) │
                    └─────────────────┘    └──────────────────┘
```

### Core Components Required

#### 1. **Line-Based Text Manager**
```python
class LineBasedDocument:
    """Manages large documents as array of lines for efficient editing"""
    
    def __init__(self, content: str):
        self.lines: List[str] = content.split('\n')
        self.line_hashes: List[str] = [hash_line(line) for line in self.lines]
        self.last_modified: List[float] = [time.time()] * len(self.lines)
    
    def update_lines(self, new_content: str) -> List[int]:
        """Returns list of changed line numbers"""
        # IMPLEMENT: Efficient diff algorithm
        # RETURN: Only line numbers that actually changed
```

#### 2. **Incremental Lexer State Manager**
```python
class LexerStateManager:
    """Tracks lexer state at end of each line for incremental processing"""
    
    def __init__(self):
        self.line_states: Dict[int, LexerState] = {}  # line_num -> end state
        self.state_cache_hits = 0
        self.state_cache_misses = 0
    
    def get_initial_state(self, line_num: int) -> LexerState:
        """Get lexer state at start of given line"""
        if line_num == 0:
            return create_initial_lexer_state()
        
        # Look for cached state from previous line
        prev_state = self.line_states.get(line_num - 1)
        if prev_state:
            return copy_lexer_state(prev_state)
        
        # CRITICAL: If no cached state, must recompute from beginning
        # This is where performance optimization is crucial
```

#### 3. **Token Cache with Validation**
```python
class ValidatedTokenCache:
    """Caches tokenization results with hash-based validation"""
    
    def __init__(self, max_size: int = 100000):
        self.cache: Dict[Tuple[int, str], CacheEntry] = {}  # (line_num, hash) -> tokens
        self.max_size = max_size
    
    @dataclass
    class CacheEntry:
        tokens: List[Token]
        final_state: LexerState
        timestamp: float
        access_count: int
    
    def get_tokens(self, line_num: int, content: str, initial_state: LexerState) -> Tuple[List[Token], LexerState]:
        """Get tokens for line, using cache if valid or recomputing if needed"""
        content_hash = hash_line(content)
        cache_key = (line_num, content_hash)
        
        if cache_key in self.cache:
            entry = self.cache[cache_key]
            entry.access_count += 1
            return entry.tokens, entry.final_state
        
        # Cache miss - must tokenize
        tokens, final_state = tokenize_single_line(content, initial_state, line_num)
        
        # Store in cache
        self.cache[cache_key] = self.CacheEntry(
            tokens=tokens,
            final_state=final_state,
            timestamp=time.time(),
            access_count=1
        )
        
        return tokens, final_state
```

#### 4. **Change Detection Algorithm**
```python
def detect_changed_lines(old_lines: List[str], new_lines: List[str]) -> List[int]:
    """Efficiently detect which lines changed between versions"""
    
    # REQUIREMENT: Must be faster than O(n) for typical edits
    # IMPLEMENTATION OPTIONS:
    # 1. Line-by-line comparison (simple, O(n))
    # 2. Myers diff algorithm (complex, O(nd))  
    # 3. Hash-based detection (fast for most cases)
    
    changed_lines = []
    max_len = max(len(old_lines), len(new_lines))
    
    for i in range(max_len):
        old_line = old_lines[i] if i < len(old_lines) else None
        new_line = new_lines[i] if i < len(new_lines) else None
        
        if old_line != new_line:
            changed_lines.append(i)
    
    return changed_lines
```

### State Propagation Strategy

**CRITICAL REQUIREMENT**: LaTeX tokenization is context-sensitive. Changes early in the file can affect tokenization later.

```python
def propagate_state_changes(lexer: IncrementalLexer, changed_lines: List[int]) -> List[int]:
    """Determine which additional lines need re-tokenization due to state changes"""
    
    lines_to_process = set(changed_lines)
    
    for line_num in sorted(changed_lines):
        # Check if this line's final state differs from cached state
        old_final_state = lexer.state_manager.line_states.get(line_num)
        
        # Re-tokenize line to get new final state
        tokens, new_final_state = lexer.tokenize_line(line_num)
        
        if old_final_state is None or not states_equal(old_final_state, new_final_state):
            # State changed - need to invalidate subsequent lines until state stabilizes
            lines_to_process.update(find_affected_lines(line_num, new_final_state))
    
    return sorted(lines_to_process)
```

---

## 🔬 FORMAL VERIFICATION COMPATIBILITY

### Mathematical Correctness Requirements

#### 1. **Tokenization Equivalence**
```python
def verify_incremental_correctness(content: str) -> bool:
    """Verify incremental tokenizer produces identical results to batch tokenizer"""
    
    # Batch tokenization (ground truth)
    batch_tokens = batch_tokenize_with_coq_lexer(content)
    
    # Incremental tokenization  
    incremental_lexer = IncrementalLexer()
    incremental_lexer.set_content(content)
    incremental_tokens = incremental_lexer.get_all_tokens()
    
    # MUST BE IDENTICAL
    assert tokens_equal(batch_tokens, incremental_tokens), "Tokenization mismatch!"
    return True
```

#### 2. **State Consistency Verification**
```python
def verify_state_consistency(lexer: IncrementalLexer) -> bool:
    """Verify lexer states are consistent across line boundaries"""
    
    for line_num in range(1, lexer.total_lines):
        # State at end of previous line
        prev_final_state = lexer.state_manager.line_states[line_num - 1]
        
        # State at start of current line  
        curr_initial_state = lexer.state_manager.get_initial_state(line_num)
        
        # MUST BE IDENTICAL (except for position tracking)
        assert states_compatible(prev_final_state, curr_initial_state), \
            f"State inconsistency at line {line_num}!"
    
    return True
```

#### 3. **False Positive Prevention**
```python
def verify_false_positive_elimination(tokens: List[Token]) -> bool:
    """Verify no false positive indicators in TEXT tokens"""
    
    false_positive_count = 0
    
    for token in tokens:
        if token.type == 'TEXT':
            if '$' in token.content:
                false_positive_count += 1
            if '^' in token.content:
                false_positive_count += 1  
            if '_' in token.content:
                false_positive_count += 1
    
    assert false_positive_count == 0, f"Found {false_positive_count} false positive indicators!"
    return True
```

### Coq Lexer Integration

**REQUIREMENT**: The incremental tokenizer must use the same core tokenization logic as the formally verified Coq lexer.

```ocaml
(* CRITICAL: This must match the Coq lexer exactly *)
let tokenize_single_line_verified content initial_state line_num =
  (* Extract from lexer_optimized.ml but with position tracking *)
  let st = copy_state initial_state in
  st.line <- line_num;
  
  (* Same character processing logic as Coq lexer *)
  let tokens = ref [] in
  for i = 0 to String.length content - 1 do
    let c = content.[i] in
    st.column <- i;
    
    (* EXACT SAME LOGIC as optimized lexer *)
    if st.in_comment then
      match c with
      | '\n' | '\r' -> (* ... same as before ... *)
      | _ -> (* ... same as before ... *)
    (* ... rest of tokenization logic IDENTICAL ... *)
  done;
  
  (!tokens, st)
```

---

## ⚡ PERFORMANCE OPTIMIZATION STRATEGIES

### Memory Management
```python
class MemoryEfficientCache:
    """LRU cache with memory pressure handling"""
    
    def __init__(self, max_memory_mb: int = 100):
        self.max_memory_bytes = max_memory_mb * 1024 * 1024
        self.current_memory = 0
        self.cache = OrderedDict()
    
    def evict_if_needed(self):
        """Remove oldest entries if memory pressure detected"""
        while self.current_memory > self.max_memory_bytes and self.cache:
            oldest_key = next(iter(self.cache))
            removed_entry = self.cache.pop(oldest_key)
            self.current_memory -= self.estimate_size(removed_entry)
```

### Background Processing
```python
import asyncio
from typing import Callable

class BackgroundTokenizer:
    """Non-blocking incremental tokenization"""
    
    def __init__(self, callback: Callable[[List[Token]], None]):
        self.callback = callback
        self.processing_queue = asyncio.Queue()
        self.background_task = None
    
    async def process_changes(self, changed_lines: List[int]):
        """Process changes in background without blocking UI"""
        await self.processing_queue.put(changed_lines)
        
        if self.background_task is None:
            self.background_task = asyncio.create_task(self._background_worker())
    
    async def _background_worker(self):
        """Background worker that processes tokenization updates"""
        while True:
            try:
                changed_lines = await asyncio.wait_for(
                    self.processing_queue.get(), timeout=0.1
                )
                
                # Process incrementally
                updated_tokens = self.incremental_lexer.process_changes(changed_lines)
                
                # Call callback on main thread
                self.callback(updated_tokens)
                
            except asyncio.TimeoutError:
                # No work to do, yield control
                await asyncio.sleep(0.001)
```

### Multi-threading Strategy
```python
from concurrent.futures import ThreadPoolExecutor
import threading

class ThreadSafeIncrementalLexer:
    """Thread-safe incremental lexer for parallel processing"""
    
    def __init__(self):
        self.lexer_lock = threading.RLock()
        self.cache_lock = threading.RLock()
        self.thread_pool = ThreadPoolExecutor(max_workers=2)
    
    def process_large_change(self, changed_lines: List[int]) -> Future[List[Token]]:
        """Process large changes in background thread"""
        return self.thread_pool.submit(self._process_change_batch, changed_lines)
    
    def _process_change_batch(self, changed_lines: List[int]) -> List[Token]:
        """Thread-safe batch processing of changes"""
        with self.lexer_lock:
            return self.incremental_lexer.process_changes(changed_lines)
```

---

## 🧪 TESTING REQUIREMENTS

### Unit Test Coverage
```python
def test_single_line_tokenization():
    """Test basic line tokenization matches Coq lexer"""
    test_cases = [
        "\\section{Introduction}",
        "$x^2 + y^2 = z^2$",
        "Text % comment with $symbols$",
        "\\begin{document}Hello\\end{document}",
        "Math: $\\alpha + \\beta$ and text",
    ]
    
    for content in test_cases:
        # Compare with verified batch tokenizer
        batch_result = verified_batch_tokenizer(content)
        incremental_result = incremental_tokenizer.tokenize_line(content, initial_state, 0)
        
        assert tokens_equal(batch_result[0], incremental_result[0])

def test_incremental_equivalence():
    """Test incremental processing produces same result as batch"""
    large_content = generate_large_latex_document(size_mb=3)
    
    # Batch processing (slow but correct)
    batch_tokens = batch_tokenize(large_content)
    
    # Incremental processing
    incremental_lexer = IncrementalLexer()
    incremental_lexer.set_content(large_content)
    incremental_tokens = incremental_lexer.get_all_tokens()
    
    assert tokens_equal(batch_tokens, incremental_tokens)

def test_performance_requirements():
    """Test performance meets real-time requirements"""
    large_doc = create_3mb_latex_document()
    lexer = IncrementalLexer()
    lexer.set_content(large_doc)
    
    # Test single character edit
    start_time = time.time()
    lexer.edit_single_character(50000, 'a')  # Edit line 50,000
    elapsed_ms = (time.time() - start_time) * 1000
    
    assert elapsed_ms < 1.0, f"Single char edit took {elapsed_ms}ms (must be <1ms)"
    
    # Test larger edits
    start_time = time.time()
    lexer.edit_paragraph(50000, 20)  # Edit 20 lines at line 50,000
    elapsed_ms = (time.time() - start_time) * 1000
    
    assert elapsed_ms < 100.0, f"Paragraph edit took {elapsed_ms}ms (must be <100ms)"
```

### Integration Tests
```python
def test_real_editing_scenarios():
    """Test realistic editing workflows"""
    scenarios = [
        ("typing", simulate_user_typing),
        ("copy_paste", simulate_copy_paste),  
        ("find_replace", simulate_find_replace),
        ("section_reorder", simulate_section_reorder),
    ]
    
    for scenario_name, scenario_func in scenarios:
        print(f"Testing {scenario_name}...")
        elapsed_times = scenario_func(create_large_document())
        
        # All operations must be under real-time threshold
        max_time = max(elapsed_times)
        assert max_time < 100.0, f"{scenario_name} max time: {max_time}ms"

def test_stress_scenarios():
    """Test extreme scenarios"""
    # Very large file (10MB)  
    huge_doc = create_latex_document(size_mb=10)
    lexer = IncrementalLexer()
    lexer.set_content(huge_doc)
    
    # Many rapid edits
    for i in range(1000):
        start_time = time.time()
        lexer.edit_single_character(random.randint(0, lexer.total_lines-1), 'x')
        elapsed = (time.time() - start_time) * 1000
        assert elapsed < 5.0, f"Edit {i} took {elapsed}ms"
```

### Performance Benchmarks
```python
def benchmark_against_requirements():
    """Benchmark against formal performance requirements"""
    
    results = {
        "file_100kb": benchmark_file_size(100 * 1024),
        "file_1mb": benchmark_file_size(1024 * 1024), 
        "file_3mb": benchmark_file_size(3 * 1024 * 1024),
        "file_10mb": benchmark_file_size(10 * 1024 * 1024),
    }
    
    # Generate performance report
    print("PERFORMANCE BENCHMARK RESULTS")
    print("=" * 50)
    for test_name, metrics in results.items():
        print(f"{test_name}:")
        print(f"  Single char edit: {metrics['single_char']:.2f}ms")
        print(f"  Line edit: {metrics['line_edit']:.2f}ms") 
        print(f"  Paragraph edit: {metrics['paragraph']:.2f}ms")
        print(f"  Real-time capable: {'✅' if metrics['paragraph'] < 100 else '❌'}")
        print()
```

---

## 🚀 IMPLEMENTATION PHASES

### Phase 1: Core Incremental Engine (Week 1)
**Deliverables**:
- [ ] Line-based document manager
- [ ] Basic incremental tokenizer 
- [ ] Token cache with hash validation
- [ ] Unit tests for correctness

**Success Criteria**:
- Tokenization matches Coq lexer exactly
- Single line edits under 5ms
- Basic cache functionality working

### Phase 2: Performance Optimization (Week 1)  
**Deliverables**:
- [ ] State propagation algorithm
- [ ] Memory-efficient caching
- [ ] Background processing
- [ ] Performance benchmarks

**Success Criteria**:
- 3MB files: <100ms for any edit
- Memory usage under 100MB for 10MB files
- All performance requirements met

### Phase 3: Production Hardening (Week 1)
**Deliverables**:
- [ ] Thread safety
- [ ] Error handling and recovery
- [ ] Comprehensive test suite
- [ ] Integration with existing validator

**Success Criteria**:
- Zero crashes under stress testing
- Graceful degradation for extreme scenarios
- Full integration test suite passing

---

## 🎯 SUCCESS METRICS

### Functional Requirements
- [ ] **100% tokenization accuracy**: Identical to Coq lexer
- [ ] **0% false positives**: Comment handling preserved
- [ ] **Complete LaTeX support**: All constructs supported
- [ ] **State consistency**: No inconsistencies across edits

### Performance Requirements  
- [ ] **Single char edit**: <1ms (currently: N/A, need to implement)
- [ ] **Line edit**: <5ms (currently: N/A, need to implement)
- [ ] **Paragraph edit**: <50ms (currently: N/A, need to implement) 
- [ ] **Section edit**: <100ms (currently: N/A, need to implement)
- [ ] **3MB file support**: Full editing under 100ms (currently: impossible)

### Quality Requirements
- [ ] **Memory efficiency**: <100MB for 10MB files
- [ ] **Thread safety**: No race conditions
- [ ] **Error recovery**: Graceful handling of edge cases
- [ ] **Test coverage**: >95% line coverage
- [ ] **Performance stability**: Consistent under load

---

## 🔍 EDGE CASES AND CORNER CASES

### LaTeX-Specific Challenges
```latex
% These cases must be handled correctly:

1. Multi-line commands:
\newcommand{\mycommand}{%
  This spans multiple lines
}

2. Verbatim blocks:
\begin{verbatim}  
% This is not a comment!
$This is not math$
\end{verbatim}

3. Math mode spanning lines:
\begin{align}
  x &= y \\
  z &= w
\end{align}

4. Nested environments:
\begin{itemize}
  \item \begin{enumerate}
    \item Nested
  \end{enumerate}
\end{itemize}

5. Comment edge cases:
Text before % comment
% Full line comment
\% Escaped percent
```

### State Propagation Edge Cases
```python
def test_state_propagation_edge_cases():
    """Test complex state propagation scenarios"""
    
    edge_cases = [
        # Math mode starts on one line, ends on another
        ("math_across_lines", ["$x = ", "y + z$"]),
        
        # Command starts on one line, ends on another  
        ("command_across_lines", ["\\newcommand{\\test}{", "content here}"]),
        
        # Comment affects subsequent tokenization
        ("comment_state", ["Text % rest is comment", "New line continues"]),
        
        # Verbatim environment
        ("verbatim", ["\\begin{verbatim}", "% not a comment", "\\end{verbatim}"]),
    ]
    
    for case_name, lines in edge_cases:
        test_incremental_state_handling(case_name, lines)
```

---

## 🛡️ ERROR HANDLING SPECIFICATION

### Cache Corruption Recovery
```python
def handle_cache_corruption(lexer: IncrementalLexer, corrupted_line: int):
    """Recover from cache corruption by rebuilding from known good state"""
    
    # Find last known good state
    good_state_line = find_last_valid_state(lexer, corrupted_line)
    
    # Clear cache from corruption point forward
    lexer.clear_cache_from_line(good_state_line + 1)
    
    # Rebuild incrementally from good state
    lexer.rebuild_from_line(good_state_line + 1)
    
    # Verify correctness
    assert verify_tokenization_correctness(lexer)
```

### Memory Pressure Handling
```python
def handle_memory_pressure(lexer: IncrementalLexer):
    """Handle memory pressure by intelligent cache eviction"""
    
    # Measure current memory usage
    current_memory = get_memory_usage()
    
    if current_memory > MEMORY_THRESHOLD:
        # Evict least recently used cache entries
        evicted_count = lexer.cache.evict_lru(target_memory=MEMORY_THRESHOLD * 0.8)
        
        # Log for monitoring
        logger.info(f"Memory pressure: evicted {evicted_count} cache entries")
        
        # If still over threshold, fall back to batch processing
        if get_memory_usage() > MEMORY_THRESHOLD:
            logger.warning("Falling back to batch processing due to memory pressure")
            return lexer.fallback_to_batch_mode()
```

### Tokenization Mismatch Recovery
```python
def handle_tokenization_mismatch(incremental_tokens: List[Token], 
                                batch_tokens: List[Token],
                                line_range: Tuple[int, int]):
    """Handle case where incremental tokenization doesn't match batch"""
    
    # This should NEVER happen, but if it does:
    logger.error(f"Tokenization mismatch detected in lines {line_range}")
    
    # Clear incremental cache for affected range
    lexer.clear_cache_range(line_range[0], line_range[1])
    
    # Force re-tokenization using batch method
    corrected_tokens = batch_tokenize_range(line_range[0], line_range[1])
    
    # Update cache with corrected results
    lexer.update_cache_range(line_range, corrected_tokens)
    
    # Alert for investigation
    raise TokenizationInconsistencyError(
        f"Incremental tokenization mismatch at lines {line_range}"
    )
```

---

## 📚 REFERENCE IMPLEMENTATIONS

### Existing Code to Reuse
```python
# From lexer_optimized.ml - Core tokenization logic (MUST REUSE)
# From ultra_optimized_bridge.py - Token definitions and parsing
# From production_validator.py - Error handling patterns
# From fixed_integration.py - File I/O and subprocess management
```

### Libraries and Dependencies
```python
# Required libraries:
import hashlib          # For change detection
import threading        # For thread safety  
import asyncio          # For background processing
import time             # For performance measurement
from typing import *    # For type safety
from dataclasses import dataclass  # For structured data
from collections import OrderedDict  # For LRU cache
import weakref          # For memory-efficient references
```

---

## 🎯 FINAL IMPLEMENTATION CHECKLIST

### Must-Have Features
- [ ] **Incremental tokenization**: Only process changed lines
- [ ] **Hash-based change detection**: Efficient diff algorithm
- [ ] **State-aware caching**: Preserve lexer state across lines
- [ ] **Memory management**: LRU cache with size limits
- [ ] **Thread safety**: Safe for concurrent access
- [ ] **Error recovery**: Handle all edge cases gracefully

### Must-Maintain Qualities  
- [ ] **Mathematical correctness**: Identical to Coq lexer
- [ ] **Zero false positives**: Perfect comment handling
- [ ] **Performance guarantee**: <100ms for any reasonable edit
- [ ] **Memory efficiency**: Reasonable memory usage
- [ ] **Production quality**: No crashes, comprehensive error handling

### Must-Pass Tests
- [ ] **Correctness verification**: Against Coq lexer on all test cases
- [ ] **Performance benchmarks**: All timing requirements met
- [ ] **Stress testing**: Handles extreme scenarios gracefully
- [ ] **Integration testing**: Works with existing validation pipeline
- [ ] **Edge case coverage**: All LaTeX constructs handled correctly

---

## 🚨 CRITICAL SUCCESS FACTORS

### 1. **Preserve Mathematical Correctness**
The incremental tokenizer MUST produce identical results to the formally verified Coq lexer. Any deviation is a critical failure.

### 2. **Achieve Real-Time Performance**  
Sub-100ms response for any edit to any size file is non-negotiable. This is what makes the system usable.

### 3. **Maintain Zero False Positives**
The comment handling fix that eliminates false positives must be preserved exactly.

### 4. **Handle State Propagation Correctly**
LaTeX's context-sensitive nature means changes can affect distant parts of the file. The state propagation algorithm is critical.

### 5. **Provide Graceful Degradation**
If incremental processing fails for any reason, the system must fall back to batch processing without data loss.

---

## 📞 IMPLEMENTATION SUPPORT

### Questions to Resolve
1. **State Propagation Boundaries**: How far should state changes propagate before we can assume stability?
2. **Cache Size Optimization**: What's the optimal cache size vs memory usage trade-off?
3. **Background Processing Strategy**: Should large changes be processed synchronously or asynchronously?
4. **Error Recovery Policies**: What's the best strategy when incremental processing detects inconsistencies?

### Testing Data Available
- **Small test files**: Available in corpus/papers/
- **Performance baseline**: 43ms for 91KB files (batch processing)  
- **Correctness baseline**: Coq lexer produces verified results
- **Edge case samples**: Various LaTeX constructs for testing

### Success Validation Process
1. **Implement core incremental engine**
2. **Verify tokenization correctness** against Coq lexer
3. **Benchmark performance** against requirements  
4. **Test edge cases** and error scenarios
5. **Integration testing** with existing pipeline
6. **Stress testing** with large files and rapid edits

---

**🎯 IMPLEMENTATION TARGET**: Create a real-time incremental LaTeX tokenizer that maintains formal verification guarantees while achieving interactive performance for files of any size.

**📈 SUCCESS METRIC**: User can edit 3MB LaTeX files with <100ms response time while maintaining 100% tokenization accuracy and 0% false positives.

**🚀 ULTIMATE GOAL**: Enable real-time LaTeX editing experience equivalent to modern code editors like VS Code, but with mathematical correctness guarantees that no other system provides.**