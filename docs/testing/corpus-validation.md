# 📚 Corpus Validation Strategy
## Real-World Testing with arXiv Papers

### Overview

The corpus validation system uses **2,844 real LaTeX documents** from arXiv to ensure the checkpoint-based incremental lexer produces **identical results** to the batch lexer. This provides confidence that the optimization preserves correctness across the full spectrum of LaTeX usage while achieving the target 1,000x+ speedup.

### Corpus Composition

- **Total papers**: 2,844 from diverse arXiv categories
- **Target selection**: 2,000 papers optimized for issue diversity
- **Quarantined papers**: 1,091 (being recovered for edge case testing)
- **Categories covered**: math, cs, physics, econ, q-bio, stat, and more

---

## Purpose of Corpus Testing

### Why Corpus Testing Matters

1. **Real-World Validation**: Academic papers use complex LaTeX features that synthetic tests might miss
2. **Performance Verification**: Measures speedup on authentic documents with realistic complexity
3. **Edge Case Discovery**: Finds issues that only appear in specific LaTeX constructs
4. **Regression Prevention**: Ensures changes don't break existing functionality

### What We Test

- **Equivalence**: Incremental tokens = Batch tokens for every document
- **Performance**: Actual speedup on real papers (target: >1000x)
- **Coverage**: Handles all LaTeX features found in practice
- **Stability**: No crashes or errors on any valid LaTeX

---

## Corpus Testing Architecture

### Integration with Incremental Lexer

```python
class CorpusIncrementalValidator:
    def __init__(self):
        self.batch_lexer = BatchLexer()
        self.incr_lexer = IncrementalLexer()
        self.test_results = []
    
    def validate_paper(self, paper_path):
        """Validate incremental lexer on single paper"""
        content = self.load_paper(paper_path)
        
        # Generate realistic edit sequence
        edits = self.generate_edit_sequence(content)
        
        # Process with both lexers
        batch_tokens = self.batch_lexer.tokenize(content)
        
        # Incremental processing
        self.incr_lexer.load_document(content)
        for edit in edits:
            self.incr_lexer.apply_edit(edit)
        incr_tokens = self.incr_lexer.get_all_tokens()
        
        # Verify equivalence
        assert tokens_equal(batch_tokens, incr_tokens)
        
        # Record performance
        return {
            'paper': paper_path,
            'size': len(content),
            'batch_time': batch_time,
            'incr_time': incr_time,
            'speedup': batch_time / incr_time
        }
```

### Edit Sequence Generation

```python
def generate_edit_sequence(content):
    """Generate realistic editing patterns"""
    edits = []
    lines = content.split('\n')
    
    # Simulate common editing patterns
    patterns = [
        # Typing new content
        lambda: insert_text(random_line(), "\\section{New Section}\n"),
        
        # Modifying equations
        lambda: replace_in_line("x^2", "x^3", find_equation_line()),
        
        # Adding citations
        lambda: insert_text(end_of_sentence(), "~\\cite{new2024}"),
        
        # Comment toggling
        lambda: toggle_comment(random_line()),
        
        # Copy-paste operations
        lambda: copy_paste_block(find_environment(), random_position())
    ]
    
    # Generate 50-100 edits per document
    for _ in range(random.randint(50, 100)):
        pattern = random.choice(patterns)
        edits.append(pattern())
    
    return edits
```

---

## Corpus Test Implementation

### Phase 1: Corpus Building

```bash
# Download diverse papers from arXiv
python corpus/build_corpus.py \
    --categories math.GT cs.LG physics.hep-th q-bio.NC \
    --max-papers 200 \
    --min-size 10000 \
    --require-math true
```

### Phase 2: Validation Execution

```python
def run_corpus_validation():
    """Main corpus validation entry point"""
    
    # Initialize validator
    validator = CorpusIncrementalValidator()
    
    # Load corpus
    papers = glob.glob("corpus/papers/*/main.tex")
    
    # Test each paper
    results = []
    for paper in tqdm(papers, desc="Validating corpus"):
        try:
            result = validator.validate_paper(paper)
            results.append(result)
        except Exception as e:
            logging.error(f"Failed on {paper}: {e}")
            # Record failure for investigation
            results.append({
                'paper': paper,
                'status': 'failed',
                'error': str(e)
            })
    
    # Generate report
    generate_corpus_report(results)
```

### Phase 3: Results Analysis

```python
def analyze_corpus_results(results):
    """Analyze validation results"""
    
    # Success rate
    success_rate = sum(1 for r in results if r.get('status') != 'failed') / len(results)
    
    # Performance metrics
    speedups = [r['speedup'] for r in results if 'speedup' in r]
    avg_speedup = statistics.mean(speedups)
    min_speedup = min(speedups)
    max_speedup = max(speedups)
    
    # Feature coverage
    features_tested = {
        'equations': count_papers_with_feature(results, 'equation'),
        'figures': count_papers_with_feature(results, 'includegraphics'),
        'tables': count_papers_with_feature(results, 'tabular'),
        'citations': count_papers_with_feature(results, 'cite'),
        'custom_commands': count_papers_with_feature(results, 'newcommand')
    }
    
    return {
        'success_rate': success_rate,
        'performance': {
            'average_speedup': avg_speedup,
            'min_speedup': min_speedup,
            'max_speedup': max_speedup
        },
        'coverage': features_tested
    }
```

---

## Expected Results

### Performance Targets

| Metric | Target | Acceptable Range |
|--------|--------|------------------|
| Success Rate | 100% | >99.5% |
| Average Speedup | >1500x | 1000x-2000x |
| Min Speedup | >500x | >200x |
| Memory Usage | <100MB | <150MB |

### Feature Coverage

All common LaTeX constructs must be handled:
- Math environments (equation, align, gather)
- Text formatting (sections, emphasis, lists)
- Floats (figures, tables)
- Bibliography and citations
- Custom commands and environments
- Comments (single and multi-line)

---

## Failure Investigation

### When Corpus Tests Fail

1. **Capture failing document**
   ```python
   def save_failure_case(paper, expected, actual):
       failure_dir = f"corpus/failures/{timestamp}"
       os.makedirs(failure_dir, exist_ok=True)
       
       # Save all relevant data
       shutil.copy(paper, failure_dir)
       json.dump({
           'expected_tokens': expected,
           'actual_tokens': actual,
           'diff': compute_token_diff(expected, actual)
       }, open(f"{failure_dir}/analysis.json", "w"))
   ```

2. **Minimize test case**
   ```python
   def minimize_failure(paper, edit_sequence):
       """Find minimal reproduction"""
       # Binary search to find minimal edit sequence
       # that still triggers the failure
   ```

3. **Add to regression suite**
   ```python
   def add_regression_test(minimal_case):
       """Add failing case to permanent test suite"""
       test_file = "tests/corpus_regressions.py"
       # Generate test case from minimal reproduction
   ```

---

## Continuous Corpus Testing

### CI Integration

```yaml
# .github/workflows/corpus-validation.yml
name: Corpus Validation

on:
  schedule:
    - cron: '0 0 * * 0'  # Weekly full corpus run
  pull_request:
    paths:
      - 'src/coq/lexer/**'
      - 'src/ocaml/runtime/**'

jobs:
  corpus-quick:
    runs-on: ubuntu-latest
    steps:
      - name: Quick corpus validation
        run: |
          python corpus/run_corpus_tests.py \
            --max-papers 10 \
            --categories math.GT cs.LG

  corpus-full:
    if: github.event_name == 'schedule'
    runs-on: ubuntu-latest
    steps:
      - name: Full corpus validation
        run: |
          python corpus/run_corpus_tests.py \
            --max-papers 200 \
            --all-categories
```

### Performance Tracking

```python
def track_corpus_performance():
    """Track performance over time"""
    
    results = run_corpus_validation()
    
    # Store in time series database
    metrics = {
        'timestamp': datetime.now(),
        'commit': get_git_commit(),
        'avg_speedup': results['performance']['average_speedup'],
        'success_rate': results['success_rate'],
        'corpus_size': len(results['papers'])
    }
    
    # Check for regression
    baseline = get_baseline_metrics()
    if metrics['avg_speedup'] < baseline['avg_speedup'] * 0.9:
        raise PerformanceRegression(
            f"Speedup degraded: {metrics['avg_speedup']} vs {baseline['avg_speedup']}"
        )
```

---

## Summary

The corpus validation system provides:

1. **Real-world confidence**: Tests on actual academic papers
2. **Performance validation**: Measures speedup on authentic documents  
3. **Comprehensive coverage**: Ensures all LaTeX features work
4. **Regression prevention**: Catches issues before production

**Result**: Mathematical correctness + real-world performance = production-ready incremental lexer.