# Implementation Roadmap: LaTeX Perfectionist Validation System

Based on the comprehensive solution provided, here's our actionable implementation plan:

## Phase 1: Grammar Extraction (Week 1-2)

### 1.1 Extract LaTeX Grammar
```python
# extract_grammar.py
def extract_catcodes_from_tex():
    """Extract category codes from plain.tex and expl3."""
    # Parse plain.tex to get default catcodes
    # Parse expl3 for extended catcodes
    # Generate formal grammar specification
    return Grammar(
        catcodes=catcode_table,
        environments=environment_list,
        commands=command_list
    )
```

### 1.2 Build Context Tracker
```python
# context_tracker.py
class ContextTracker:
    """PDA-based context tracking with formal verification."""
    def __init__(self, grammar):
        self.grammar = grammar
        self.stack = []
    
    def enter_context(self, token):
        # Push context based on grammar rules
        pass
    
    def exit_context(self, token):
        # Pop context, verify balance
        pass
    
    def is_in_context(self, context_type):
        # O(1) context query
        return context_type in self.stack
```

## Phase 2: Property-Based Testing (Week 3-4)

### 2.1 Grammar-Driven Test Generation
```python
# grammar_fuzzer.py
from hypothesis import strategies as st

def latex_document_from_grammar(grammar):
    """Generate valid LaTeX using extracted grammar."""
    @st.composite
    def strategy(draw):
        # Use grammar productions to generate valid LaTeX
        tokens = draw(st.lists(grammar.token_strategy()))
        return ''.join(tokens)
    return strategy

# Generate test cases automatically
test_docs = [latex_document_from_grammar(grammar).example() 
             for _ in range(1000)]
```

### 2.2 Metamorphic Properties
```python
# metamorphic_tests.py
def test_idempotency(rule, document):
    """audit(audit(x)) ≡ audit(x)"""
    once = rule.apply(document)
    twice = rule.apply(once)
    assert once == twice

def test_semantic_preservation(rule, document):
    """LaTeX compilation unchanged"""
    original_pdf = compile_to_pdf(document)
    fixed_pdf = compile_to_pdf(rule.apply(document))
    assert pdfs_equivalent(original_pdf, fixed_pdf)
```

## Phase 3: Shadow Mode Testing (Week 5-6)

### 3.1 Shadow Mode Runner
```python
# shadow_mode.py
class ShadowModeValidator:
    def __init__(self, corpus_path):
        self.corpus = load_corpus(corpus_path)
        self.results = []
    
    def run_shadow_mode(self, rule):
        """Run rule without applying fixes."""
        for doc in self.corpus:
            issues = rule.audit(doc)
            self.results.append({
                'doc': doc.path,
                'issues': issues,
                'would_change': len(issues) > 0
            })
        
        # Analyze for false positives
        false_positives = self.detect_false_positives()
        return len(false_positives) == 0
```

### 3.2 Differential Testing
```python
# differential_testing.py
def compare_tex_engines(document):
    """Compile with multiple engines, compare output."""
    results = {}
    for engine in ['pdflatex', 'lualatex', 'xelatex']:
        try:
            pdf = compile_with_engine(document, engine)
            results[engine] = compute_pdf_hash(pdf)
        except CompilationError as e:
            results[engine] = f"error: {e}"
    
    # All engines should produce same result
    hashes = [h for h in results.values() if not h.startswith("error")]
    return len(set(hashes)) == 1
```

## Phase 4: Incremental Validation (Week 7-8)

### 4.1 Incremental Parser
```python
# incremental_parser.py
class IncrementalValidator:
    def __init__(self, checkpoint_interval=4096):
        self.checkpoint_interval = checkpoint_interval
        self.checkpoints = {}
    
    def create_checkpoints(self, document):
        """Create restart points every k characters."""
        for i in range(0, len(document), self.checkpoint_interval):
            context = self.compute_context_at(document, i)
            self.checkpoints[i] = context
    
    def validate_change(self, document, change_start, change_end):
        """Only re-validate affected region."""
        # Find nearest checkpoint before change
        checkpoint = max(k for k in self.checkpoints if k <= change_start)
        # Only validate from checkpoint to change_end + buffer
        return self.validate_region(document, checkpoint, change_end + 1000)
```

## Immediate Next Steps

1. **Extract Grammar from plain.tex** (Day 1-3)
   ```bash
   python extract_grammar.py /usr/share/texlive/texmf-dist/tex/plain/base/plain.tex
   ```

2. **Build PDA Context Tracker** (Day 4-7)
   - Implement stack-based context tracking
   - Add formal verification properties

3. **Grammar-Based Fuzzer** (Week 2)
   - Connect Hypothesis to grammar
   - Generate 10,000 test documents automatically

4. **Shadow Mode on Current Rules** (Week 3)
   - Run TYPO-001 and TYPO-002 in shadow mode
   - Measure false positive rate on real corpus

5. **Differential PDF Testing** (Week 4)
   - Set up multi-engine compilation
   - Implement PDF comparison

## Success Metrics

- [ ] Grammar extraction covers 100% of standard LaTeX contexts
- [ ] PDA tracker passes formal verification
- [ ] Fuzzer generates valid LaTeX 99.9% of the time  
- [ ] Shadow mode shows 0 false positives on 10,000 documents
- [ ] All rules pass idempotency and preservation tests
- [ ] Validation time < 30 seconds for 1,000 documents

## Key Innovation Points

1. **No Manual Test Writing**: Grammar drives everything
2. **No Position Tracking**: Context stack tells us everything
3. **No Ground Truth Needed**: Metamorphic properties + differential testing
4. **Automatic Failure Triage**: Clustering by minimal failing slice

This approach transforms validation from a manual, error-prone process to an automated, mathematically rigorous system. The beauty is that once we build the grammar extractor and PDA tracker, everything else follows automatically.