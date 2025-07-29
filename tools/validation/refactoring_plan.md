# LaTeX Perfectionist v22: Comprehensive Refactoring Plan

## 1. Current State Analysis

### 1.1 Existing Assets (Keep & Enhance)
```
✅ KEEP - High Value Components:
- src/latex_perfectionist/rules/compiled/rule_typo_001.py (working rule)
- src/latex_perfectionist/rules/compiled/rule_typo_002.py (working rule)
- src/latex_perfectionist/core/types.py (Issue, Fix, RuleResult)
- corpus/ (arXiv document collection)
- validation/foolproof_validator.py (behavior-based testing approach)

⚠️ MODIFY - Good Ideas, Poor Implementation:
- validation/v21_workflow.py (has validation concepts, needs redesign)
- validation/automated_validator.py (position-based, needs behavior focus)
- src/latex_perfectionist/testing/ (paranoid testing framework, needs integration)

❌ REMOVE - Obsolete/Problematic:
- validation/ground_truth_generator.py (synthetic approach superseded)
- validation/smart_paper_selector.py (manual selection superseded)
- refactoring/ (one-time scripts, can be archived)
```

### 1.2 Architecture Gaps
- No shadow mode validation
- No metamorphic property testing
- No incremental validation
- No multi-engine compilation
- No context-aware testing framework

## 2. New Project Structure (v22 Architecture)

```
latex_perfectionist/
├── README.md
├── pyproject.toml
├── requirements.txt
├── Makefile
│
├── src/latex_perfectionist/
│   ├── __init__.py
│   ├── core/                           # L1: Core Infrastructure
│   │   ├── __init__.py
│   │   ├── types.py                    # Issue, Fix, RuleResult (existing)
│   │   ├── document_parser.py          # Enhanced document parsing
│   │   ├── context_detector.py         # Context detection library
│   │   ├── corpus_manager.py           # Corpus management system
│   │   └── test_framework.py           # Testing infrastructure
│   │
│   ├── rules/                          # L2: Rule Engine
│   │   ├── __init__.py
│   │   ├── executor.py                 # Context-aware rule executor
│   │   ├── incremental.py              # Incremental change detector
│   │   ├── profiler.py                 # Performance profiler
│   │   └── compiled/                   # Compiled rules
│   │       ├── __init__.py
│   │       ├── rule_typo_001.py        # Enhanced with v22 context
│   │       └── rule_typo_002.py        # Enhanced with v22 context
│   │
│   ├── validation/                     # L3: Validation Engine
│   │   ├── __init__.py
│   │   ├── shadow_mode.py              # Shadow mode validator
│   │   ├── metamorphic.py              # Metamorphic property tester
│   │   ├── property_based.py           # Property-based test generator
│   │   ├── multi_engine.py             # Multi-engine compiler
│   │   └── clustering.py               # Failure clustering
│   │
│   ├── dashboard/                      # L4: Dashboard & Reporting
│   │   ├── __init__.py
│   │   ├── web_interface.py            # Web dashboard
│   │   ├── reports.py                  # Report generation
│   │   └── metrics.py                  # Metrics collection
│   │
│   └── cli/                            # Command-line interface
│       ├── __init__.py
│       ├── main.py                     # Main CLI entry point
│       ├── validate.py                 # Validation commands
│       └── corpus.py                   # Corpus commands
│
├── tests/                              # Test suite
│   ├── __init__.py
│   ├── conftest.py                     # Pytest configuration
│   ├── unit/                           # Unit tests
│   │   ├── test_context_detector.py
│   │   ├── test_shadow_mode.py
│   │   └── test_metamorphic.py
│   ├── integration/                    # Integration tests
│   │   ├── test_validation_pipeline.py
│   │   └── test_multi_engine.py
│   └── fixtures/                       # Test fixtures
│       ├── documents/
│       └── expected_results/
│
├── corpus/                             # Document corpus
│   ├── demo_corpus/                    # Small test corpus
│   ├── validation_corpus/              # Validation corpus
│   └── benchmark_corpus/               # Performance benchmarks
│
├── config/                             # Configuration
│   ├── validation_config.yaml
│   ├── corpus_config.yaml
│   └── engine_config.yaml
│
├── scripts/                            # Utility scripts
│   ├── setup_corpus.py
│   ├── run_validation.py
│   └── benchmark.py
│
└── docs/                               # Documentation
    ├── architecture.md
    ├── validation_guide.md
    └── api_reference.md
```

## 3. Refactoring Strategy

### 3.1 Phase 1: Foundation Refactoring (Week 1)

#### 3.1.1 Create New Core Infrastructure
```python
# src/latex_perfectionist/core/context_detector.py
from typing import List, Optional, Tuple
from dataclasses import dataclass
from enum import Enum

class ContextType(Enum):
    NORMAL = "normal"
    VERBATIM = "verbatim"
    MATH_INLINE = "math_inline"
    MATH_DISPLAY = "math_display"
    CODE = "code"
    COMMENT = "comment"

@dataclass
class Context:
    type: ContextType
    start: int
    end: int
    nested_level: int = 0

class ContextDetector:
    """Enhanced context detection with caching and validation."""
    
    def __init__(self):
        self._cache = {}
        self._patterns = self._load_patterns()
    
    def detect_context(self, text: str, position: int) -> Context:
        """Detect context at specific position."""
        pass
    
    def get_all_contexts(self, text: str) -> List[Context]:
        """Get all contexts in document."""
        pass
    
    def is_in_context(self, text: str, position: int, context_type: ContextType) -> bool:
        """Check if position is in specific context type."""
        pass
```

#### 3.1.2 Enhance Rule Executor
```python
# src/latex_perfectionist/rules/executor.py
from typing import List, Optional
from ..core.types import Issue, Fix, RuleResult
from ..core.context_detector import ContextDetector

class RuleExecutor:
    """Context-aware rule executor with enhanced validation."""
    
    def __init__(self):
        self.context_detector = ContextDetector()
        self.performance_metrics = {}
    
    def execute_rule(self, rule_module, text: str, config: dict) -> RuleResult:
        """Execute rule with context awareness."""
        # Time execution
        start_time = time.time()
        
        # Get base result
        result = rule_module.audit(text, config)
        
        # Filter fixes based on context
        filtered_fixes = self._filter_fixes_by_context(result.fixes, text)
        
        # Update performance metrics
        self.performance_metrics[rule_module.RULE_ID] = {
            'execution_time': time.time() - start_time,
            'issues_found': len(result.issues),
            'fixes_applied': len(filtered_fixes)
        }
        
        return RuleResult(result.issues, filtered_fixes)
    
    def _filter_fixes_by_context(self, fixes: List[Fix], text: str) -> List[Fix]:
        """Filter fixes based on context detection."""
        pass
```

#### 3.1.3 Create Shadow Mode Validator
```python
# src/latex_perfectionist/validation/shadow_mode.py
from typing import List, Dict, Optional
from dataclasses import dataclass
from ..core.types import Issue, Fix
from ..rules.executor import RuleExecutor

@dataclass
class ShadowResult:
    rule_id: str
    document_path: str
    issues_found: List[Issue]
    would_change: bool
    execution_time: float
    context_violations: List[Dict]

class ShadowModeValidator:
    """Run rules in shadow mode to detect false positives."""
    
    def __init__(self, corpus_manager):
        self.corpus_manager = corpus_manager
        self.executor = RuleExecutor()
        self.results = []
    
    def validate_rule(self, rule_module, corpus_subset: Optional[List[str]] = None) -> List[ShadowResult]:
        """Validate rule in shadow mode."""
        documents = corpus_subset or self.corpus_manager.get_all_documents()
        results = []
        
        for doc_path in documents:
            document = self.corpus_manager.load_document(doc_path)
            result = self._validate_single_document(rule_module, doc_path, document)
            results.append(result)
        
        return results
    
    def _validate_single_document(self, rule_module, doc_path: str, document: str) -> ShadowResult:
        """Validate rule on single document."""
        pass
    
    def detect_false_positives(self, results: List[ShadowResult]) -> List[ShadowResult]:
        """Detect potential false positives using heuristics."""
        pass
```

### 3.2 Phase 2: Validation Engine (Week 2)

#### 3.2.1 Metamorphic Property Testing
```python
# src/latex_perfectionist/validation/metamorphic.py
from typing import List, Dict, Any
from dataclasses import dataclass
from ..rules.executor import RuleExecutor

@dataclass
class PropertyResult:
    property_name: str
    passed: bool
    error_message: Optional[str] = None
    test_case: Optional[str] = None

class MetamorphicTester:
    """Test metamorphic properties of rules."""
    
    def __init__(self):
        self.executor = RuleExecutor()
    
    def test_idempotency(self, rule_module, document: str) -> PropertyResult:
        """Test that rule(rule(x)) == rule(x)."""
        pass
    
    def test_semantic_preservation(self, rule_module, document: str) -> PropertyResult:
        """Test that rule doesn't change document meaning."""
        pass
    
    def test_monotonicity(self, rule_module, document: str) -> PropertyResult:
        """Test that rule doesn't introduce new issues."""
        pass
    
    def run_all_properties(self, rule_module, documents: List[str]) -> Dict[str, List[PropertyResult]]:
        """Run all metamorphic properties on document set."""
        pass
```

#### 3.2.2 Property-Based Test Generator
```python
# src/latex_perfectionist/validation/property_based.py
from typing import List, Generator, Dict, Any
from hypothesis import strategies as st
from hypothesis.strategies import composite

class PropertyBasedGenerator:
    """Generate test cases using property-based testing."""
    
    def __init__(self):
        self.context_templates = self._load_context_templates()
    
    @composite
    def latex_document(self, draw) -> str:
        """Generate LaTeX document with various constructs."""
        pass
    
    def generate_context_tests(self, context_type: str, count: int) -> List[str]:
        """Generate documents with specific context type."""
        pass
    
    def generate_edge_cases(self, rule_module, count: int) -> List[str]:
        """Generate edge cases for specific rule."""
        pass
    
    def generate_mutation_tests(self, base_document: str, mutations: int) -> List[str]:
        """Generate mutations of base document."""
        pass
```

### 3.3 Phase 3: Integration & CLI (Week 3)

#### 3.3.1 Main CLI Interface
```python
# src/latex_perfectionist/cli/main.py
import click
from .validate import validate_cmd
from .corpus import corpus_cmd

@click.group()
@click.version_option()
def cli():
    """LaTeX Perfectionist v22 - Validation System."""
    pass

@cli.command()
@click.argument('rule_id')
@click.option('--corpus', default='validation', help='Corpus to use')
@click.option('--shadow', is_flag=True, help='Run in shadow mode')
@click.option('--properties', is_flag=True, help='Test metamorphic properties')
@click.option('--engines', multiple=True, help='Engines to test')
def validate(rule_id, corpus, shadow, properties, engines):
    """Validate a rule."""
    validate_cmd(rule_id, corpus, shadow, properties, engines)

@cli.command()
@click.argument('corpus_name')
@click.option('--size', default=1000, help='Corpus size')
def setup_corpus(corpus_name, size):
    """Set up validation corpus."""
    corpus_cmd.setup_corpus(corpus_name, size)

if __name__ == '__main__':
    cli()
```

#### 3.3.2 Validation Pipeline
```python
# src/latex_perfectionist/cli/validate.py
from typing import List, Optional
from ..validation.shadow_mode import ShadowModeValidator
from ..validation.metamorphic import MetamorphicTester
from ..validation.property_based import PropertyBasedGenerator
from ..validation.multi_engine import MultiEngineCompiler

def validate_cmd(rule_id: str, corpus: str, shadow: bool, properties: bool, engines: List[str]):
    """Main validation command."""
    print(f"🔍 Validating rule {rule_id}")
    
    # Load rule
    rule_module = load_rule(rule_id)
    
    # Initialize validators
    validators = {
        'shadow': ShadowModeValidator(corpus) if shadow else None,
        'metamorphic': MetamorphicTester() if properties else None,
        'multi_engine': MultiEngineCompiler(engines) if engines else None
    }
    
    # Run validation pipeline
    results = run_validation_pipeline(rule_module, validators)
    
    # Generate report
    generate_validation_report(rule_id, results)
```

### 3.4 Phase 4: Dashboard & Reporting (Week 4)

#### 3.4.1 Web Dashboard
```python
# src/latex_perfectionist/dashboard/web_interface.py
from flask import Flask, render_template, jsonify
from .reports import ReportGenerator
from .metrics import MetricsCollector

app = Flask(__name__)

@app.route('/')
def dashboard():
    """Main dashboard."""
    return render_template('dashboard.html')

@app.route('/api/validation/<rule_id>')
def validation_status(rule_id):
    """Get validation status for rule."""
    return jsonify(get_validation_status(rule_id))

@app.route('/api/metrics')
def metrics():
    """Get system metrics."""
    return jsonify(MetricsCollector().get_current_metrics())
```

## 4. Migration Strategy

### 4.1 Preserve Working Components
```bash
# Keep existing working rules
mv src/latex_perfectionist/rules/compiled/rule_typo_001.py src/latex_perfectionist/rules/compiled/rule_typo_001.py.backup
mv src/latex_perfectionist/rules/compiled/rule_typo_002.py src/latex_perfectionist/rules/compiled/rule_typo_002.py.backup

# Archive old validation attempts
mkdir -p archive/validation_attempts
mv validation/automated_validator.py archive/validation_attempts/
mv validation/ground_truth_generator.py archive/validation_attempts/
mv validation/smart_paper_selector.py archive/validation_attempts/
```

### 4.2 Extract Useful Code
```python
# Extract useful patterns from existing code
# validation/foolproof_validator.py -> src/latex_perfectionist/validation/shadow_mode.py
# validation/v21_workflow.py -> src/latex_perfectionist/validation/metamorphic.py
# src/latex_perfectionist/testing/paranoid_test_framework.py -> src/latex_perfectionist/validation/property_based.py
```

### 4.3 Update Dependencies
```toml
# pyproject.toml
[tool.poetry.dependencies]
python = "^3.9"
hypothesis = "^6.0"
pytest = "^7.0"
click = "^8.0"
flask = "^2.0"
pydantic = "^1.10"
pyyaml = "^6.0"
rich = "^13.0"  # For beautiful CLI output
```

## 5. Testing Strategy

### 5.1 Test Migration
```python
# Migrate existing tests to new structure
# tests/unit/test_context_detector.py
# tests/unit/test_shadow_mode.py
# tests/integration/test_validation_pipeline.py
```

### 5.2 New Test Categories
- **Unit Tests**: Each component in isolation
- **Integration Tests**: Component interaction
- **Property Tests**: Metamorphic properties
- **Performance Tests**: Benchmark validation
- **End-to-End Tests**: Complete validation pipeline

## 6. Implementation Priority

### Week 1: Foundation
1. Create new project structure
2. Implement ContextDetector
3. Enhance RuleExecutor
4. Create ShadowModeValidator base

### Week 2: Validation Core
1. Complete ShadowModeValidator
2. Implement MetamorphicTester
3. Create PropertyBasedGenerator
4. Set up MultiEngineCompiler

### Week 3: Integration
1. Build CLI interface
2. Create validation pipeline
3. Implement corpus management
4. Add performance profiling

### Week 4: Polish
1. Build web dashboard
2. Create comprehensive reports
3. Add metrics collection
4. Performance optimization

## 7. Success Criteria

- [ ] Shadow mode validation runs on 1,000 documents in <5 minutes
- [ ] All metamorphic properties pass for existing rules
- [ ] Property-based testing generates 1,000 test cases in <10 seconds
- [ ] Multi-engine compilation achieves 95% agreement
- [ ] CLI provides clear, actionable output
- [ ] Web dashboard shows real-time validation status

---

This refactoring plan provides a systematic approach to transform the current codebase into the v22 architecture while preserving valuable existing work and ensuring a smooth transition.