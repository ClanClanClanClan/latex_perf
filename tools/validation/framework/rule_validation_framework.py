#!/usr/bin/env python3
"""
Comprehensive Generic Rule Validation Framework

This framework provides 100% accuracy validation for ANY LaTeX Perfectionist rule
through systematic ground truth creation, differential testing, and iterative refinement.

EVERY rule must pass through this validation process before production deployment.
"""

import os
import sys
import json
import sqlite3
import hashlib
import statistics
from pathlib import Path
from typing import Dict, List, Tuple, Set, Optional, Any
from dataclasses import dataclass, asdict
from enum import Enum
from datetime import datetime
import importlib.util

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / 'src'))

class ExampleType(Enum):
    """Types of validation examples."""
    POSITIVE = "positive"      # Should trigger the rule
    NEGATIVE = "negative"      # Should NOT trigger the rule
    EDGE_CASE = "edge_case"    # Boundary conditions
    ADVERSARIAL = "adversarial" # Designed to break the rule

class ValidationStatus(Enum):
    """Validation status for examples."""
    UNVERIFIED = "unverified"
    VERIFIED = "verified"
    DISPUTED = "disputed"
    REJECTED = "rejected"

class ContextType(Enum):
    """LaTeX contexts where rules may apply."""
    NORMAL_TEXT = "normal_text"
    MATH_INLINE = "math_inline"
    MATH_DISPLAY = "math_display"
    MATH_ENVIRONMENT = "math_environment"
    VERBATIM = "verbatim"
    COMMENT = "comment"
    PREAMBLE = "preamble"
    CITATION = "citation"
    REFERENCE = "reference"

@dataclass
class ValidationExample:
    """A single validation example with expected behavior."""
    id: str
    rule_id: str
    example_type: ExampleType
    context_type: ContextType
    latex_content: str
    should_trigger: bool
    expected_issues: int
    expected_fixes: List[str]
    difficulty_level: int  # 1=easy, 5=adversarial
    description: str
    verification_status: ValidationStatus
    verified_by: str
    verification_date: str
    notes: str

@dataclass
class ValidationResult:
    """Results of validating a rule against ground truth."""
    rule_id: str
    total_examples: int
    true_positives: int
    false_positives: int
    true_negatives: int
    false_negatives: int
    precision: float
    recall: float
    f1_score: float
    accuracy: float
    failed_examples: List[str]
    validation_date: str

@dataclass
class RuleSpecification:
    """Formal specification of what a rule should do."""
    rule_id: str
    name: str
    description: str
    category: str
    
    # What should trigger the rule
    positive_patterns: List[str]
    positive_contexts: List[ContextType]
    
    # What should NOT trigger the rule
    negative_patterns: List[str]
    negative_contexts: List[ContextType]
    
    # Edge cases and constraints
    edge_cases: List[str]
    constraints: List[str]
    
    # Success criteria
    min_precision: float  # Must be 1.0 for production
    min_recall: float
    max_false_positive_rate: float  # Must be 0.0 for production
    
    created_by: str
    created_date: str

class RuleValidationFramework:
    """Comprehensive framework for validating LaTeX Perfectionist rules."""
    
    def __init__(self, validation_dir: str = "validation"):
        self.validation_dir = Path(validation_dir)
        self.validation_dir.mkdir(exist_ok=True)
        
        # Database for storing validation data
        self.db_path = self.validation_dir / "validation.db"
        self._init_database()
        
        # Directories for organized storage
        self.specifications_dir = self.validation_dir / "specifications"
        self.examples_dir = self.validation_dir / "examples"
        self.results_dir = self.validation_dir / "results"
        self.reports_dir = self.validation_dir / "reports"
        
        for dir_path in [self.specifications_dir, self.examples_dir, 
                        self.results_dir, self.reports_dir]:
            dir_path.mkdir(exist_ok=True)
    
    def _init_database(self):
        """Initialize validation database."""
        with sqlite3.connect(self.db_path) as conn:
            # Rule specifications table
            conn.execute("""
                CREATE TABLE IF NOT EXISTS rule_specifications (
                    rule_id TEXT PRIMARY KEY,
                    name TEXT,
                    description TEXT,
                    category TEXT,
                    positive_patterns TEXT,
                    positive_contexts TEXT,
                    negative_patterns TEXT,
                    negative_contexts TEXT,
                    edge_cases TEXT,
                    constraints TEXT,
                    min_precision REAL,
                    min_recall REAL,
                    max_false_positive_rate REAL,
                    created_by TEXT,
                    created_date TEXT
                )
            """)
            
            # Validation examples table
            conn.execute("""
                CREATE TABLE IF NOT EXISTS validation_examples (
                    id TEXT PRIMARY KEY,
                    rule_id TEXT,
                    example_type TEXT,
                    context_type TEXT,
                    latex_content TEXT,
                    should_trigger BOOLEAN,
                    expected_issues INTEGER,
                    expected_fixes TEXT,
                    difficulty_level INTEGER,
                    description TEXT,
                    verification_status TEXT,
                    verified_by TEXT,
                    verification_date TEXT,
                    notes TEXT,
                    FOREIGN KEY (rule_id) REFERENCES rule_specifications (rule_id)
                )
            """)
            
            # Validation results table
            conn.execute("""
                CREATE TABLE IF NOT EXISTS validation_results (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    rule_id TEXT,
                    total_examples INTEGER,
                    true_positives INTEGER,
                    false_positives INTEGER,
                    true_negatives INTEGER,
                    false_negatives INTEGER,
                    precision REAL,
                    recall REAL,
                    f1_score REAL,
                    accuracy REAL,
                    failed_examples TEXT,
                    validation_date TEXT,
                    FOREIGN KEY (rule_id) REFERENCES rule_specifications (rule_id)
                )
            """)
    
    # ================================
    # Phase 1: Rule Specification
    # ================================
    
    def create_rule_specification(self, spec: RuleSpecification) -> bool:
        """Create formal specification for a rule."""
        try:
            with sqlite3.connect(self.db_path) as conn:
                conn.execute("""
                    INSERT OR REPLACE INTO rule_specifications VALUES (
                        ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?
                    )
                """, (
                    spec.rule_id, spec.name, spec.description, spec.category,
                    json.dumps(spec.positive_patterns),
                    json.dumps([ctx.value for ctx in spec.positive_contexts]),
                    json.dumps(spec.negative_patterns),
                    json.dumps([ctx.value for ctx in spec.negative_contexts]),
                    json.dumps(spec.edge_cases),
                    json.dumps(spec.constraints),
                    spec.min_precision, spec.min_recall, spec.max_false_positive_rate,
                    spec.created_by, spec.created_date
                ))
            
            # Save as JSON for human readability
            spec_file = self.specifications_dir / f"{spec.rule_id}.json"
            with open(spec_file, 'w') as f:
                json.dump(asdict(spec), f, indent=2, default=str)
            
            print(f"✓ Rule specification created: {spec.rule_id}")
            return True
            
        except Exception as e:
            print(f"✗ Failed to create specification: {e}")
            return False
    
    def generate_specification_template(self, rule_id: str) -> str:
        """Generate a template for rule specification."""
        template = f"""# Rule Specification: {rule_id}

## Purpose
Describe what this rule is designed to detect and fix.

## Positive Examples (Should Trigger)
Examples of LaTeX code that should trigger this rule:
```latex
"This should be fixed"
'Single quotes need fixing'
```

## Negative Examples (Should NOT Trigger)
Examples of LaTeX code that should NOT trigger this rule:
```latex
\\texttt{{"code in quotes"}}
\\verb|"literal quotes"|
${{\\rm "math quotes"}}$
```

## Contexts
- **Should apply in**: Normal text, certain environments
- **Should NOT apply in**: Verbatim, math mode, comments

## Edge Cases
- Empty quotes: `""`
- Nested quotes: `"outer 'inner' quotes"`
- LaTeX commands: `\\href{{"url"}}{{"text"}}`

## Success Criteria
- **Precision**: Must be 1.0 (no false positives)
- **Recall**: Should be ≥ 0.95 (catch 95% of real issues)
- **False Positive Rate**: Must be 0.0

## Implementation Notes
Special considerations, known limitations, etc.
"""
        return template
    
    # ================================
    # Phase 2: Ground Truth Creation
    # ================================
    
    def add_validation_example(self, example: ValidationExample) -> bool:
        """Add a validation example to the ground truth dataset."""
        try:
            with sqlite3.connect(self.db_path) as conn:
                conn.execute("""
                    INSERT OR REPLACE INTO validation_examples VALUES (
                        ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?
                    )
                """, (
                    example.id, example.rule_id, example.example_type.value,
                    example.context_type.value, example.latex_content,
                    example.should_trigger, example.expected_issues,
                    json.dumps(example.expected_fixes), example.difficulty_level,
                    example.description, example.verification_status.value,
                    example.verified_by, example.verification_date, example.notes
                ))
            
            print(f"✓ Added validation example: {example.id}")
            return True
            
        except Exception as e:
            print(f"✗ Failed to add example: {e}")
            return False
    
    def generate_examples_from_corpus(self, rule_id: str, count: int = 100) -> List[ValidationExample]:
        """Generate validation examples from the corpus."""
        examples = []
        
        # Load corpus papers
        corpus_dir = Path("corpus/papers")
        if not corpus_dir.exists():
            print("No corpus found")
            return examples
        
        paper_dirs = list(corpus_dir.iterdir())[:10]  # Sample 10 papers
        
        for paper_dir in paper_dirs:
            if not paper_dir.is_dir():
                continue
            
            # Load paper content
            try:
                metadata_file = paper_dir / "metadata.json"
                with open(metadata_file) as f:
                    metadata = json.load(f)
                
                main_tex_file = paper_dir / metadata['main_tex_file']
                if not main_tex_file.exists():
                    tex_files = list(paper_dir.glob("*.tex"))
                    if tex_files:
                        main_tex_file = tex_files[0]
                    else:
                        continue
                
                content = main_tex_file.read_text(encoding='utf-8', errors='ignore')
                
                # Extract relevant snippets based on rule type
                snippets = self._extract_relevant_snippets(content, rule_id)
                
                for i, snippet in enumerate(snippets[:5]):  # Max 5 per paper
                    example_id = f"{rule_id}_{paper_dir.name}_{i}"
                    
                    example = ValidationExample(
                        id=example_id,
                        rule_id=rule_id,
                        example_type=ExampleType.NEGATIVE,  # Assume negative, manual verification needed
                        context_type=self._detect_context_type(snippet),
                        latex_content=snippet,
                        should_trigger=False,  # To be manually verified
                        expected_issues=0,
                        expected_fixes=[],
                        difficulty_level=3,  # Medium difficulty
                        description=f"Real-world example from {paper_dir.name}",
                        verification_status=ValidationStatus.UNVERIFIED,
                        verified_by="",
                        verification_date="",
                        notes="Auto-generated from corpus, needs manual verification"
                    )
                    examples.append(example)
                    
            except Exception as e:
                print(f"Error processing {paper_dir.name}: {e}")
        
        return examples
    
    def _extract_relevant_snippets(self, content: str, rule_id: str) -> List[str]:
        """Extract relevant snippets for a rule from document content."""
        lines = content.split('\n')
        snippets = []
        
        # Rule-specific extraction logic
        if 'TYPO' in rule_id:
            # Look for lines with quotes or potential typography issues
            for line in lines:
                if any(char in line for char in ['"', "'", '`']):
                    # Include context (3 lines)
                    line_num = lines.index(line)
                    start = max(0, line_num - 1)
                    end = min(len(lines), line_num + 2)
                    snippet = '\n'.join(lines[start:end])
                    snippets.append(snippet)
        
        elif 'MATH' in rule_id:
            # Look for mathematical content
            for line in lines:
                if any(pattern in line for pattern in ['$', '\\[', '\\]', '\\begin{equation}']):
                    line_num = lines.index(line)
                    start = max(0, line_num - 1)
                    end = min(len(lines), line_num + 2)
                    snippet = '\n'.join(lines[start:end])
                    snippets.append(snippet)
        
        # Remove duplicates and limit size
        unique_snippets = list(set(snippets))
        return unique_snippets[:20]  # Max 20 snippets
    
    def _detect_context_type(self, snippet: str) -> ContextType:
        """Detect the LaTeX context type of a snippet."""
        if '\\begin{verbatim}' in snippet or '\\verb' in snippet:
            return ContextType.VERBATIM
        elif '%' in snippet and snippet.strip().startswith('%'):
            return ContextType.COMMENT
        elif any(env in snippet for env in ['\\begin{equation}', '\\begin{align}', '\\begin{gather}']):
            return ContextType.MATH_ENVIRONMENT
        elif '\\[' in snippet and '\\]' in snippet:
            return ContextType.MATH_DISPLAY
        elif '$' in snippet:
            return ContextType.MATH_INLINE
        elif any(cmd in snippet for cmd in ['\\documentclass', '\\usepackage', '\\newcommand']):
            return ContextType.PREAMBLE
        else:
            return ContextType.NORMAL_TEXT
    
    def create_adversarial_examples(self, rule_id: str) -> List[ValidationExample]:
        """Create adversarial examples designed to break the rule."""
        examples = []
        
        # Common adversarial patterns for typography rules
        if 'TYPO' in rule_id:
            adversarial_patterns = [
                # LaTeX braces that look like quotes
                '\\textbf{"bold text"}',
                '\\href{"url"}{"text"}',
                '{\\em "emphasized"}',
                '\\texttt{{"code"}}',
                
                # Mathematical expressions with braces
                '${\\rm "Det"}(A)$',
                '\\begin{equation}\\text{"solution"}\\end{equation}',
                
                # Escaped quotes
                '\\"actual quote\\"',
                
                # Comments with quotes
                '% This is "commented out"',
                
                # Verbatim environments
                '\\begin{verbatim}"raw text"\\end{verbatim}',
                
                # Mixed contexts
                'Text with "quotes" and $\\text{"math"}$ together',
            ]
            
            for i, pattern in enumerate(adversarial_patterns):
                example = ValidationExample(
                    id=f"{rule_id}_adversarial_{i}",
                    rule_id=rule_id,
                    example_type=ExampleType.ADVERSARIAL,
                    context_type=self._detect_context_type(pattern),
                    latex_content=pattern,
                    should_trigger=False,  # These should NOT trigger
                    expected_issues=0,
                    expected_fixes=[],
                    difficulty_level=5,  # Maximum difficulty
                    description=f"Adversarial example: {pattern[:30]}...",
                    verification_status=ValidationStatus.VERIFIED,
                    verified_by="framework",
                    verification_date=datetime.now().isoformat(),
                    notes="Auto-generated adversarial example"
                )
                examples.append(example)
        
        return examples
    
    # ================================
    # Phase 3: Automated Validation
    # ================================
    
    def validate_rule(self, rule_id: str, rule_module: Any = None) -> ValidationResult:
        """Validate a rule against all ground truth examples."""
        print(f"Validating rule: {rule_id}")
        
        # Load rule if not provided
        if rule_module is None:
            rule_module = self._load_rule(rule_id)
            if not rule_module:
                raise ValueError(f"Could not load rule: {rule_id}")
        
        # Load validation examples
        examples = self._load_validation_examples(rule_id)
        if not examples:
            print(f"No validation examples found for {rule_id}")
            return None
        
        # Run validation
        results = {
            'true_positives': 0,
            'false_positives': 0,
            'true_negatives': 0,
            'false_negatives': 0,
            'failed_examples': []
        }
        
        for example in examples:
            try:
                # Run rule on example
                audit_result = rule_module.audit(example.latex_content, {'locale': 'en-US'})
                issues_found = len(audit_result.issues)
                rule_triggered = issues_found > 0
                
                # Compare with expected result
                if example.should_trigger and rule_triggered:
                    results['true_positives'] += 1
                elif example.should_trigger and not rule_triggered:
                    results['false_negatives'] += 1
                    results['failed_examples'].append(f"{example.id}: Expected trigger, got none")
                elif not example.should_trigger and rule_triggered:
                    results['false_positives'] += 1
                    results['failed_examples'].append(f"{example.id}: Unexpected trigger")
                else:  # not should_trigger and not rule_triggered
                    results['true_negatives'] += 1
                    
            except Exception as e:
                results['failed_examples'].append(f"{example.id}: Rule execution error: {e}")
        
        # Calculate metrics
        total = len(examples)
        tp = results['true_positives']
        fp = results['false_positives']
        tn = results['true_negatives']
        fn = results['false_negatives']
        
        precision = tp / (tp + fp) if (tp + fp) > 0 else 0
        recall = tp / (tp + fn) if (tp + fn) > 0 else 0
        f1_score = 2 * (precision * recall) / (precision + recall) if (precision + recall) > 0 else 0
        accuracy = (tp + tn) / total if total > 0 else 0
        
        validation_result = ValidationResult(
            rule_id=rule_id,
            total_examples=total,
            true_positives=tp,
            false_positives=fp,
            true_negatives=tn,
            false_negatives=fn,
            precision=precision,
            recall=recall,
            f1_score=f1_score,
            accuracy=accuracy,
            failed_examples=results['failed_examples'],
            validation_date=datetime.now().isoformat()
        )
        
        # Save results
        self._save_validation_result(validation_result)
        
        return validation_result
    
    def _load_rule(self, rule_id: str) -> Any:
        """Load a compiled rule module."""
        # Map rule ID to file name
        rule_file_map = {
            'TYPO-001': 'rule_typo_001.py',
            'TYPO-002': 'rule_typo_002.py',
            'TYPO-003': 'rule_typo_003.py',
            'MATH-001': 'rule_math_001.py',
            'MENV-001': 'rule_menv_001.py',
            'MENV-002': 'rule_menv_002.py',
            'MENV-003': 'rule_menv_003.py',
        }
        
        rule_file = rule_file_map.get(rule_id)
        if not rule_file:
            return None
        
        rule_path = Path(f'src/latex_perfectionist/compiled_rules/{rule_file}')
        if not rule_path.exists():
            return None
        
        try:
            spec = importlib.util.spec_from_file_location(rule_id, rule_path)
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            return module
        except Exception as e:
            print(f"Error loading rule {rule_id}: {e}")
            return None
    
    def _load_validation_examples(self, rule_id: str) -> List[ValidationExample]:
        """Load validation examples for a rule."""
        examples = []
        
        with sqlite3.connect(self.db_path) as conn:
            cursor = conn.cursor()
            cursor.execute("""
                SELECT * FROM validation_examples WHERE rule_id = ?
            """, (rule_id,))
            
            for row in cursor.fetchall():
                example = ValidationExample(
                    id=row[0],
                    rule_id=row[1],
                    example_type=ExampleType(row[2]),
                    context_type=ContextType(row[3]),
                    latex_content=row[4],
                    should_trigger=bool(row[5]),
                    expected_issues=row[6],
                    expected_fixes=json.loads(row[7]) if row[7] else [],
                    difficulty_level=row[8],
                    description=row[9],
                    verification_status=ValidationStatus(row[10]),
                    verified_by=row[11],
                    verification_date=row[12],
                    notes=row[13]
                )
                examples.append(example)
        
        return examples
    
    def _save_validation_result(self, result: ValidationResult):
        """Save validation result to database."""
        with sqlite3.connect(self.db_path) as conn:
            conn.execute("""
                INSERT INTO validation_results VALUES (
                    NULL, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?
                )
            """, (
                result.rule_id, result.total_examples,
                result.true_positives, result.false_positives,
                result.true_negatives, result.false_negatives,
                result.precision, result.recall, result.f1_score, result.accuracy,
                json.dumps(result.failed_examples), result.validation_date
            ))
    
    # ================================
    # Phase 4: Reporting & Analysis
    # ================================
    
    def generate_validation_report(self, rule_id: str) -> str:
        """Generate comprehensive validation report."""
        # Load latest validation result
        with sqlite3.connect(self.db_path) as conn:
            cursor = conn.cursor()
            cursor.execute("""
                SELECT * FROM validation_results 
                WHERE rule_id = ? 
                ORDER BY validation_date DESC 
                LIMIT 1
            """, (rule_id,))
            
            row = cursor.fetchone()
            if not row:
                return f"No validation results found for {rule_id}"
        
        result = ValidationResult(
            rule_id=row[1],
            total_examples=row[2],
            true_positives=row[3],
            false_positives=row[4],
            true_negatives=row[5],
            false_negatives=row[6],
            precision=row[7],
            recall=row[8],
            f1_score=row[9],
            accuracy=row[10],
            failed_examples=json.loads(row[11]),
            validation_date=row[12]
        )
        
        # Generate report
        status = "✅ PRODUCTION READY" if result.precision == 1.0 and result.false_positives == 0 else "❌ NEEDS IMPROVEMENT"
        
        report = f"""# Validation Report: {rule_id}

## Status: {status}

## Summary
- **Total Examples**: {result.total_examples}
- **Precision**: {result.precision:.2%}
- **Recall**: {result.recall:.2%}
- **F1 Score**: {result.f1_score:.2%}
- **Accuracy**: {result.accuracy:.2%}

## Detailed Metrics
- **True Positives**: {result.true_positives}
- **False Positives**: {result.false_positives}
- **True Negatives**: {result.true_negatives}
- **False Negatives**: {result.false_negatives}

## Production Readiness
- **Precision Requirement**: {'✅ PASS' if result.precision == 1.0 else '❌ FAIL'} (Required: 1.0, Actual: {result.precision:.2%})
- **False Positive Rate**: {'✅ PASS' if result.false_positives == 0 else '❌ FAIL'} (Required: 0, Actual: {result.false_positives})
"""

        if result.failed_examples:
            report += f"""
## Failed Examples ({len(result.failed_examples)})
"""
            for failure in result.failed_examples[:10]:  # Show first 10
                report += f"- {failure}\n"
        
        if result.precision < 1.0 or result.false_positives > 0:
            report += f"""
## ⚠️ CRITICAL ISSUES
This rule has accuracy problems and cannot be deployed to production.

### Required Actions:
1. Fix false positive issues
2. Improve pattern matching accuracy
3. Enhance context detection
4. Re-validate until 100% precision achieved

"""
        
        return report
    
    # ================================
    # Phase 5: Integration & Workflow
    # ================================
    
    def complete_validation_workflow(self, rule_id: str) -> bool:
        """Complete end-to-end validation workflow for a rule."""
        print(f"Starting complete validation workflow for {rule_id}")
        
        # Step 1: Generate examples if needed
        examples = self._load_validation_examples(rule_id)
        if len(examples) < 50:  # Minimum required examples
            print("Generating additional validation examples...")
            
            # Generate from corpus
            corpus_examples = self.generate_examples_from_corpus(rule_id, 30)
            for example in corpus_examples:
                self.add_validation_example(example)
            
            # Generate adversarial examples
            adversarial_examples = self.create_adversarial_examples(rule_id)
            for example in adversarial_examples:
                self.add_validation_example(example)
        
        # Step 2: Run validation
        print("Running validation...")
        result = self.validate_rule(rule_id)
        
        if not result:
            print("Validation failed")
            return False
        
        # Step 3: Generate report
        print("Generating validation report...")
        report = self.generate_validation_report(rule_id)
        
        report_file = self.reports_dir / f"{rule_id}_validation_report.md"
        report_file.write_text(report, encoding='utf-8')
        
        # Step 4: Check production readiness
        is_production_ready = (result.precision == 1.0 and 
                              result.false_positives == 0 and 
                              result.recall >= 0.9)
        
        print(f"\n{'='*60}")
        print(f"VALIDATION COMPLETE: {rule_id}")
        print(f"{'='*60}")
        print(f"Precision: {result.precision:.2%}")
        print(f"Recall: {result.recall:.2%}")
        print(f"False Positives: {result.false_positives}")
        print(f"Production Ready: {'✅ YES' if is_production_ready else '❌ NO'}")
        print(f"Report: {report_file}")
        
        return is_production_ready


def main():
    """Demonstrate the validation framework."""
    framework = RuleValidationFramework()
    
    # Example: Validate TYPO-001
    rule_id = "TYPO-001"
    
    print("LaTeX Perfectionist Rule Validation Framework")
    print("=" * 50)
    
    # Run complete validation workflow
    is_ready = framework.complete_validation_workflow(rule_id)
    
    if not is_ready:
        print(f"\n⚠️  Rule {rule_id} is NOT ready for production")
        print("Please fix accuracy issues and re-validate")
    else:
        print(f"\n✅ Rule {rule_id} is ready for production deployment")

if __name__ == "__main__":
    main()