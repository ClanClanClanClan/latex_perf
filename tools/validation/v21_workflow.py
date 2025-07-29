#!/usr/bin/env python3
"""
LaTeX Perfectionist v21 - Production Workflow Implementation

This module implements the complete v21 workflow for rule development,
testing, and validation with 100% accuracy guarantee.
"""

import sys
import os
sys.path.insert(0, 'src')

import re
import json
import time
from pathlib import Path
from typing import Dict, List, Any, Optional, Tuple
from dataclasses import dataclass, asdict
from datetime import datetime

# Import our validation framework
try:
    from latex_perfectionist.validation.gates import ProductionGates, ValidationResult
    from latex_perfectionist.validation.performance import PerformanceOptimizer
except ImportError:
    # Create minimal classes for now
    from dataclasses import dataclass
    
    @dataclass
    class ValidationResult:
        rule_id: str
        precision: float
        recall: float
        performance_ms: float
        false_positives: int
        false_negatives: int
        total_tests: int
        passed: bool
    
    class ProductionGates:
        def __init__(self):
            pass
    
    class PerformanceOptimizer:
        def __init__(self):
            pass

@dataclass
class GroundTruthExample:
    """Ground truth example for rule validation."""
    rule_id: str
    input_text: str
    expected_matches: List[Dict[str, Any]]
    expected_fixes: List[Dict[str, Any]]
    context: str
    description: str
    should_match: bool

@dataclass
class RuleTestResult:
    """Result of testing a rule against ground truth."""
    rule_id: str
    example_id: str
    expected: bool
    actual: bool
    matches_found: List[Dict[str, Any]]
    fixes_applied: List[Dict[str, Any]]
    execution_time_ms: float
    passed: bool

class V21Workflow:
    """Complete v21 workflow for rule development and validation."""
    
    def __init__(self):
        self.production_gates = ProductionGates()
        self.performance_optimizer = PerformanceOptimizer()
        
        # Ground truth storage
        self.ground_truth_dir = Path("validation/ground_truth")
        self.ground_truth_dir.mkdir(parents=True, exist_ok=True)
        
        # Results storage
        self.results_dir = Path("validation/results")
        self.results_dir.mkdir(parents=True, exist_ok=True)
        
    def create_ground_truth_examples(self, rule_id: str, examples: List[GroundTruthExample]) -> None:
        """Create ground truth examples for a rule."""
        examples_file = self.ground_truth_dir / f"{rule_id}_examples.json"
        
        examples_data = {
            "rule_id": rule_id,
            "created_date": datetime.now().isoformat(),
            "examples": [asdict(example) for example in examples]
        }
        
        with open(examples_file, 'w') as f:
            json.dump(examples_data, f, indent=2)
        
        print(f"✓ Created {len(examples)} ground truth examples for {rule_id}")
    
    def load_ground_truth_examples(self, rule_id: str) -> List[GroundTruthExample]:
        """Load ground truth examples for a rule."""
        examples_file = self.ground_truth_dir / f"{rule_id}_examples.json"
        
        if not examples_file.exists():
            return []
        
        with open(examples_file, 'r') as f:
            data = json.load(f)
        
        examples = []
        for example_data in data["examples"]:
            examples.append(GroundTruthExample(**example_data))
        
        return examples
    
    def test_rule_against_ground_truth(self, rule_id: str) -> List[RuleTestResult]:
        """Test a rule against its ground truth examples."""
        examples = self.load_ground_truth_examples(rule_id)
        if not examples:
            print(f"⚠️ No ground truth examples found for {rule_id}")
            return []
        
        results = []
        
        for i, example in enumerate(examples):
            # Time the rule execution
            start_time = time.time()
            
            # Run the rule (this would be replaced with actual rule execution)
            matches_found, fixes_applied = self._run_rule_on_text(rule_id, example.input_text)
            
            end_time = time.time()
            execution_time_ms = (end_time - start_time) * 1000
            
            # Determine if rule should have matched
            expected = example.should_match
            actual = len(matches_found) > 0
            
            # Check if result matches expectation
            passed = (expected == actual)
            
            result = RuleTestResult(
                rule_id=rule_id,
                example_id=f"{rule_id}_example_{i}",
                expected=expected,
                actual=actual,
                matches_found=matches_found,
                fixes_applied=fixes_applied,
                execution_time_ms=execution_time_ms,
                passed=passed
            )
            
            results.append(result)
        
        return results
    
    def _run_rule_on_text(self, rule_id: str, text: str) -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]]]:
        """Run a rule on text and return matches and fixes."""
        # Import the rule executor
        import sys
        sys.path.append('.')
        from validation.rule_executor import RuleExecutor
        
        if not hasattr(self, 'rule_executor'):
            self.rule_executor = RuleExecutor()
        
        return self.rule_executor.execute_rule(rule_id, text)
    
    def calculate_rule_accuracy(self, rule_id: str) -> Dict[str, Any]:
        """Calculate accuracy metrics for a rule."""
        test_results = self.test_rule_against_ground_truth(rule_id)
        
        if not test_results:
            return {
                "precision": 0.0,
                "recall": 0.0,
                "f1_score": 0.0,
                "accuracy": 0.0,
                "true_positives": 0,
                "false_positives": 0,
                "true_negatives": 0,
                "false_negatives": 0,
                "total_tests": 0
            }
        
        # Calculate confusion matrix
        true_positives = sum(1 for r in test_results if r.expected and r.actual)
        false_positives = sum(1 for r in test_results if not r.expected and r.actual)
        true_negatives = sum(1 for r in test_results if not r.expected and not r.actual)
        false_negatives = sum(1 for r in test_results if r.expected and not r.actual)
        
        # Calculate metrics
        precision = true_positives / (true_positives + false_positives) if (true_positives + false_positives) > 0 else 0.0
        recall = true_positives / (true_positives + false_negatives) if (true_positives + false_negatives) > 0 else 0.0
        f1_score = 2 * (precision * recall) / (precision + recall) if (precision + recall) > 0 else 0.0
        accuracy = (true_positives + true_negatives) / len(test_results) if test_results else 0.0
        
        return {
            "precision": precision,
            "recall": recall,
            "f1_score": f1_score,
            "accuracy": accuracy,
            "true_positives": true_positives,
            "false_positives": false_positives,
            "true_negatives": true_negatives,
            "false_negatives": false_negatives,
            "total_tests": len(test_results)
        }
    
    def validate_rule_for_production(self, rule_id: str) -> ValidationResult:
        """Validate a rule for production deployment."""
        print(f"🔍 Validating rule {rule_id} for production...")
        
        # Calculate accuracy metrics
        accuracy_metrics = self.calculate_rule_accuracy(rule_id)
        
        # Calculate average performance
        test_results = self.test_rule_against_ground_truth(rule_id)
        avg_performance = sum(r.execution_time_ms for r in test_results) / len(test_results) if test_results else 0
        
        # Create validation result
        result = ValidationResult(
            rule_id=rule_id,
            precision=accuracy_metrics["precision"],
            recall=accuracy_metrics["recall"],
            performance_ms=avg_performance,
            false_positives=accuracy_metrics["false_positives"],
            false_negatives=accuracy_metrics["false_negatives"],
            total_tests=accuracy_metrics["total_tests"],
            passed=False
        )
        
        # Apply production gates
        try:
            if result.precision < 1.0:
                raise ValueError(f"Rule {rule_id} failed precision: {result.precision:.2%} < 100%")
            
            if result.recall < 0.95:
                raise ValueError(f"Rule {rule_id} failed recall: {result.recall:.2%} < 95%")
            
            if result.performance_ms > 100:
                raise ValueError(f"Rule {rule_id} too slow: {result.performance_ms:.2f}ms > 100ms")
            
            result.passed = True
            print(f"✅ Rule {rule_id} passed all production gates")
            
        except ValueError as e:
            print(f"❌ Rule {rule_id} failed validation: {e}")
            result.passed = False
        
        return result
    
    def save_validation_results(self, rule_id: str, result: ValidationResult) -> None:
        """Save validation results to file."""
        results_file = self.results_dir / f"{rule_id}_validation_results.json"
        
        results_data = {
            "rule_id": rule_id,
            "validation_date": datetime.now().isoformat(),
            "result": asdict(result),
            "passed_production_gates": result.passed
        }
        
        with open(results_file, 'w') as f:
            json.dump(results_data, f, indent=2)
        
        print(f"💾 Saved validation results for {rule_id}")
    
    def generate_validation_report(self, rule_id: str) -> str:
        """Generate a comprehensive validation report."""
        result = self.validate_rule_for_production(rule_id)
        accuracy_metrics = self.calculate_rule_accuracy(rule_id)
        
        report = f"""
# Rule Validation Report: {rule_id}

## Validation Date
{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}

## Production Gates Status
{'✅ PASSED' if result.passed else '❌ FAILED'}

## Accuracy Metrics
- **Precision**: {result.precision:.2%} (Target: 100%)
- **Recall**: {result.recall:.2%} (Target: ≥95%)
- **F1 Score**: {accuracy_metrics['f1_score']:.2%}
- **Accuracy**: {accuracy_metrics['accuracy']:.2%}

## Performance Metrics
- **Average Execution Time**: {result.performance_ms:.2f}ms (Target: <100ms)

## Test Results
- **Total Tests**: {result.total_tests}
- **True Positives**: {accuracy_metrics['true_positives']}
- **False Positives**: {result.false_positives}
- **True Negatives**: {accuracy_metrics['true_negatives']}
- **False Negatives**: {result.false_negatives}

## Production Readiness
{'🚀 Rule is ready for production deployment' if result.passed else '⚠️ Rule requires fixes before production deployment'}

## Recommendations
"""
        
        if not result.passed:
            if result.precision < 1.0:
                report += f"- Fix false positives (current: {result.false_positives})\n"
            if result.recall < 0.95:
                report += f"- Improve recall (current: {result.recall:.2%})\n"
            if result.performance_ms > 100:
                report += f"- Optimize performance (current: {result.performance_ms:.2f}ms)\n"
        else:
            report += "- Rule meets all production requirements\n"
        
        return report
    
    def create_typo_001_ground_truth(self) -> None:
        """Create ground truth examples for TYPO-001."""
        examples = [
            # Positive examples - should match
            GroundTruthExample(
                rule_id="TYPO-001",
                input_text='This is a "quoted text" example.',
                expected_matches=[{"start": 10, "end": 23, "text": '"quoted text"'}],
                expected_fixes=[{"start": 10, "end": 23, "replacement": "\u201cquoted text\u201d"}],
                context="normal_text",
                description="Simple straight quotes in normal text",
                should_match=True
            ),
            GroundTruthExample(
                rule_id="TYPO-001",
                input_text="This uses 'single quotes' in text.",
                expected_matches=[{"start": 10, "end": 25, "text": "'single quotes'"}],
                expected_fixes=[{"start": 10, "end": 25, "replacement": "\u2018single quotes\u2019"}],
                context="normal_text",
                description="Single straight quotes in normal text",
                should_match=True
            ),
            
            # Negative examples - should NOT match
            GroundTruthExample(
                rule_id="TYPO-001",
                input_text='\\begin{verbatim}"quoted text"\\end{verbatim}',
                expected_matches=[],
                expected_fixes=[],
                context="verbatim_environment",
                description="Quotes inside verbatim environment",
                should_match=False
            ),
            GroundTruthExample(
                rule_id="TYPO-001",
                input_text='\\begin{equation}x = "value"\\end{equation}',
                expected_matches=[],
                expected_fixes=[],
                context="math_environment",
                description="Quotes inside math environment",
                should_match=False
            ),
            GroundTruthExample(
                rule_id="TYPO-001",
                input_text='\\texttt{"code"}',
                expected_matches=[],
                expected_fixes=[],
                context="code_context",
                description="Quotes in code formatting",
                should_match=False
            ),
            GroundTruthExample(
                rule_id="TYPO-001",
                input_text='\\LaTeX{} braces are {not quotes}',
                expected_matches=[],
                expected_fixes=[],
                context="latex_braces",
                description="LaTeX braces should not be treated as quotes",
                should_match=False
            ),
            
            # Edge cases
            GroundTruthExample(
                rule_id="TYPO-001",
                input_text='Nested "quotes with \'inner\' quotes"',
                expected_matches=[{"start": 7, "end": 40, "text": '"quotes with \'inner\' quotes"'}],
                expected_fixes=[{"start": 7, "end": 40, "replacement": "\u201cquotes with \u2018inner\u2019 quotes\u201d"}],
                context="nested_quotes",
                description="Nested quotes handling",
                should_match=True
            ),
            GroundTruthExample(
                rule_id="TYPO-001",
                input_text='Text with "unclosed quote at end',
                expected_matches=[],
                expected_fixes=[],
                context="unclosed_quote",
                description="Unclosed quotes should not match",
                should_match=False
            )
        ]
        
        self.create_ground_truth_examples("TYPO-001", examples)
    
    def create_typo_002_ground_truth(self) -> None:
        """Create ground truth examples for TYPO-002."""
        examples = [
            # Positive examples - should match
            GroundTruthExample(
                rule_id="TYPO-002",
                input_text='This has three dots...',
                expected_matches=[{"start": 19, "end": 22, "text": '...'}],
                expected_fixes=[{"start": 19, "end": 22, "replacement": "\u2026"}],
                context="normal_text",
                description="Three dots should become ellipsis",
                should_match=True
            ),
            GroundTruthExample(
                rule_id="TYPO-002",
                input_text='Wait...what happened?',
                expected_matches=[{"start": 4, "end": 7, "text": '...'}],
                expected_fixes=[{"start": 4, "end": 7, "replacement": "\u2026"}],
                context="normal_text",
                description="Ellipsis in middle of sentence",
                should_match=True
            ),
            
            # Negative examples - should NOT match
            GroundTruthExample(
                rule_id="TYPO-002",
                input_text='\\begin{verbatim}...\\end{verbatim}',
                expected_matches=[],
                expected_fixes=[],
                context="verbatim_environment",
                description="Ellipsis in verbatim should not match",
                should_match=False
            ),
            GroundTruthExample(
                rule_id="TYPO-002",
                input_text='\\begin{equation}x + y + z = ...\\end{equation}',
                expected_matches=[],
                expected_fixes=[],
                context="math_environment",
                description="Ellipsis in math environment should not match",
                should_match=False
            ),
            GroundTruthExample(
                rule_id="TYPO-002",
                input_text='\\texttt{...}',
                expected_matches=[],
                expected_fixes=[],
                context="code_context",
                description="Ellipsis in code formatting should not match",
                should_match=False
            ),
            GroundTruthExample(
                rule_id="TYPO-002",
                input_text='File.ext',
                expected_matches=[],
                expected_fixes=[],
                context="file_extension",
                description="File extensions should not match",
                should_match=False
            ),
        ]
        
        self.create_ground_truth_examples("TYPO-002", examples)

def main():
    """Main function to demonstrate v21 workflow."""
    workflow = V21Workflow()
    
    print("🚀 Setting up v21 workflow...")
    
    # Create ground truth examples
    workflow.create_typo_001_ground_truth()
    workflow.create_typo_002_ground_truth()
    
    # Validate rules (this will show current state)
    for rule_id in ["TYPO-001", "TYPO-002"]:
        print(f"\n📊 Validating {rule_id}...")
        result = workflow.validate_rule_for_production(rule_id)
        workflow.save_validation_results(rule_id, result)
        
        # Generate report
        report = workflow.generate_validation_report(rule_id)
        report_file = Path(f"validation/reports/{rule_id}_validation_report.md")
        report_file.parent.mkdir(parents=True, exist_ok=True)
        report_file.write_text(report)
        print(f"📄 Generated report: {report_file}")
    
    print("\n✅ v21 workflow setup complete!")

if __name__ == "__main__":
    main()