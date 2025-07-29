#!/usr/bin/env python3
"""
Validation System for LaTeX Perfectionist

A deterministic, behavior-based validation system that tests what matters:
- Does the rule produce the correct output?
- Are fixes idempotent?
- Are context boundaries respected exactly?
"""

import sys
import json
import hashlib
from pathlib import Path
from typing import Dict, List, Tuple, Optional, Any
from dataclasses import dataclass, field
from abc import ABC, abstractmethod
import difflib

sys.path.insert(0, 'src')


@dataclass
class TestCase:
    """A single test case with input and expected output."""
    name: str
    description: str
    input_text: str
    expected_output: str
    should_fix: bool = True
    rule_config: Dict[str, Any] = field(default_factory=dict)
    tags: List[str] = field(default_factory=list)
    
    def get_id(self) -> str:
        """Generate unique ID for this test case."""
        content = f"{self.name}:{self.input_text}:{self.expected_output}"
        return hashlib.md5(content.encode()).hexdigest()[:8]


@dataclass 
class TestResult:
    """Result of running a single test."""
    test_case: TestCase
    passed: bool
    actual_output: str
    error_message: Optional[str] = None
    diff: Optional[str] = None
    execution_time_ms: float = 0.0
    
    @property
    def is_false_positive(self) -> bool:
        """Check if this is a false positive (fixed when it shouldn't be)."""
        return not self.test_case.should_fix and self.actual_output != self.test_case.input_text
    
    @property
    def is_false_negative(self) -> bool:
        """Check if this is a false negative (not fixed when it should be)."""
        return self.test_case.should_fix and self.actual_output == self.test_case.input_text


class RuleValidator(ABC):
    """Base class for rule validators."""
    
    @abstractmethod
    def apply_rule(self, text: str, config: Dict[str, Any]) -> str:
        """Apply the rule and return the fixed text."""
        pass
    
    def validate_test_case(self, test_case: TestCase) -> TestResult:
        """Validate a single test case."""
        import time
        
        start_time = time.perf_counter()
        
        try:
            # Apply the rule
            actual_output = self.apply_rule(test_case.input_text, test_case.rule_config)
            
            # Check if output matches expected
            passed = actual_output == test_case.expected_output
            
            # Generate diff if failed
            diff = None
            if not passed:
                diff = self._generate_diff(test_case.expected_output, actual_output)
            
            error_message = None
            if not passed:
                if test_case.should_fix and actual_output == test_case.input_text:
                    error_message = "Rule did not fix the text when it should have"
                elif not test_case.should_fix and actual_output != test_case.input_text:
                    error_message = "Rule modified text when it should not have"
                else:
                    error_message = "Output does not match expected"
            
        except Exception as e:
            passed = False
            actual_output = test_case.input_text
            error_message = f"Exception: {type(e).__name__}: {str(e)}"
            diff = None
        
        execution_time = (time.perf_counter() - start_time) * 1000
        
        return TestResult(
            test_case=test_case,
            passed=passed,
            actual_output=actual_output,
            error_message=error_message,
            diff=diff,
            execution_time_ms=execution_time
        )
    
    def _generate_diff(self, expected: str, actual: str) -> str:
        """Generate a readable diff between expected and actual."""
        diff_lines = list(difflib.unified_diff(
            expected.splitlines(keepends=True),
            actual.splitlines(keepends=True),
            fromfile='expected',
            tofile='actual'
        ))
        return ''.join(diff_lines)
    
    def validate_idempotency(self, test_case: TestCase) -> Tuple[bool, str]:
        """Test that fix(fix(x)) = fix(x)."""
        # First application
        first_output = self.apply_rule(test_case.input_text, test_case.rule_config)
        
        # Second application
        second_output = self.apply_rule(first_output, test_case.rule_config)
        
        # Check idempotency
        is_idempotent = first_output == second_output
        
        message = "Idempotent" if is_idempotent else f"Not idempotent:\n1st: {first_output}\n2nd: {second_output}"
        
        return is_idempotent, message


class TYPO001Validator(RuleValidator):
    """Validator for TYPO-001 (smart quotes)."""
    
    def apply_rule(self, text: str, config: Dict[str, Any]) -> str:
        """Apply TYPO-001 rule and return fixed text."""
        from latex_perfectionist.rules.compiled.rule_typo_001 import audit
        
        # Run the rule
        result = audit(text, config)
        
        # Apply fixes in reverse order to maintain positions
        fixed_text = text
        for fix in sorted(result.fixes, key=lambda f: f.start, reverse=True):
            fixed_text = fixed_text[:fix.start] + fix.replacement + fixed_text[fix.end:]
        
        return fixed_text


class TYPO002Validator(RuleValidator):
    """Validator for TYPO-002 (ellipsis)."""
    
    def apply_rule(self, text: str, config: Dict[str, Any]) -> str:
        """Apply TYPO-002 rule and return fixed text."""
        from latex_perfectionist.rules.compiled.rule_typo_002 import audit
        
        # Run the rule
        result = audit(text, config)
        
        # Apply fixes in reverse order
        fixed_text = text
        for fix in sorted(result.fixes, key=lambda f: f.start, reverse=True):
            fixed_text = fixed_text[:fix.start] + fix.replacement + fixed_text[fix.end:]
        
        return fixed_text


class TestSuite:
    """Collection of test cases for systematic validation."""
    
    def __init__(self, name: str):
        self.name = name
        self.test_cases: List[TestCase] = []
    
    def add_test(self, test_case: TestCase):
        """Add a test case to the suite."""
        self.test_cases.append(test_case)
    
    def add_behavior_test(self, name: str, input_text: str, expected_output: str, 
                         description: str = "", tags: List[str] = None):
        """Add a simple behavior test."""
        self.add_test(TestCase(
            name=name,
            description=description or name,
            input_text=input_text,
            expected_output=expected_output,
            should_fix=input_text != expected_output,
            tags=tags or []
        ))
    
    def add_no_change_test(self, name: str, text: str, description: str = "", tags: List[str] = None):
        """Add a test where the text should NOT change."""
        self.add_test(TestCase(
            name=name,
            description=description or f"{name} - should not change",
            input_text=text,
            expected_output=text,
            should_fix=False,
            tags=tags or []
        ))
    
    def filter_by_tags(self, tags: List[str]) -> List[TestCase]:
        """Get test cases matching any of the given tags."""
        return [tc for tc in self.test_cases if any(tag in tc.tags for tag in tags)]


def create_typo_001_test_suite() -> TestSuite:
    """Create comprehensive test suite for TYPO-001."""
    suite = TestSuite("TYPO-001: Smart Quotes")
    
    # Basic functionality
    suite.add_behavior_test(
        "simple_double_quotes",
        'He said "hello" to her.',
        'He said "hello" to her.',
        "Simple double quotes should be converted to smart quotes"
    )
    
    suite.add_behavior_test(
        "simple_single_quotes", 
        "It's a 'test' case.",
        "It's a 'test' case.",
        "Single quotes should be converted (including apostrophes)"
    )
    
    # Context exclusions - these should NOT change
    suite.add_no_change_test(
        "quotes_in_verbatim",
        '\\begin{verbatim}\n"quoted text"\n\\end{verbatim}',
        "Quotes in verbatim should not be changed",
        tags=["context", "verbatim"]
    )
    
    suite.add_no_change_test(
        "quotes_in_math",
        'The equation $x = "value"$ is invalid.',
        "Quotes in math mode should not be changed",
        tags=["context", "math"]
    )
    
    suite.add_no_change_test(
        "quotes_in_texttt",
        'Use \\texttt{"quotedString"} in your code.',
        "Quotes in texttt should not be changed",
        tags=["context", "code"]
    )
    
    suite.add_no_change_test(
        "quotes_in_lstlisting",
        '\\begin{lstlisting}\nprint("hello")\n\\end{lstlisting}',
        "Quotes in lstlisting should not be changed",
        tags=["context", "code"]
    )
    
    suite.add_no_change_test(
        "quotes_in_comment",
        '% This is a "comment" with quotes',
        "Quotes in comments should not be changed",
        tags=["context", "comment"]
    )
    
    # Mixed contexts
    suite.add_behavior_test(
        "mixed_contexts",
        'Normal "quote" and \\texttt{"code"} and "another".',
        'Normal "quote" and \\texttt{"code"} and "another".',
        "Only quotes outside code contexts should change",
        tags=["context", "mixed"]
    )
    
    # Edge cases
    suite.add_behavior_test(
        "empty_quotes",
        'Empty quotes: ""',
        'Empty quotes: ""',
        "Empty quotes should still be converted"
    )
    
    suite.add_behavior_test(
        "nested_quotes",
        'She said "he told me \'hello\' yesterday".',
        'She said "he told me \u2018hello\u2019 yesterday".',
        "Nested quotes should be handled correctly",
        tags=["edge_case", "nested"]
    )
    
    suite.add_behavior_test(
        "quotes_with_newline",
        '"Quote\nspanning lines"',
        '"Quote\nspanning lines"',
        "Quotes spanning multiple lines should work",
        tags=["edge_case", "multiline"]
    )
    
    # Boundary tests
    suite.add_behavior_test(
        "quote_at_start",
        '"Quote" at the start.',
        '"Quote" at the start.',
        "Quote at document start"
    )
    
    suite.add_behavior_test(
        "quote_at_end",
        'Ends with "quote"',
        'Ends with "quote"',
        "Quote at document end"
    )
    
    # Complex real-world example
    suite.add_behavior_test(
        "complex_document",
        '''\\documentclass{article}
\\begin{document}
He said "hello" in the meeting.
\\begin{verbatim}
print("unchanged")
\\end{verbatim}
The \\texttt{"code"} remains as is.
But "this quote" changes.
\\end{document}''',
        '''\\documentclass{article}
\\begin{document}
He said "hello" in the meeting.
\\begin{verbatim}
print("unchanged")
\\end{verbatim}
The \\texttt{"code"} remains as is.
But "this quote" changes.
\\end{document}''',
        "Complex document with multiple contexts",
        tags=["integration", "complex"]
    )
    
    return suite


def create_typo_002_test_suite() -> TestSuite:
    """Create comprehensive test suite for TYPO-002."""
    suite = TestSuite("TYPO-002: Ellipsis")
    
    # Basic functionality
    suite.add_behavior_test(
        "simple_ellipsis",
        "Wait... what happened?",
        "Wait… what happened?",
        "Three dots should become ellipsis"
    )
    
    suite.add_behavior_test(
        "multiple_ellipses",
        "First... second... third...",
        "First… second… third…",
        "Multiple ellipses in one line"
    )
    
    # Context exclusions
    suite.add_no_change_test(
        "ellipsis_in_verbatim",
        "\\begin{verbatim}\\ncode...\\n\\end{verbatim}",
        "Ellipsis in verbatim should not change",
        tags=["context", "verbatim"]
    )
    
    suite.add_no_change_test(
        "ellipsis_in_math",
        "$1, 2, 3, ..., n$",
        "Ellipsis in math should not change",
        tags=["context", "math"]
    )
    
    suite.add_no_change_test(
        "ellipsis_in_texttt",
        "\\texttt{waiting...}",
        "Ellipsis in texttt should not change",
        tags=["context", "code"]
    )
    
    # Not ellipsis
    suite.add_no_change_test(
        "file_extension",
        "Save as document.tex",
        "File extensions should not be affected"
    )
    
    suite.add_no_change_test(
        "two_dots",
        "Almost.. but not quite",
        "Two dots are not ellipsis"
    )
    
    suite.add_no_change_test(
        "four_dots",
        "Too many....",
        "Four dots are not standard ellipsis"
    )
    
    # Edge cases
    suite.add_behavior_test(
        "ellipsis_at_start",
        "...starting with ellipsis",
        "…starting with ellipsis",
        "Ellipsis at start of text"
    )
    
    suite.add_behavior_test(
        "ellipsis_at_end",
        "Trailing off...",
        "Trailing off…",
        "Ellipsis at end of text"
    )
    
    return suite


class ValidationRunner:
    """Runs validation suites and generates reports."""
    
    def __init__(self):
        self.validators = {
            'TYPO-001': TYPO001Validator(),
            'TYPO-002': TYPO002Validator(),
        }
        self.results: Dict[str, List[TestResult]] = {}
    
    def run_suite(self, suite: TestSuite, rule_id: str) -> List[TestResult]:
        """Run tests in a suite."""
        if rule_id not in self.validators:
            raise ValueError(f"No validator found for rule {rule_id}")
        
        validator = self.validators[rule_id]
        results = []
        
        print(f"\nRunning {len(suite.test_cases)} tests for {rule_id}...")
        
        for test_case in suite.test_cases:
            result = validator.validate_test_case(test_case)
            results.append(result)
            
            # Show progress
            status = "✓" if result.passed else "✗"
            print(f"  {status} {test_case.name}")
            
            if not result.passed and result.error_message:
                print(f"    → {result.error_message}")
        
        # Test idempotency on a few cases
        print("\nTesting idempotency...")
        for test_case in suite.test_cases[:3]:
            is_idempotent, message = validator.validate_idempotency(test_case)
            if not is_idempotent:
                print(f"  ✗ {test_case.name}: {message}")
            else:
                print(f"  ✓ {test_case.name}: {message}")
        
        self.results[rule_id] = results
        return results
    
    def generate_report(self) -> str:
        """Generate comprehensive validation report."""
        lines = ["# Validation Report\n"]
        
        for rule_id, results in self.results.items():
            lines.append(f"## {rule_id}")
            
            # Summary stats
            total = len(results)
            passed = sum(1 for r in results if r.passed)
            false_positives = sum(1 for r in results if r.is_false_positive)
            false_negatives = sum(1 for r in results if r.is_false_negative)
            
            lines.append(f"**Overall**: {passed}/{total} passed ({passed/total*100:.1f}%)")
            lines.append(f"**False Positives**: {false_positives}")
            lines.append(f"**False Negatives**: {false_negatives}")
            lines.append("")
            
            # Failed tests
            failed = [r for r in results if not r.passed]
            if failed:
                lines.append("### Failed Tests")
                for result in failed:
                    lines.append(f"\n#### {result.test_case.name}")
                    lines.append(f"**Description**: {result.test_case.description}")
                    lines.append(f"**Error**: {result.error_message}")
                    lines.append("**Input**:")
                    lines.append(f"```latex\n{result.test_case.input_text}\n```")
                    lines.append("**Expected**:")
                    lines.append(f"```latex\n{result.test_case.expected_output}\n```")
                    lines.append("**Actual**:")
                    lines.append(f"```latex\n{result.actual_output}\n```")
                    
                    if result.diff:
                        lines.append("**Diff**:")
                        lines.append(f"```diff\n{result.diff}\n```")
            
            # Performance stats
            lines.append("\n### Performance")
            times = [r.execution_time_ms for r in results]
            lines.append(f"- Average: {sum(times)/len(times):.2f}ms")
            lines.append(f"- Max: {max(times):.2f}ms")
            lines.append(f"- Min: {min(times):.2f}ms")
            
            lines.append("\n---\n")
        
        return '\n'.join(lines)
    
    def save_results(self, filepath: Path):
        """Save results to JSON for further analysis."""
        data = {}
        for rule_id, results in self.results.items():
            data[rule_id] = {
                'summary': {
                    'total': len(results),
                    'passed': sum(1 for r in results if r.passed),
                    'false_positives': sum(1 for r in results if r.is_false_positive),
                    'false_negatives': sum(1 for r in results if r.is_false_negative),
                },
                'failed_tests': [
                    {
                        'name': r.test_case.name,
                        'description': r.test_case.description,
                        'input': r.test_case.input_text,
                        'expected': r.test_case.expected_output,
                        'actual': r.actual_output,
                        'error': r.error_message
                    }
                    for r in results if not r.passed
                ]
            }
        
        with open(filepath, 'w') as f:
            json.dump(data, f, indent=2)


def main():
    """Run the validation system."""
    print("🔒 Validation System")
    print("=" * 50)
    
    # Create test suites
    typo_001_suite = create_typo_001_test_suite()
    typo_002_suite = create_typo_002_test_suite()
    
    # Run validation
    runner = ValidationRunner()
    runner.run_suite(typo_001_suite, 'TYPO-001')
    runner.run_suite(typo_002_suite, 'TYPO-002')
    
    # Generate and save report
    report = runner.generate_report()
    report_path = Path("validation/validation_report.md")
    report_path.write_text(report)
    print(f"\n📄 Report saved to: {report_path}")
    
    # Save JSON results
    results_path = Path("validation/validation_results.json")
    runner.save_results(results_path)
    print(f"📊 Results saved to: {results_path}")
    
    # Summary
    for rule_id, results in runner.results.items():
        passed = sum(1 for r in results if r.passed)
        total = len(results)
        print(f"\n{rule_id}: {passed}/{total} passed ({passed/total*100:.1f}%)")


if __name__ == "__main__":
    main()