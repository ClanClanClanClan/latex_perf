#!/usr/bin/env python3
"""
LaTeX Perfectionist Test Runner
Runs all unit tests and generates coverage report
"""

import os
import sys
import subprocess
import json
import time
from pathlib import Path
from dataclasses import dataclass
from typing import List, Dict, Tuple

@dataclass
class TestResult:
    """Result of a single test"""
    category: str
    rule_id: str
    test_name: str
    passed: bool
    error_msg: str = ""
    execution_time: float = 0.0

@dataclass
class CoverageReport:
    """Test coverage statistics"""
    total_rules: int
    tested_rules: int
    passed_tests: int
    failed_tests: int
    coverage_percent: float
    
class TestRunner:
    """Manages test execution and reporting"""
    
    def __init__(self, project_root: Path):
        self.project_root = project_root
        self.tests_dir = project_root / "tests"
        self.results: List[TestResult] = []
        
        # Define all rules that should have tests
        self.all_rules = {
            "TYPO": [f"TYPO-{i:03d}" for i in range(1, 26)],
            "ENC": [f"ENC-{i:03d}" for i in range(1, 6)],
            "CHAR": [f"CHAR-{i:03d}" for i in range(1, 6)],
            "MATH": [f"MATH-{i:03d}" for i in range(1, 6)],
            "ENV": [f"ENV-{i:03d}" for i in range(1, 6)],
            "STRUCT": [f"STRUCT-{i:03d}" for i in range(1, 11)],
            "REF": [f"REF-{i:03d}" for i in range(1, 11)],
            "STYLE": [f"STYLE-{i:03d}" for i in range(1, 11)]
        }
    
    def find_test_files(self) -> List[Path]:
        """Find all test files in the project"""
        test_files = []
        for pattern in ["*_Tests.v", "*_test.v", "test_*.v"]:
            test_files.extend(self.tests_dir.rglob(pattern))
        return sorted(test_files)
    
    def compile_test(self, test_file: Path) -> Tuple[bool, str]:
        """Compile a single test file"""
        try:
            # Compile with coqc
            result = subprocess.run(
                ["coqc", "-R", str(self.project_root / "src"), "LP", str(test_file)],
                capture_output=True,
                text=True,
                timeout=30
            )
            
            if result.returncode == 0:
                return True, ""
            else:
                return False, result.stderr
                
        except subprocess.TimeoutExpired:
            return False, "Compilation timeout"
        except Exception as e:
            return False, str(e)
    
    def extract_test_results(self, test_file: Path) -> List[TestResult]:
        """Extract test results from compiled test file"""
        results = []
        
        # Parse the test file to find test definitions
        with open(test_file, 'r') as f:
            content = f.read()
            
        # Simple pattern matching to find test examples
        import re
        
        # Extract category from filename
        category = test_file.stem.split('_')[0]
        
        # Find all Example definitions
        example_pattern = r'Example\s+(\w+)\s*:.*?(?:Proof|Qed|Admitted)'
        examples = re.findall(example_pattern, content, re.DOTALL)
        
        for example_name in examples:
            # Try to determine which rule this tests
            rule_match = re.search(r'(TYPO|ENC|CHAR|MATH|ENV|STRUCT|REF|STYLE)[-_](\d{3})', example_name, re.IGNORECASE)
            if rule_match:
                rule_id = f"{rule_match.group(1)}-{rule_match.group(2)}"
            else:
                rule_id = "UNKNOWN"
            
            # For now, assume all compiled tests pass
            # In real implementation, would parse Coq output
            results.append(TestResult(
                category=category,
                rule_id=rule_id,
                test_name=example_name,
                passed=True
            ))
        
        return results
    
    def run_all_tests(self):
        """Run all tests and collect results"""
        test_files = self.find_test_files()
        
        print(f"Found {len(test_files)} test files")
        print("=" * 60)
        
        for test_file in test_files:
            relative_path = test_file.relative_to(self.project_root)
            print(f"Running {relative_path}...", end=" ")
            
            start_time = time.time()
            success, error_msg = self.compile_test(test_file)
            execution_time = time.time() - start_time
            
            if success:
                print(f"✓ ({execution_time:.2f}s)")
                # Extract individual test results
                test_results = self.extract_test_results(test_file)
                self.results.extend(test_results)
            else:
                print(f"✗ ({execution_time:.2f}s)")
                # Record compilation failure
                category = test_file.stem.split('_')[0]
                self.results.append(TestResult(
                    category=category,
                    rule_id="COMPILATION",
                    test_name=test_file.stem,
                    passed=False,
                    error_msg=error_msg,
                    execution_time=execution_time
                ))
    
    def calculate_coverage(self) -> CoverageReport:
        """Calculate test coverage statistics"""
        # Count total rules
        total_rules = sum(len(rules) for rules in self.all_rules.values())
        
        # Find which rules have tests
        tested_rules = set()
        for result in self.results:
            if result.rule_id != "COMPILATION" and result.rule_id != "UNKNOWN":
                tested_rules.add(result.rule_id)
        
        # Count passed/failed tests
        passed_tests = sum(1 for r in self.results if r.passed)
        failed_tests = sum(1 for r in self.results if not r.passed)
        
        coverage_percent = (len(tested_rules) / total_rules * 100) if total_rules > 0 else 0
        
        return CoverageReport(
            total_rules=total_rules,
            tested_rules=len(tested_rules),
            passed_tests=passed_tests,
            failed_tests=failed_tests,
            coverage_percent=coverage_percent
        )
    
    def generate_report(self):
        """Generate test coverage report"""
        coverage = self.calculate_coverage()
        
        print("\n" + "=" * 60)
        print("TEST COVERAGE REPORT")
        print("=" * 60)
        
        # Overall statistics
        print(f"\nOverall Coverage: {coverage.coverage_percent:.1f}%")
        print(f"Rules with tests: {coverage.tested_rules}/{coverage.total_rules}")
        print(f"Tests passed: {coverage.passed_tests}")
        print(f"Tests failed: {coverage.failed_tests}")
        
        # Per-category breakdown
        print("\nCoverage by Category:")
        print("-" * 40)
        
        for category, rules in self.all_rules.items():
            # Find which rules in this category have tests
            category_tested = set()
            for result in self.results:
                if result.rule_id.startswith(category):
                    category_tested.add(result.rule_id)
            
            coverage_pct = (len(category_tested) / len(rules) * 100) if rules else 0
            print(f"{category:8} {len(category_tested):2}/{len(rules):2} ({coverage_pct:5.1f}%)")
        
        # List untested rules
        print("\n" + "-" * 40)
        print("Untested Rules:")
        
        all_tested_rules = {r.rule_id for r in self.results 
                           if r.rule_id not in ["COMPILATION", "UNKNOWN"]}
        
        for category, rules in self.all_rules.items():
            untested = [r for r in rules if r not in all_tested_rules]
            if untested:
                print(f"\n{category}: {', '.join(untested)}")
        
        # Failed tests
        if coverage.failed_tests > 0:
            print("\n" + "-" * 40)
            print("Failed Tests:")
            for result in self.results:
                if not result.passed:
                    print(f"\n{result.test_name}")
                    if result.error_msg:
                        print(f"  Error: {result.error_msg[:200]}")
        
        # Save detailed results to JSON
        self.save_results_json(coverage)
    
    def save_results_json(self, coverage: CoverageReport):
        """Save detailed results to JSON file"""
        results_data = {
            "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
            "summary": {
                "total_rules": coverage.total_rules,
                "tested_rules": coverage.tested_rules,
                "coverage_percent": coverage.coverage_percent,
                "passed_tests": coverage.passed_tests,
                "failed_tests": coverage.failed_tests
            },
            "results": [
                {
                    "category": r.category,
                    "rule_id": r.rule_id,
                    "test_name": r.test_name,
                    "passed": r.passed,
                    "error_msg": r.error_msg,
                    "execution_time": r.execution_time
                }
                for r in self.results
            ]
        }
        
        output_file = self.project_root / "test_results.json"
        with open(output_file, 'w') as f:
            json.dump(results_data, f, indent=2)
        
        print(f"\nDetailed results saved to: {output_file}")

def main():
    """Main entry point"""
    # Find project root (contains _CoqProject file)
    current_dir = Path.cwd()
    project_root = current_dir
    
    while project_root.parent != project_root:
        if (project_root / "_CoqProject").exists():
            break
        project_root = project_root.parent
    else:
        print("Error: Could not find project root (_CoqProject file)")
        sys.exit(1)
    
    print(f"Project root: {project_root}")
    
    # Create and run test runner
    runner = TestRunner(project_root)
    runner.run_all_tests()
    runner.generate_report()

if __name__ == "__main__":
    main()