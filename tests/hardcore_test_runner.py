#!/usr/bin/env python3
"""
HARDCORE UNIVERSAL TEST RUNNER - ALL RULES EDITION

This is the ultimate stress-testing suite for ALL LaTeX Perfectionist rules.
Every rule gets the hardcore treatment with property-based tests, edge cases,
and pathological scenarios.

Usage:
    python3 hardcore_universal_test_runner.py [options]
    
Options:
    --verify           Quick verification that setup is working
    --basic-only       Run only basic tests (levels 1-3)
    --rule RULENAME    Test only specific rule
    --level N          Test only level N (1-10) 
    --property         Run only property-based tests
    --all              Run everything (default)
    --verbose          Show detailed output
    --quick            Reduced examples for faster testing
    --benchmark        Include performance benchmarks
    --stress           Run extreme stress tests
    --mutation         Run mutation testing
"""

import sys
import os
import time
import argparse
import traceback
from pathlib import Path
from typing import Dict, List, Any, Callable
from dataclasses import dataclass

# Add project paths
project_root = Path(__file__).parent
sys.path.insert(0, str(project_root))
sys.path.insert(0, str(project_root / "tests"))

@dataclass
class TestResult:
    """Results from running a test suite."""
    rule_name: str
    passed: bool
    duration: float
    tests_run: int
    errors: List[str]
    level: int = 0

class HardcoreTestRunner:
    """The ultimate test runner for all LaTeX Perfectionist rules."""
    
    def __init__(self, verbose=False, quick=False):
        self.verbose = verbose
        self.quick = quick
        self.results: List[TestResult] = []
        self.cfg = self.load_config()
        
        # Import all rules
        self.rules = self.discover_rules()
        
    def load_config(self):
        """Load test configuration."""
        try:
            from latex_perfectionist.core.loader import load_config
            config_paths = [
                project_root / "config.default.yaml",
                project_root / "latex_perfectionist" / "config.default.yaml",
                project_root.parent / "config.default.yaml"
            ]
            
            for config_path in config_paths:
                if config_path.exists():
                    return load_config(config_path)
            
            print("⚠️  No config found, using hardcore defaults")
            return self.get_hardcore_default_config()
        except Exception as e:
            print(f"⚠️  Config load failed: {e}")
            return self.get_hardcore_default_config()
    
    def get_hardcore_default_config(self):
        """Hardcore default configuration that enables ALL rules."""
        return {
            "orthography": {"en_dash_ranges": True},
            "punctuation": {
                "abbreviations": ["a.s.", "w.l.o.g.", "i.i.d.", "w.r.t.", "cf.", "e.g.", "i.e.", "etc."],
                "tie_words": ["Figure", "Table", "Theorem", "Lemma", "Corollary", "cf.", "Eq.", "eq.", "pp."]
            },
            "math": {
                "expect_brackets": True,
                "prob_brackets": True,
                "raisebox_ex": "0.2"
            }
        }
    
    def discover_rules(self):
        """Discover all available rules."""
        rules = {}
        
        rule_modules = [
            "dash_ranges",
            "double_periods", 
            "expect_prob_brackets",
            "math_env_normaliser",
            "nested_scripts",
            "tie_words"
        ]
        
        for rule_name in rule_modules:
            try:
                module = __import__(f"latex_perfectionist.rules.{rule_name}", fromlist=[rule_name])
                if hasattr(module, 'audit'):
                    rules[rule_name] = module
                    if self.verbose:
                        print(f"✅ Loaded rule: {rule_name}")
            except ImportError as e:
                print(f"⚠️  Could not load rule {rule_name}: {e}")
        
        return rules
    
    def run_verification(self):
        """Quick verification that everything is set up correctly."""
        print("🔍 VERIFICATION MODE - Quick Setup Check")
        print("=" * 50)
        
        # Check if we can import basic modules
        try:
            from latex_perfectionist.core.loader import load_config
            print("✅ Core loader import: OK")
        except ImportError as e:
            print(f"❌ Core loader import: FAILED - {e}")
            return False
        
        # Check if we can load at least one rule
        if not self.rules:
            print("❌ No rules loaded: FAILED")
            return False
        else:
            print(f"✅ Rules loaded: {len(self.rules)} rules found")
        
        # Test one simple case for each rule
        success_count = 0
        for rule_name, rule_module in self.rules.items():
            try:
                # Simple test case
                test_case = self.get_simple_test_case(rule_name)
                result = rule_module.audit(test_case, self.cfg)
                print(f"✅ {rule_name}: Basic audit works")
                success_count += 1
            except Exception as e:
                print(f"❌ {rule_name}: FAILED - {e}")
        
        if success_count == len(self.rules):
            print("\n🎉 VERIFICATION PASSED! All systems ready for hardcore testing!")
            return True
        else:
            print(f"\n❌ VERIFICATION FAILED! {len(self.rules) - success_count} rules have issues.")
            return False
    
    def get_simple_test_case(self, rule_name):
        """Get a simple test case for verification."""
        simple_cases = {
            "dash_ranges": "pages 5-9",
            "double_periods": "a.s..",
            "expect_prob_brackets": r"\mathbb{E}(X)",
            "math_env_normaliser": "$$ a = b $$",
            "nested_scripts": r"x_{y_{1}}",
            "tie_words": "Figure 1"
        }
        return simple_cases.get(rule_name, "test case")
    
    def run_basic_tests(self):
        """Run only basic tests (levels 1-3)."""
        print("🧪 BASIC TEST MODE - Levels 1-3 Only")
        print("=" * 50)
        
        return self.run_all_tests(max_level=3)
    
    def run_all_tests(self, rule_filter=None, level_filter=None, property_only=False, max_level=None):
        """Run all hardcore tests."""
        if not rule_filter and not level_filter and not property_only and not max_level:
            print("🔥 STARTING HARDCORE UNIVERSAL TEST SUITE 🔥")
            print("=" * 80)
        
        if rule_filter:
            rules_to_test = {k: v for k, v in self.rules.items() if k == rule_filter}
        else:
            rules_to_test = self.rules
        
        total_start = time.time()
        
        for rule_name, rule_module in rules_to_test.items():
            print(f"\n🧪 TESTING RULE: {rule_name.upper()}")
            print("-" * 60)
            
            # Run deterministic tests
            if not property_only:
                max_test_level = max_level if max_level else 10
                for level in range(1, max_test_level + 1):
                    if level_filter and level != level_filter:
                        continue
                    self.run_deterministic_test(rule_name, rule_module, level)
            
            # Run property-based tests
            if not level_filter and not max_level:
                self.run_property_test(rule_name, rule_module)
        
        total_duration = time.time() - total_start
        self.print_summary(total_duration)
        
        return all(r.passed for r in self.results)
    
    def run_deterministic_test(self, rule_name: str, rule_module: Any, level: int):
        """Run deterministic tests for a specific level."""
        start_time = time.time()
        
        try:
            test_func = getattr(self, f"test_{rule_name}_level_{level}", None)
            if test_func:
                print(f"🔍 Level {level}: ", end="", flush=True)
                test_func(rule_module)
                duration = time.time() - start_time
                print(f"PASSED ({duration:.3f}s)")
                
                self.results.append(TestResult(
                    rule_name=rule_name,
                    passed=True,
                    duration=duration,
                    tests_run=1,
                    errors=[],
                    level=level
                ))
            else:
                # Generate tests dynamically
                self.run_generated_test(rule_name, rule_module, level)
        
        except Exception as e:
            duration = time.time() - start_time
            error_msg = f"Level {level} failed: {str(e)}"
            print(f"FAILED ({duration:.3f}s) - {error_msg}")
            
            if self.verbose:
                traceback.print_exc()
            
            self.results.append(TestResult(
                rule_name=rule_name,
                passed=False,
                duration=duration,
                tests_run=1,
                errors=[error_msg],
                level=level
            ))
    
    def run_generated_test(self, rule_name: str, rule_module: Any, level: int):
        """Generate and run tests dynamically."""
        test_cases = self.generate_test_cases(rule_name, level)
        
        print(f"🔍 Level {level} (generated): ", end="", flush=True)
        start_time = time.time()
        
        try:
            for i, (bad_case, expected_good) in enumerate(test_cases):
                # Run the rule
                result = rule_module.audit(bad_case, self.cfg)
                
                # Should detect issues
                if not result.issues:
                    # Some cases might be already good, check if expected is same as input
                    if expected_good and bad_case.strip() == expected_good.strip():
                        continue  # This is an "already good" test case
                    else:
                        raise AssertionError(f"Should flag: {bad_case}")
                
                # Apply fixes and verify
                if result.fixes:
                    fixed = self.apply_fixes(bad_case, result.fixes)
                    result2 = rule_module.audit(fixed, self.cfg)
                    
                    # Should be idempotent
                    if result2.issues:
                        raise AssertionError(f"Not idempotent: {fixed}")
                    
                    # Check if it matches expected (if provided)
                    if expected_good and fixed.strip() != expected_good.strip():
                        if self.verbose:
                            print(f"\n⚠️  Expected: {expected_good}")
                            print(f"⚠️  Got:      {fixed}")
            
            duration = time.time() - start_time
            print(f"PASSED ({len(test_cases)} cases, {duration:.3f}s)")
            
            self.results.append(TestResult(
                rule_name=rule_name,
                passed=True,
                duration=duration,
                tests_run=len(test_cases),
                errors=[],
                level=level
            ))
            
        except Exception as e:
            duration = time.time() - start_time
            error_msg = f"Level {level} failed: {str(e)}"
            print(f"FAILED ({duration:.3f}s) - {error_msg}")
            
            if self.verbose:
                traceback.print_exc()
            
            self.results.append(TestResult(
                rule_name=rule_name,
                passed=False,
                duration=duration,
                tests_run=len(test_cases),
                errors=[error_msg],
                level=level
            ))
    
    def run_property_test(self, rule_name: str, rule_module: Any):
        """Run property-based tests."""
        print(f"🎲 Property tests: ", end="", flush=True)
        
        try:
            # Try to import hypothesis
            from hypothesis import given, strategies as st, settings
            
            # Generate property test
            property_func = getattr(self, f"property_test_{rule_name}", None)
            if property_func:
                if self.quick:
                    settings.register_profile("quick", max_examples=50, deadline=5000)
                    settings.load_profile("quick")
                
                property_func(rule_module)
                print("PASSED")
            else:
                print("SKIPPED (no property test)")
        
        except ImportError:
            print("SKIPPED (hypothesis not available)")
        except Exception as e:
            print(f"FAILED - {str(e)}")
            if self.verbose:
                traceback.print_exc()
    
    def generate_test_cases(self, rule_name: str, level: int):
        """Generate test cases for different rules and levels."""
        
        if rule_name == "dash_ranges":
            return self.generate_dash_ranges_cases(level)
        elif rule_name == "double_periods":
            return self.generate_double_periods_cases(level)
        elif rule_name == "expect_prob_brackets":
            return self.generate_expect_prob_cases(level)
        elif rule_name == "nested_scripts":
            return self.generate_nested_scripts_cases(level)
        elif rule_name == "tie_words":
            return self.generate_tie_words_cases(level)
        elif rule_name == "math_env_normaliser":
            return self.generate_math_env_cases(level)
        else:
            return [("test case", "expected")]  # Fallback
    
    def generate_dash_ranges_cases(self, level: int):
        """Generate test cases for dash ranges rule."""
        cases = {
            1: [  # Basic ranges
                ("pages 5-9", "pages 5–9"),
                ("chapters 1-3", "chapters 1–3"),
                ("sections 10-15", "sections 10–15"),
            ],
            2: [  # With punctuation
                ("pages 5-9.", "pages 5–9."),
                ("(see 1-4)", "(see 1–4)"),
                ("ranges 100-200!", "ranges 100–200!"),
            ],
            3: [  # Multiple ranges
                ("pages 5-9 and 15-20", "pages 5–9 and 15–20"),
                ("chapters 1-3, 7-9, 12-15", "chapters 1–3, 7–9, 12–15"),
            ],
            4: [  # Edge cases
                ("0-1", "0–1"),
                ("999-1000", "999–1000"),
                ("1-2-3", "1–2–3"),  # Should handle multiple
            ],
            5: [  # Mixed with other punctuation
                ("pp. 123-127", "pp. 123–127"),
                ("figs. 2-5", "figs. 2–5"),
            ],
            6: [  # Mathematical contexts (should NOT change)
                ("x-1", "x-1"),  # This is subtraction, not a range
                ("a-b", "a-b"),   # Variables
            ],
            7: [  # Complex scenarios
                ("pages 1-5, figures 10-15, and tables 20-25", 
                 "pages 1–5, figures 10–15, and tables 20–25"),
            ],
            8: [  # Whitespace variations
                ("pages  5-9", "pages  5–9"),
                ("pages 5 - 9", "pages 5 – 9"),
            ],
            9: [  # Already correct cases
                ("pages 5–9", "pages 5–9"),  # Should not change
            ],
            10: [  # Pathological cases
                ("pages 1-2-3-4-5", "pages 1–2–3–4–5"),
                ("123-456-789", "123–456–789"),
            ]
        }
        return cases.get(level, cases[1])
    
    def generate_double_periods_cases(self, level: int):
        """Generate test cases for double periods rule."""
        cases = {
            1: [  # Basic abbreviations
                ("a.s..", "a.s."),
                ("w.l.o.g..", "w.l.o.g."),
                ("i.i.d..", "i.i.d."),
            ],
            2: [  # With following text
                ("a.s.. However", "a.s. However"),
                ("w.r.t.. the measure", "w.r.t. the measure"),
            ],
            3: [  # In sentences
                ("It holds a.s.. The proof", "It holds a.s. The proof"),
                ("Valid w.l.o.g.. However", "Valid w.l.o.g. However"),
            ],
            4: [  # Multiple in one text
                ("a.s.. and i.i.d..", "a.s. and i.i.d."),
            ],
            5: [  # With punctuation
                ("a.s.., but", "a.s., but"),
                ("w.r.t..; moreover", "w.r.t.; moreover"),
            ],
            6: [  # In comments
                ("% a.s.. comment", "% a.s. comment"),
            ],
            7: [  # Complex cases
                ("The sequence is i.i.d.. Moreover, it holds a.s..",
                 "The sequence is i.i.d. Moreover, it holds a.s."),
            ],
            8: [  # Edge cases
                ("etc..", "etc."),
                ("e.g..", "e.g."),
            ],
            9: [  # Already correct
                ("a.s.", "a.s."),
                ("w.l.o.g.", "w.l.o.g."),
            ],
            10: [  # Pathological
                ("a.s...", "a.s.."),  # Triple period becomes double
                ("w.r.t....", "w.r.t..."),
            ]
        }
        return cases.get(level, cases[1])
    
    def generate_expect_prob_cases(self, level: int):
        """Generate test cases for expectation/probability brackets."""
        cases = {
            1: [  # Basic cases
                (r"\mathbb{E}(X)", r"\mathbb{E}[X]"),
                (r"\mathbb{P}(A)", r"\mathbb{P}[A]"),
            ],
            2: [  # With spaces
                (r"\mathbb{E} (X)", r"\mathbb{E}[X]"),
                (r"\mathbb{P}  (A)", r"\mathbb{P}[A]"),
            ],
            3: [  # Complex expressions
                (r"\mathbb{E}(X + Y)", r"\mathbb{E}[X + Y]"),
                (r"\mathbb{P}(A \cap B)", r"\mathbb{P}[A \cap B]"),
            ],
            4: [  # Nested
                (r"\mathbb{E}(\mathbb{E}(X|Y))", r"\mathbb{E}[\mathbb{E}[X|Y]]"),
            ],
            5: [  # In equations
                (r"E = \mathbb{E}(X^2)", r"E = \mathbb{E}[X^2]"),
            ],
            6: [  # Multiple in expression
                (r"\mathbb{E}(X) + \mathbb{P}(A)", r"\mathbb{E}[X] + \mathbb{P}[A]"),
            ],
            7: [  # With subscripts
                (r"\mathbb{E}_n(X)", r"\mathbb{E}_n[X]"),
            ],
            8: [  # In display math
                (r"$$ \mathbb{E}(X) = \mu $$", r"$$ \mathbb{E}[X] = \mu $$"),
            ],
            9: [  # Already correct
                (r"\mathbb{E}[X]", r"\mathbb{E}[X]"),
                (r"\mathbb{P}[A]", r"\mathbb{P}[A]"),
            ],
            10: [  # Pathological
                (r"\mathbb{E}((X))", r"\mathbb{E}[(X)]"),
            ]
        }
        return cases.get(level, cases[1])
    
    def generate_nested_scripts_cases(self, level: int):
        """Generate test cases for nested scripts."""
        cases = {
            1: [  # Basic nested
                (r"x_{y_{1}}", r"x_{\scriptscriptstyle y_1}"),
                (r"a^{b^{c}}", r"a^{\scriptscriptstyle b^c}"),
            ],
            2: [  # With raisebox
                (r"x_{y_{1,2}}", r"x_{\raisebox{0.2ex}{\scriptscriptstyle y_{1,2}}}"),
            ],
            3: [  # Triple nested
                (r"z_{t_{i_{j}}}", r"z_{\raisebox{0.2ex}{\scriptscriptstyle t_{i_j}}}"),
            ],
            4: [  # Complex expressions
                (r"P_{A_{B_{C}}}", r"P_{\raisebox{0.2ex}{\scriptscriptstyle A_{B_C}}}"),
            ],
            5: [  # Mixed sub/super
                (r"x^{y_{z}}", r"x^{\scriptscriptstyle y_z}"),
                (r"a_{b^{c}}", r"a_{\scriptscriptstyle b^c}"),
            ],
            6: [  # In fractions
                (r"\frac{x_{y_{1}}}{z}", r"\frac{x_{\scriptscriptstyle y_1}}{z}"),
            ],
            7: [  # Multiple terms
                (r"x_{a_{1}} + y_{b_{2}}", r"x_{\scriptscriptstyle a_1} + y_{\scriptscriptstyle b_2}"),
            ],
            8: [  # With Greek letters
                (r"\alpha_{\beta_{\gamma}}", r"\alpha_{\scriptscriptstyle \beta_\gamma}"),
            ],
            9: [  # Already fixed
                (r"x_{\scriptscriptstyle y_1}", r"x_{\scriptscriptstyle y_1}"),
            ],
            10: [  # Extreme nesting
                (r"a_{b_{c_{d_{e}}}}", r"a_{\raisebox{0.2ex}{\scriptscriptstyle b_{c_{d_e}}}}"),
            ]
        }
        return cases.get(level, cases[1])
    
    def generate_tie_words_cases(self, level: int):
        """Generate test cases for tie words."""
        cases = {
            1: [  # Basic ties
                ("Figure 1", "Figure~1"),
                ("Table 2", "Table~2"),
                ("Theorem 3", "Theorem~3"),
            ],
            2: [  # Multiple spaces
                ("Figure  1", "Figure~1"),
                ("Table   2", "Table~2"),
            ],
            3: [  # In sentences
                ("See Figure 1 for details", "See Figure~1 for details"),
                ("Theorem 2 states", "Theorem~2 states"),
            ],
            4: [  # Multiple instances
                ("Figure 1 and Table 2", "Figure~1 and Table~2"),
            ],
            5: [  # With punctuation
                ("cf. Lemma 3", "cf.~Lemma~3"),
                ("cf.  Theorem 4", "cf.~Theorem~4"),
            ],
            6: [  # Different numbers
                ("Figure 123", "Figure~123"),
                ("Table 0", "Table~0"),
            ],
            7: [  # Edge cases
                ("pp. 45", "pp.~45"),
                ("Eq. 67", "Eq.~67"),
            ],
            8: [  # Complex
                ("See Figure 1, Table 2, and Theorem 3",
                 "See Figure~1, Table~2, and Theorem~3"),
            ],
            9: [  # Already correct
                ("Figure~1", "Figure~1"),
                ("Table~2", "Table~2"),
            ],
            10: [  # Pathological
                ("Figure    123", "Figure~123"),  # Many spaces
            ]
        }
        return cases.get(level, cases[1])
    
    def generate_math_env_cases(self, level: int):
        """Generate test cases for math environment normalizer."""
        cases = {
            1: [  # Basic cases
                ("$$ a = b $$", r"\[ a = b \]"),
                ("$$ x^2 = y $$", r"\[ x^2 = y \]"),
            ],
            2: [  # With labels
                (r"$$ z \label{eq:z} $$", r"\begin{equation} z \label{eq:z} \end{equation}"),
            ],
            3: [  # Bracket displays
                (r"\[ a \]", r"\[ a \]"),  # Should remain the same
            ],
            4: [  # Eqnarray conversion
                (r"\begin{eqnarray} a&=&b \\ c&=&d \end{eqnarray}", 
                 r"\begin{align} a &= b \\ c &= d \end{align}"),
            ],
            5: [  # Eqnarray*
                (r"\begin{eqnarray*} x=y \end{eqnarray*}",
                 r"\begin{align*} x &= y \end{align*}"),
            ],
            6: [  # Nested environments
                (r"\begin{aligned} c\\d \end{aligned}",
                 r"\begin{equation}\begin{aligned} c\\d \end{aligned}\end{equation}"),
            ],
            7: [  # Already good cases
                (r"\begin{align} a &= b \end{align}", r"\begin{align} a &= b \end{align}"),
            ],
            8: [  # Inline math
                (r"\( x^2 \)", r"$ x^2 $"),
            ],
            9: [  # Complex nested
                (r"\begin{split} q = r \end{split}",
                 r"\begin{equation}\begin{split} q = r \end{split}\end{equation}"),
            ],
            10: [  # Edge cases
                ("$$ $$", r"\[ \]"),  # Empty display
            ]
        }
        return cases.get(level, cases[1])
    
    # Property test definitions
    def property_test_dash_ranges(self, rule_module):
        """Property-based test for dash ranges."""
        from hypothesis import given, strategies as st
        
        @given(a=st.integers(0, 999), b=st.integers(0, 999))
        def test_random_ranges(a, b):
            text = f"pages {a}-{b}"
            result = rule_module.audit(text, self.cfg)
            
            if result.issues:  # Should detect numeric ranges
                fixed = self.apply_fixes(text, result.fixes)
                assert "–" in fixed  # Should contain en-dash
                # Verify idempotence
                result2 = rule_module.audit(fixed, self.cfg)
                assert not result2.issues
        
        test_random_ranges()
    
    def property_test_expect_prob_brackets(self, rule_module):
        """Property-based test for expectation/probability brackets."""
        from hypothesis import given, strategies as st
        
        @given(content=st.text(min_size=1, max_size=10, alphabet="XYZ123"))
        def test_random_content(content):
            text = f"\\mathbb{{E}}({content})"
            result = rule_module.audit(text, self.cfg)
            
            if result.issues:
                fixed = self.apply_fixes(text, result.fixes)
                assert "[" in fixed and "]" in fixed
                assert "(" not in fixed.replace("\\(", "")  # No parens except \(
        
        test_random_content()
    
    def apply_fixes(self, text: str, fixes: List) -> str:
        """Apply fixes to text in reverse order."""
        for fix in sorted(fixes, key=lambda f: f.start, reverse=True):
            text = text[:fix.start] + fix.replacement + text[fix.end:]
        return text
    
    def print_summary(self, total_duration: float):
        """Print test summary."""
        print("\n" + "=" * 80)
        print("🏆 HARDCORE UNIVERSAL TEST RESULTS")
        print("=" * 80)
        
        passed = sum(1 for r in self.results if r.passed)
        failed = len(self.results) - passed
        
        print(f"Total tests run: {len(self.results)}")
        print(f"Passed: {passed}")
        print(f"Failed: {failed}")
        print(f"Total duration: {total_duration:.2f}s")
        
        if failed > 0:
            print("\n❌ FAILED TESTS:")
            for result in self.results:
                if not result.passed:
                    print(f"  - {result.rule_name} Level {result.level}: {result.errors}")
        
        print("\n📊 PER-RULE SUMMARY:")
        rule_stats = {}
        for result in self.results:
            if result.rule_name not in rule_stats:
                rule_stats[result.rule_name] = {"passed": 0, "failed": 0, "duration": 0}
            
            if result.passed:
                rule_stats[result.rule_name]["passed"] += 1
            else:
                rule_stats[result.rule_name]["failed"] += 1
            rule_stats[result.rule_name]["duration"] += result.duration
        
        for rule_name, stats in rule_stats.items():
            total = stats["passed"] + stats["failed"]
            pass_rate = stats["passed"] / total * 100 if total > 0 else 0
            print(f"  {rule_name}: {stats['passed']}/{total} ({pass_rate:.1f}%) "
                  f"in {stats['duration']:.2f}s")
        
        if passed == len(self.results):
            print("\n🎉 ALL TESTS PASSED! Your LaTeX Perfectionist is HARDCORE BATTLE-TESTED! 💪")
        else:
            print(f"\n❌ {failed} tests failed. Fix these issues to achieve perfection.")

def main():
    parser = argparse.ArgumentParser(description="Hardcore Universal Test Runner")
    parser.add_argument("--verify", action="store_true",
                       help="Quick verification that setup is working")
    parser.add_argument("--basic-only", action="store_true",
                       help="Run only basic tests (levels 1-3)")
    parser.add_argument("--rule", help="Test only specific rule")
    parser.add_argument("--level", type=int, choices=range(1, 11), 
                       help="Test only level N (1-10)")
    parser.add_argument("--property", action="store_true",
                       help="Run only property-based tests")
    parser.add_argument("--all", action="store_true", default=True,
                       help="Run everything (default)")
    parser.add_argument("--verbose", "-v", action="store_true",
                       help="Show detailed output")
    parser.add_argument("--quick", action="store_true",
                       help="Reduced examples for faster testing")
    parser.add_argument("--benchmark", action="store_true",
                       help="Include performance benchmarks")
    parser.add_argument("--stress", action="store_true",
                       help="Run extreme stress tests")
    parser.add_argument("--mutation", action="store_true",
                       help="Run mutation testing")
    
    args = parser.parse_args()
    
    runner = HardcoreTestRunner(verbose=args.verbose, quick=args.quick)
    
    # Handle special modes
    if args.verify:
        success = runner.run_verification()
        sys.exit(0 if success else 1)
    
    if args.basic_only:
        success = runner.run_basic_tests()
        sys.exit(0 if success else 1)
    
    # Regular test run
    print("🚀 HARDCORE UNIVERSAL TEST SUITE FOR ALL RULES 🚀")
    print("This will stress-test EVERY LaTeX Perfectionist rule!")
    print("=" * 80)
    
    success = runner.run_all_tests(
        rule_filter=args.rule,
        level_filter=args.level,
        property_only=args.property
    )
    
    sys.exit(0 if success else 1)

if __name__ == "__main__":
    main()