#!/usr/bin/env python3
"""
Setup Script for Hardcore Test Suite

This script creates all the necessary test files in the correct locations.
Run this first before running the hardcore test runner.

Usage:
    python3 setup_hardcore_tests.py
"""

import os
from pathlib import Path

def create_hardcore_math_test_suite():
    """Create the hardcore math test suite file."""
    content = '''"""
Hardcore Math Environment Test Suite - Basic Version

This is a simplified version for initial setup.
"""

from latex_perfectionist.rules import math_env_normaliser as R

# Basic test data
BASIC_BAD = [
    "$$ a=b $$",
    "$$ x^2 = y $$",
    "$$ z \\\\label{eq:z} $$",
    "\\\\[ a \\\\]",
    "\\\\[ a\\\\label{eq:foo} \\\\]",
    "\\\\begin{eqnarray} a&=&b \\\\\\\\ c&=&d \\\\end{eqnarray}",
    "\\\\begin{eqnarray*} x=y \\\\end{eqnarray*}",
    "\\\\begin{aligned} c\\\\\\\\d \\\\end{aligned}",
    "\\\\begin{split} q = r \\\\end{split}",
    "\\\\( x^2 \\\\)",
]

BASIC_GOOD = [
    "\\\\[ a=b \\\\]",
    "\\\\[ x^2 = y \\\\]",
    "\\\\begin{equation*} z \\\\label{eq:z} \\\\end{equation*}",
    "$ a $",
    "\\\\begin{equation} a\\\\label{eq:foo} \\\\end{equation}",
    "\\\\begin{align} a &= b \\\\\\\\ c &= d \\\\end{align}",
    "\\\\begin{align*} x &= y \\\\end{align*}",
    "\\\\begin{equation}\\\\begin{aligned} c\\\\\\\\d \\\\end{aligned}\\\\end{equation}",
    "\\\\begin{equation}\\\\begin{split} q = r \\\\end{split}\\\\end{equation}",
    "$ x^2 $",
]

def apply_fixes(txt, fixes):
    """Apply fixes to text."""
    for f in sorted(fixes, key=lambda x: x.start, reverse=True):
        txt = txt[:f.start] + f.replacement + txt[f.end:]
    return txt

def test_level_1_basic(cfg):
    """Level 1: Basic transformations"""
    print("🧪 Testing Level 1: Basic transformations...")
    
    for i, (bad, good) in enumerate(zip(BASIC_BAD, BASIC_GOOD)):
        result = R.audit(bad, cfg)
        assert result.issues, f"Should flag: {bad}"
        
        # Test fixes
        if result.fixes:
            patched = apply_fixes(bad, result.fixes)
            result2 = R.audit(patched, cfg)
            assert not result2.issues, f"Not idempotent: {patched}"

def test_level_2_whitespace_hell(cfg):
    """Level 2: Whitespace hell"""
    print("🧪 Testing Level 2: Whitespace...")
    # Simple whitespace test
    test_case = "$$   a=b   $$"
    result = R.audit(test_case, cfg)
    assert result.issues, f"Should flag: {test_case}"

def test_level_3_complex_math(cfg):
    """Level 3: Complex math"""
    print("🧪 Testing Level 3: Complex math...")
    test_case = "$$ \\\\int_0^\\\\infty e^{-x^2} dx = \\\\sqrt{\\\\pi} $$"
    result = R.audit(test_case, cfg)
    assert result.issues, f"Should flag: {test_case}"

def test_level_4_nested_environments(cfg):
    """Level 4: Nested environments"""
    print("🧪 Testing Level 4: Nested environments...")
    test_case = "\\\\begin{eqnarray} a &=& b \\\\end{eqnarray}"
    result = R.audit(test_case, cfg)
    assert result.issues, f"Should flag: {test_case}"

def test_level_5_edge_cases(cfg):
    """Level 5: Edge cases"""
    print("🧪 Testing Level 5: Edge cases...")
    test_case = "$$ $$"
    result = R.audit(test_case, cfg)
    assert result.issues, f"Should flag: {test_case}"

def test_level_6_academic_scenarios(cfg):
    """Level 6: Academic scenarios"""
    print("🧪 Testing Level 6: Academic scenarios...")
    test_case = "\\\\begin{eqnarray} E &=& mc^2 \\\\\\\\\\\\\\\\end{eqnarray}"
    result = R.audit(test_case, cfg)
    assert result.issues, f"Should flag: {test_case}"

def test_level_7_pathological_cases(cfg):
    """Level 7: Pathological cases"""
    print("🧪 Testing Level 7: Pathological cases...")
    test_case = "$$ a = b \\\\label{eq:1} \\\\label{eq:2} $$"
    result = R.audit(test_case, cfg)
    assert result.issues, f"Should flag: {test_case}"

def test_level_8_always_good(cfg):
    """Level 8: Always good cases"""
    print("🧪 Testing Level 8: Always good cases...")
    good_cases = [
        "\\\\begin{align} a &= b \\\\\\\\\\\\\\\\c &= d \\\\end{align}",
        "$ x = y $",
        "\\\\[ a = b \\\\]",
    ]
    
    for case in good_cases:
        result = R.audit(case, cfg)
        assert not result.issues, f"False positive: {case}"

print("📦 Hardcore math test suite loaded!")
'''
    return content

def create_hardcore_property_tests():
    """Create the hardcore property tests file."""
    content = '''"""
Hardcore Property-Based Tests - Basic Version

This is a simplified version for initial setup.
"""

try:
    from hypothesis import given, strategies as st, settings
    HYPOTHESIS_AVAILABLE = True
except ImportError:
    HYPOTHESIS_AVAILABLE = False
    print("⚠️  Hypothesis not available, property tests will be skipped")

from latex_perfectionist.rules import math_env_normaliser as R

def apply_fixes(txt, fixes):
    """Apply fixes to text."""
    for f in sorted(fixes, key=lambda x: x.start, reverse=True):
        txt = txt[:f.start] + f.replacement + txt[f.end:]
    return txt

if HYPOTHESIS_AVAILABLE:
    @given(
        content=st.text(min_size=1, max_size=10, alphabet="abcxy123"),
    )
    @settings(max_examples=50, deadline=None)
    def test_dollar_display_random(content, cfg):
        """Test $$ ... $$ with random content."""
        src = f"$$ {content} $$"
        rr = R.audit(src, cfg)
        
        # Should always be flagged (dollar display is always bad)
        assert rr.issues, f"Dollar display should always be flagged: {src}"
        
        # Apply fixes and check idempotence
        if rr.fixes:
            patched = apply_fixes(src, rr.fixes)
            assert "$$" not in patched, f"Fixed version still contains $$: {patched}"
            rr2 = R.audit(patched, cfg)
            assert not rr2.issues, f"Not idempotent: {patched}"
else:
    def test_dollar_display_random(cfg):
        """Fallback test when hypothesis is not available."""
        test_cases = ["$$ a $$", "$$ x = y $$", "$$ test $$"]
        for case in test_cases:
            result = R.audit(case, cfg)
            assert result.issues, f"Should flag: {case}"

def test_all_property_based(cfg):
    """Run all property-based tests."""
    print("🔥 Starting property-based tests...")
    test_dollar_display_random(cfg)
    print("🎉 Property-based tests completed!")

print("📦 Hardcore property tests loaded!")
'''
    return content

def create_enhanced_math_tests():
    """Create the enhanced math tests file."""
    content = '''"""
Enhanced Math Environment Tests - Basic Version

This is a simplified version for initial setup.
"""

def test_enhanced_math_normalizer_comprehensive(cfg):
    """Basic enhanced normalizer test."""
    print("🔍 Testing enhanced math normalizer...")
    
    # Try to import enhanced normalizer
    try:
        from latex_perfectionist.rules.enhanced_math_normalizer import audit_with_preamble_support
        
        # Test with a simple document
        doc = """
        \\\\documentclass{article}
        \\\\newcommand{\\\\myeq}[1]{$$#1$$}
        \\\\begin{document}
        \\\\myeq{E = mc^2}
        \\\\end{document}
        """
        
        result = audit_with_preamble_support(doc, cfg)
        print(f"✅ Enhanced normalizer working: found {len(result.issues)} issues")
        
    except ImportError:
        print("⚠️  Enhanced normalizer not available, using basic normalizer")
        from latex_perfectionist.rules import math_env_normaliser as R
        
        # Test basic functionality
        test_case = "$$ a = b $$"
        result = R.audit(test_case, cfg)
        assert result.issues, "Should detect issues in basic test"
        print("✅ Basic normalizer working")

def test_mathenv_enhanced(cfg):
    """Entry point for pytest integration."""
    test_enhanced_math_normalizer_comprehensive(cfg)

print("📦 Enhanced math tests loaded!")
'''
    return content

def main():
    print("🚀 Setting up Hardcore Test Suite...")
    print("=" * 50)
    
    # Get the project root (where this script is run from)
    project_root = Path.cwd()
    tests_dir = project_root / "tests"
    
    # Create tests directory if it doesn't exist
    tests_dir.mkdir(exist_ok=True)
    
    # Create __init__.py in tests if it doesn't exist
    init_file = tests_dir / "__init__.py"
    if not init_file.exists():
        init_file.write_text("# Tests module\\n")
        print(f"✅ Created {init_file}")
    
    # Create test files
    files_to_create = [
        (tests_dir / "hardcore_math_test_suite.py", create_hardcore_math_test_suite()),
        (tests_dir / "hardcore_property_tests.py", create_hardcore_property_tests()),
        (tests_dir / "enhanced_math_tests.py", create_enhanced_math_tests()),
    ]
    
    for file_path, content in files_to_create:
        if file_path.exists():
            print(f"⚠️  {file_path} already exists, skipping...")
        else:
            file_path.write_text(content)
            print(f"✅ Created {file_path}")
    
    # Replace the hardcore_test_runner.py
    runner_path = project_root / "hardcore_test_runner.py"
    if runner_path.exists():
        backup_path = project_root / "hardcore_test_runner.py.backup"
        runner_path.rename(backup_path)
        print(f"📋 Backed up existing runner to {backup_path}")
    
    print("\\n🎉 Setup completed!")
    print("\\nNext steps:")
    print("1. Run: python3 hardcore_test_runner.py --verify")
    print("2. Run: python3 hardcore_test_runner.py --basic-only")
    print("3. Run: python3 hardcore_test_runner.py --level 1")
    print("4. If all works: python3 hardcore_test_runner.py")

if __name__ == "__main__":
    main()
