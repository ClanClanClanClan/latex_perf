#!/usr/bin/env python3
"""
🔍 MANUAL VERIFICATION OF VALIDATOR RESULTS
Quick audit to check if our detected "issues" are actually problems
"""

import re
from pathlib import Path

def analyze_math_issues(latex_file):
    """Manually analyze MATH-001 detections to see if they're false positives"""
    
    with open(latex_file, 'r', encoding='utf-8', errors='ignore') as f:
        content = f.read()
    
    # Find all inline math expressions using $ delimiters
    inline_math = re.findall(r'\$([^$]+)\$', content)
    
    print(f"📄 Analyzing: {latex_file.name}")
    print(f"📊 Found {len(inline_math)} inline math expressions")
    print("\n🔍 SAMPLE DETECTIONS:")
    
    # Show first 10 examples
    for i, math_expr in enumerate(inline_math[:10], 1):
        print(f"{i:2d}. ${math_expr}$")
        
        # Classify as legitimate or problematic
        if len(math_expr.strip()) > 0 and not math_expr.startswith('"'):
            classification = "✅ LEGITIMATE MATH"
        else:
            classification = "❌ POTENTIAL ISSUE"
            
        print(f"    → {classification}")
    
    print(f"\n📈 ANALYSIS:")
    print(f"Our MATH-001 validator would flag ALL {len(inline_math)} of these as 'issues'")
    print(f"But most appear to be legitimate mathematical expressions!")
    
    return len(inline_math)

def analyze_double_dollar_math(latex_file):
    """Check POST-037 detections (our supposedly accurate validator)"""
    
    with open(latex_file, 'r', encoding='utf-8', errors='ignore') as f:
        content = f.read()
    
    # Find display math using $$
    display_math = re.findall(r'\$\$([^$]+)\$\$', content, re.DOTALL)
    
    print(f"\n💰 DOUBLE DOLLAR MATH ANALYSIS:")
    print(f"Found {len(display_math)} display math blocks using $$")
    
    for i, math_block in enumerate(display_math[:3], 1):
        preview = math_block.strip()[:100].replace('\n', ' ')
        print(f"{i}. $${preview}{'...' if len(math_block) > 100 else ''}$$")
        print(f"   → This IS obsolete syntax (should use \\[ \\] or equation)")
    
    return len(display_math)

def analyze_ground_truth_vs_detections():
    """Compare what ground truth expects vs what we detect"""
    
    print(f"\n🎯 GROUND TRUTH vs OUR DETECTIONS:")
    print(f"{'Rule':<20} {'Ground Truth':<15} {'We Detect':<12} {'Status'}")
    print(f"{'-'*20} {'-'*15} {'-'*12} {'-'*20}")
    
    comparisons = [
        ("straight_quotes", 1, 0, "❌ MISSED"),
        ("double_dollar_math", 12, 23, "✅ DETECTED (1.9x)"),
        ("wrong_dashes", 936, 0, "❌ MISSED"),
        ("bad_ellipsis", 9, 0, "❌ MISSED"),
        ("missing_tilde_cite", 8, 0, "❌ MISSED"),
        ("complex_macros", 43, 0, "❌ MISSED"),
        ("nested_environments", 4, 0, "❌ MISSED"),
        ("MATH-001 (extra)", 0, 531, "⚠️ FALSE POSITIVE?"),
        ("SCRIPT-005 (extra)", 0, 420, "⚠️ FALSE POSITIVE?"),
        ("MATH-029 (extra)", 0, 413, "⚠️ FALSE POSITIVE?"),
    ]
    
    for rule, gt, detected, status in comparisons:
        print(f"{rule:<20} {gt:<15} {detected:<12} {status}")

if __name__ == "__main__":
    # Analyze the first paper
    paper_path = Path("corpus/papers/2506.20456v2/Final-fractals.tex")
    
    if paper_path.exists():
        math_count = analyze_math_issues(paper_path)
        dollar_count = analyze_double_dollar_math(paper_path)
        analyze_ground_truth_vs_detections()
        
        print(f"\n🚨 CRITICAL CONCLUSION:")
        print(f"• We detect 531 MATH-001 'issues' but found {math_count} legitimate math expressions")
        print(f"• We detect 23 POST-037 issues and found {dollar_count} actual $$ blocks")  
        print(f"• We miss 6/7 ground truth issue types completely")
        print(f"• We generate 1,544 extra detections with unknown accuracy")
        
        false_positive_rate = (531 - 1) / 531 * 100  # Assuming only 1 is real
        print(f"\n📊 ESTIMATED FALSE POSITIVE RATE: {false_positive_rate:.1f}%")
        print(f"📊 ACTUAL PRECISION: Probably <10%")
        
    else:
        print(f"❌ Could not find paper at {paper_path}")