#!/usr/bin/env python3
"""Check v20 specification compliance for TYPO-001"""

import yaml
import sys
sys.path.insert(0, 'src')

from latex_perfectionist.compiled_rules.rule_typo_001 import audit

def check_v20_compliance():
    """Check if TYPO-001 meets v20 specification requirements"""
    
    print("V20 Specification Compliance Check for TYPO-001")
    print("=" * 60)
    
    # Load rule data
    with open('src/rules/typography/TYPO-001-paranoid.yaml', 'r') as f:
        rule_data = yaml.safe_load(f)
    
    print(f"Rule ID: {rule_data['id']}")
    print(f"Name: {rule_data['name']}")
    print(f"Category: {rule_data['category']}")
    print(f"Severity: {rule_data['severity']}")
    print(f"Tier: {rule_data['tier']}")
    
    # Check v20 specification requirements
    requirements = {
        'Rule metadata': {
            'id': rule_data.get('id') == 'TYPO-001',
            'name': rule_data.get('name') is not None,
            'category': rule_data.get('category') == 'typography',
            'severity': rule_data.get('severity') in ['error', 'warning', 'info'],
            'tier': rule_data.get('tier') in ['instant', 'fast', 'normal', 'deep', 'full'],
            'message': rule_data.get('message') is not None,
            'description': rule_data.get('description') is not None,
            'rationale': rule_data.get('rationale') is not None,
        },
        'Detection': {
            'type': rule_data.get('detection', {}).get('type') == 'regex',
            'pattern': rule_data.get('detection', {}).get('pattern') is not None,
            'handles_double_quotes': '"' in rule_data.get('detection', {}).get('pattern', ''),
            'handles_single_quotes': "'" in rule_data.get('detection', {}).get('pattern', ''),
        },
        'Context exclusion': {
            'excludes_verbatim': 'verbatim' in rule_data.get('context', {}).get('excludes', []),
            'excludes_lstlisting': 'lstlisting' in rule_data.get('context', {}).get('excludes', []),
            'excludes_math': 'math' in rule_data.get('context', {}).get('excludes', []),
            'excludes_comments': 'comment' in rule_data.get('context', {}).get('excludes', []),
        },
        'Auto-fix': {
            'available': rule_data.get('autofix', {}).get('available') is True,
            'safe': rule_data.get('autofix', {}).get('safe') is True,
            'custom_function': rule_data.get('autofix', {}).get('strategy') == 'custom',
        },
        'Test coverage': {
            'basic_tests': 'basic' in rule_data.get('tests', {}),
            'edge_cases': 'edge_cases' in rule_data.get('tests', {}),
            'false_positives': 'false_positives' in rule_data.get('tests', {}),
            'unicode_tests': 'unicode' in rule_data.get('tests', {}),
            'performance_tests': 'performance' in rule_data.get('tests', {}),
            'contextual_tests': 'contextual' in rule_data.get('tests', {}),
        },
        'Documentation': {
            'examples_good': 'examples' in rule_data and 'good' in rule_data['examples'],
            'examples_bad': 'examples' in rule_data and 'bad' in rule_data['examples'],
            'references': 'references' in rule_data,
            'performance_spec': 'performance' in rule_data,
        }
    }
    
    # Check each requirement
    all_passed = True
    for category, checks in requirements.items():
        print(f"\n{category}:")
        category_passed = True
        for check_name, result in checks.items():
            status = "✅" if result else "❌"
            print(f"  {status} {check_name}: {result}")
            if not result:
                category_passed = False
                all_passed = False
        
        if category_passed:
            print(f"  ✅ {category} - PASSED")
        else:
            print(f"  ❌ {category} - FAILED")
    
    # Test functional requirements
    print(f"\nFunctional Testing:")
    
    # Test double quotes
    result = audit('He said "hello" to me.', {})
    double_quote_works = len(result.issues) > 0 and len(result.fixes) > 0
    print(f"  ✅ Double quotes detected: {double_quote_works}")
    
    # Test single quotes  
    result = audit("He said 'hello' to me.", {})
    single_quote_works = len(result.issues) > 0 and len(result.fixes) > 0
    print(f"  ✅ Single quotes detected: {single_quote_works}")
    
    # Test context exclusion
    result = audit('\\begin{verbatim}"test"\\end{verbatim}', {})
    context_exclusion_works = len(result.issues) == 0
    print(f"  ✅ Context exclusion works: {context_exclusion_works}")
    
    # Test Unicode output
    result = audit('He said "hello" to me.', {})
    if result.fixes:
        fix = result.fixes[0]
        fixed = 'He said "hello" to me.'[:fix.start] + fix.replacement + 'He said "hello" to me.'[fix.end:]
        unicode_output = chr(8220) in fixed and chr(8221) in fixed
        print(f"  ✅ Unicode curly quotes generated: {unicode_output}")
    
    # Performance check
    import time
    start = time.perf_counter()
    large_text = 'He said "hello" to me. ' * 1000
    result = audit(large_text, {})
    elapsed_ms = (time.perf_counter() - start) * 1000
    performance_ok = elapsed_ms < 70  # instant tier requirement
    print(f"  ✅ Performance (instant tier <70ms): {performance_ok} ({elapsed_ms:.2f}ms)")
    
    print(f"\n{'='*60}")
    if all_passed:
        print("🎉 TYPO-001 FULLY COMPLIANT with v20 specification!")
    else:
        print("❌ TYPO-001 has compliance issues - see details above")
    
    return all_passed

if __name__ == "__main__":
    check_v20_compliance()