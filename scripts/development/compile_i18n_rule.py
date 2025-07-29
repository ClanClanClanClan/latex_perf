#!/usr/bin/env python3
"""
Compile i18n-enabled rules using the enhanced compiler.
"""

import sys
import yaml
from pathlib import Path
sys.path.insert(0, 'src')

from latex_perfectionist.dsl.i18n_compiler import I18nDSLCompiler

def compile_i18n_rule(rule_path: str):
    """Compile a rule with i18n support."""
    rule_path = Path(rule_path)
    
    # Load the rule
    with open(rule_path, 'r') as f:
        rule_data = yaml.safe_load(f)
    
    # Create compiler
    compiler = I18nDSLCompiler()
    
    # Compile the rule
    compiled_code = compiler.compile_rule(rule_data)
    
    # Determine output path
    rule_id = rule_data['id'].lower().replace('-', '_')
    output_path = Path(f'src/latex_perfectionist/compiled_rules/rule_{rule_id}.py')
    
    # Write compiled rule
    with open(output_path, 'w') as f:
        f.write(compiled_code)
    
    print(f"Compiled {rule_path} -> {output_path}")
    return output_path

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python compile_i18n_rule.py <rule_path>")
        sys.exit(1)
    
    rule_path = sys.argv[1]
    compile_i18n_rule(rule_path)