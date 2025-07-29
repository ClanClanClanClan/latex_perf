#!/usr/bin/env python3
"""Fix Python syntax errors in test files."""

import re

def fix_file(filepath):
    with open(filepath, 'r') as f:
        content = f.read()
    
    # Replace literal \n with actual newlines
    content = content.replace('\\nfrom', '\n\nfrom')
    content = content.replace('\\nimport', '\n\nimport')
    content = content.replace('\\n\\n\\n#', '\n\n#')
    
    with open(filepath, 'w') as f:
        f.write(content)
    
    print(f"Fixed {filepath}")

# Fix all files with syntax errors
files_to_fix = [
    'tests/unit/test_core_engine.py',
    'tests/unit/test_dsl_compiler.py',
    'tests/unit/test_rules.py',
    'tests/unit/test_validation_framework.py'
]

for file in files_to_fix:
    try:
        fix_file(file)
    except Exception as e:
        print(f"Error fixing {file}: {e}")