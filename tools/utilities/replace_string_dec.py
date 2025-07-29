#!/usr/bin/env python3
"""
Replace string_dec match patterns with String.eqb
"""

import re

def replace_pattern(content):
    # Pattern to match: match string_dec var1 var2 with | left _ => true | right _ => false end
    pattern = r'match string_dec ([^\s]+) ([^\s]+) with\s*\|\s*left\s*_\s*=>\s*true\s*\|\s*right\s*_\s*=>\s*false\s*end'
    replacement = r'String.eqb \1 \2'
    
    return re.sub(pattern, replacement, content, flags=re.MULTILINE | re.DOTALL)

def main():
    filename = 'src/rules/phase1_5/RealValidators.v'
    
    with open(filename, 'r') as f:
        content = f.read()
    
    new_content = replace_pattern(content)
    
    with open(filename, 'w') as f:
        f.write(new_content)
    
    print("✅ Replaced string_dec patterns with String.eqb")

if __name__ == "__main__":
    main()