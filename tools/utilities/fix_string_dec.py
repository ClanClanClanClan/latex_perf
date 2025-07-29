#!/usr/bin/env python3
"""
Fix all string_dec usages in RealValidators.v
Convert string_dec calls to proper match syntax.
"""

import re
import sys

def fix_string_dec_pattern(content):
    """Fix string_dec patterns that return sumbool instead of bool"""
    
    # Pattern 1: string_dec var "literal" in if conditions
    pattern1 = r'if\s+string_dec\s+(\w+)\s+"([^"]+)"\s+then'
    replacement1 = r'match string_dec \1 "\2" with | left _ => true | right _ => false'
    
    # Pattern 2: existsb with string_dec 
    pattern2 = r'existsb\s+\(fun\s+(\w+)\s+=>\s+string_dec\s+(\w+)\s+\1\)'
    replacement2 = r'existsb (fun \1 => match string_dec \2 \1 with | left _ => true | right _ => false end)'
    
    # Pattern 3: Direct string_dec usage in boolean contexts
    pattern3 = r'string_dec\s+(\w+)\s+"([^"]+)"'
    def replacement3_fn(match):
        var = match.group(1) 
        literal = match.group(2)
        return f'(match string_dec {var} "{literal}" with | left _ => true | right _ => false end)'
    
    # Apply fixes
    content = re.sub(pattern1, replacement1, content)
    content = re.sub(pattern2, replacement2, content)
    
    # For remaining direct usages, we need to be more careful
    # Only replace if it's in a boolean context (not already in a match)
    lines = content.split('\n')
    fixed_lines = []
    
    for line in lines:
        # Skip lines that already have match syntax
        if 'match string_dec' in line:
            fixed_lines.append(line)
            continue
            
        # Look for string_dec in boolean contexts
        if 'string_dec' in line and ('if ' in line or 'existsb' in line or '&&' in line or '||' in line):
            # Apply the fix
            line = re.sub(pattern3, replacement3_fn, line)
        
        fixed_lines.append(line)
    
    return '\n'.join(fixed_lines)

def main():
    filename = 'src/rules/phase1_5/RealValidators.v'
    
    print(f"🔧 Fixing string_dec usages in {filename}...")
    
    try:
        with open(filename, 'r') as f:
            content = f.read()
        
        # Fix the content
        fixed_content = fix_string_dec_pattern(content)
        
        # Write back
        with open(filename, 'w') as f:
            f.write(fixed_content)
        
        print("✅ Fixed all string_dec usages!")
        
    except Exception as e:
        print(f"❌ Error: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()