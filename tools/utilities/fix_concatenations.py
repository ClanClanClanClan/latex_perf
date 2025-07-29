#!/usr/bin/env python3
"""
Fix all ++ operators in RealValidators.v by replacing string concatenations with String.append
and list concatenations with app
"""

import re

def fix_concatenations(content):
    # Fix string concatenations within message fields
    # Pattern: message := "text" ++ variable ++ "more text"
    
    # First, handle complex patterns with multiple concatenations
    content = re.sub(
        r'message := "([^"]*)" \+\+ ([^;]+) \+\+ "([^"]*)"',
        r'message := String.append (String.append "\1" \2) "\3"',
        content
    )
    
    # Handle simple string concatenations: "text" ++ variable
    content = re.sub(
        r'message := "([^"]*)" \+\+ ([^;]+);',
        r'message := String.append "\1" \2;',
        content
    )
    
    # Handle variable ++ "text" patterns
    content = re.sub(
        r'message := ([^"]+) \+\+ "([^"]*)"',
        r'message := String.append \1 "\2"',
        content
    )
    
    # Fix remaining list concatenations
    content = re.sub(
        r'(\w+) \+\+ (\w+)(?=\s*$|\s*else|\s*\))',
        r'app \1 \2',
        content,
        flags=re.MULTILINE
    )
    
    return content

def main():
    filename = 'src/rules/phase1_5/RealValidators.v'
    
    with open(filename, 'r') as f:
        content = f.read()
    
    new_content = fix_concatenations(content)
    
    with open(filename, 'w') as f:
        f.write(new_content)
    
    print("✅ Fixed all ++ concatenation operators")

if __name__ == "__main__":
    main()