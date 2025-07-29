#!/usr/bin/env python3
"""Comprehensively fix all quote-related test expectations in YAML files"""

import yaml
import re
from pathlib import Path

def convert_quotes_in_string(text):
    """Convert straight quotes to proper curly quotes in a string"""
    result = ""
    in_quotes = False
    i = 0
    
    while i < len(text):
        char = text[i]
        
        if char == '"':
            if not in_quotes:
                result += '"'  # Opening quote (U+201C)
                in_quotes = True
            else:
                result += '"'  # Closing quote (U+201D)
                in_quotes = False
        else:
            result += char
        i += 1
    
    return result

def fix_yaml_file(file_path):
    """Fix all quote expectations in a YAML file"""
    print(f"Processing {file_path}")
    
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Parse YAML to understand structure
    try:
        data = yaml.safe_load(content)
    except yaml.YAMLError as e:
        print(f"  Error parsing YAML: {e}")
        print(f"  Skipping {file_path}")
        return False
    
    if not isinstance(data, dict):
        print(f"  YAML data is not a dictionary, skipping")
        return False
    
    changes_made = 0
    
    # Process test cases
    if 'tests' in data and isinstance(data['tests'], dict):
        for category, tests in data['tests'].items():
            if isinstance(tests, list):
                for test in tests:
                    if isinstance(test, dict) and 'fixed' in test:
                        original = test['fixed']
                        fixed = convert_quotes_in_string(original)
                        
                        if original != fixed:
                            # Replace in the original content
                            # Use regex to find and replace the specific line
                            pattern = re.escape(f'fixed: {repr(original)}')
                            replacement = f'fixed: {repr(fixed)}'
                            content = re.sub(pattern, replacement, content)
                            changes_made += 1
                            print(f"  Fixed: {original} -> {fixed}")
    
    # Process examples
    if 'examples' in data:
        for category, examples in data['examples'].items():
            if isinstance(examples, list):
                for i, example in enumerate(examples):
                    if isinstance(example, str):
                        original = example
                        fixed = convert_quotes_in_string(original)
                        
                        if original != fixed:
                            # Replace in the original content
                            pattern = re.escape(f'- {repr(original)}')
                            replacement = f'- {repr(fixed)}'
                            content = re.sub(pattern, replacement, content)
                            changes_made += 1
                            print(f"  Fixed example: {original} -> {fixed}")
    
    if changes_made > 0:
        with open(file_path, 'w', encoding='utf-8') as f:
            f.write(content)
        print(f"  Made {changes_made} changes")
        return True
    else:
        print("  No changes needed")
        return False

def main():
    """Fix all YAML files in the rules directory"""
    rules_dir = Path("src/rules")
    
    if not rules_dir.exists():
        print(f"Rules directory {rules_dir} does not exist")
        return
    
    yaml_files = list(rules_dir.rglob("*.yaml"))
    
    if not yaml_files:
        print("No YAML files found")
        return
    
    print(f"Found {len(yaml_files)} YAML files to process")
    
    total_changes = 0
    for yaml_file in yaml_files:
        if fix_yaml_file(yaml_file):
            total_changes += 1
    
    print(f"\nProcessed {len(yaml_files)} files, made changes to {total_changes} files")
    
    # Verify one of the files
    if yaml_files:
        print("\nVerifying changes in first file:")
        test_file = yaml_files[0]
        
        with open(test_file, 'r', encoding='utf-8') as f:
            data = yaml.safe_load(f)
        
        if 'tests' in data and 'basic' in data['tests'] and data['tests']['basic']:
            first_test = data['tests']['basic'][0]
            if 'fixed' in first_test:
                fixed_text = first_test['fixed']
                print(f"  Sample 'fixed' field: {repr(fixed_text)}")
                
                # Check Unicode codepoints
                codepoints = [ord(c) for c in fixed_text]
                has_curly_quotes = 8220 in codepoints and 8221 in codepoints
                print(f"  Has curly quotes: {has_curly_quotes}")
                
                if has_curly_quotes:
                    print("  ✅ Unicode curly quotes detected!")
                else:
                    print("  ❌ Still using straight quotes")

if __name__ == "__main__":
    main()