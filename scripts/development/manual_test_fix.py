#!/usr/bin/env python3
"""Manually fix the key failing test cases"""

import re

# Define the mappings for the most critical test cases
test_fixes = [
    # Basic tests
    ('He said "hello world" to me.', 'He said "hello world" to me.'),
    ('The "first" and "second" items.', 'The "first" and "second" items.'),
    ('He said "" nothing.', 'He said "" nothing.'),
    ('He said "hello\\nworld" to me.', 'He said "hello\\nworld" to me.'),
    ('""Double"" quotes', '""Double"" quotes'),
    ('"Start and end"', '"Start and end"'),
    ('She said "He told me \'stop\' yesterday" quietly.', 'She said "He told me \'stop\' yesterday" quietly.'),
    ('He said "hello".', 'He said "hello".'),
    ('Hello, "world"!', 'Hello, "world"!'),
    ('The word "café" is French.', 'The word "café" is French.'),
    
    # Unicode tests
    ('Mix of "ASCII" and "Unicode" quotes', 'Mix of "ASCII" and "Unicode" quotes'),
    ('Er sagte "Hallo" zu mir.', 'Er sagte "Hallo" zu mir.'),
    ('Il a dit "bonjour" à moi.', 'Il a dit "bonjour" à moi.'),
    ('Text with "café" inside.', 'Text with "café" inside.'),
    ('Hebrew "עברית" text.', 'Hebrew "עברית" text.'),
    ('Text with "\\u200Bhidden\\u200B" spaces.', 'Text with "\\u200Bhidden\\u200B" spaces.'),
    
    # Contextual tests
    ('\\section{The "Introduction" Chapter}', '\\section{The "Introduction" Chapter}'),
    ('\\caption{The "test" figure}', '\\caption{The "test" figure}'),
    ('Text\\footnote{See "reference" for details}.', 'Text\\footnote{See "reference" for details}.'),
    ('\\bibitem{key} Author, "Title", 2023.', '\\bibitem{key} Author, "Title", 2023.'),
    ('\\index{"quoted term"}', '\\index{"quoted term"}'),
    ('\\href{http://example.com}{"Link text"}', '\\href{http://example.com}{"Link text"}'),
]

def fix_yaml_file():
    """Fix the YAML file with manual replacements"""
    file_path = 'src/rules/typography/TYPO-001-paranoid.yaml'
    
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    changes_made = 0
    
    for old_text, new_text in test_fixes:
        # Create patterns to match the fixed: lines
        old_pattern = f"fixed: '{old_text}'"
        new_pattern = f"fixed: '{new_text}'"
        
        if old_pattern in content:
            content = content.replace(old_pattern, new_pattern)
            changes_made += 1
            print(f"Fixed: {old_text} -> {new_text}")
    
    if changes_made > 0:
        with open(file_path, 'w', encoding='utf-8') as f:
            f.write(content)
        print(f"\nMade {changes_made} changes to {file_path}")
        return True
    else:
        print("No changes needed")
        return False

if __name__ == "__main__":
    fix_yaml_file()
    
    # Verify the changes
    print("\nVerifying changes...")
    
    import yaml
    with open('src/rules/typography/TYPO-001-paranoid.yaml', 'r', encoding='utf-8') as f:
        data = yaml.safe_load(f)
    
    if 'tests' in data and 'basic' in data['tests'] and data['tests']['basic']:
        first_test = data['tests']['basic'][0]
        if 'fixed' in first_test:
            fixed_text = first_test['fixed']
            print(f"First test 'fixed' field: {repr(fixed_text)}")
            
            # Check Unicode codepoints
            codepoints = [ord(c) for c in fixed_text]
            has_curly_quotes = 8220 in codepoints and 8221 in codepoints
            print(f"Has curly quotes: {has_curly_quotes}")
            
            if has_curly_quotes:
                print("✅ Unicode curly quotes detected!")
            else:
                print("❌ Still using straight quotes")
                print(f"Unicode codepoints: {codepoints}")