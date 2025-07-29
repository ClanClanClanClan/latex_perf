#!/usr/bin/env python3
"""
Script to check for unclosed comments in Coq files.
Comments in Coq are delimited by (* and *) and can be nested.
"""

def check_unclosed_comments(filename):
    """
    Check for unclosed comments in a Coq file.
    Returns a list of locations where comments are opened but not closed.
    """
    try:
        with open(filename, 'r') as f:
            content = f.read()
            lines = content.split('\n')
    except FileNotFoundError:
        print(f"Error: File '{filename}' not found.")
        return
    
    # Track comment depth and positions
    comment_depth = 0
    comment_stack = []  # Stack to track opening positions
    issues = []
    
    i = 0
    line_num = 1
    col_num = 1
    
    while i < len(content):
        # Check for comment opening (* or (**
        if i + 1 < len(content) and content[i] == '(' and content[i + 1] == '*':
            # Check if it's actually (** (documentation comment)
            is_doc_comment = i + 2 < len(content) and content[i + 2] == '*'
            comment_depth += 1
            comment_stack.append({
                'line': line_num,
                'column': col_num,
                'context': lines[line_num - 1].strip() if line_num <= len(lines) else '',
                'is_doc': is_doc_comment
            })
            i += 2
            col_num += 2
            continue
        
        # Check for comment closing *)
        if i + 1 < len(content) and content[i] == '*' and content[i + 1] == ')':
            if comment_depth > 0:
                comment_depth -= 1
                if comment_stack:
                    comment_stack.pop()
            else:
                # Found closing comment without opening
                issues.append({
                    'type': 'unmatched_closing',
                    'line': line_num,
                    'column': col_num,
                    'context': lines[line_num - 1].strip() if line_num <= len(lines) else ''
                })
            i += 2
            col_num += 2
            continue
        
        # Track line and column numbers
        if content[i] == '\n':
            line_num += 1
            col_num = 1
        else:
            col_num += 1
        
        i += 1
    
    # Check if there are unclosed comments
    if comment_depth > 0:
        for open_comment in comment_stack:
            issues.append({
                'type': 'unclosed',
                'line': open_comment['line'],
                'column': open_comment['column'],
                'context': open_comment['context']
            })
    
    return issues

def get_surrounding_lines(filename, line_num, context_lines=3):
    """Get surrounding lines for better context."""
    try:
        with open(filename, 'r') as f:
            lines = f.readlines()
        
        start = max(0, line_num - context_lines - 1)
        end = min(len(lines), line_num + context_lines)
        
        result = []
        for i in range(start, end):
            prefix = ">>> " if i == line_num - 1 else "    "
            result.append(f"{i+1:4d}: {prefix}{lines[i].rstrip()}")
        
        return '\n'.join(result)
    except:
        return ""

def main():
    filename = "/Users/dylanpossamai/Library/CloudStorage/Dropbox/Work/Articles/Scripts/core/LatexExpanderFixed2.v"
    
    print(f"Checking {filename} for unclosed comments...")
    print("-" * 60)
    
    issues = check_unclosed_comments(filename)
    
    if not issues:
        print("✓ No unclosed comments found!")
    else:
        print(f"Found {len(issues)} issue(s):\n")
        for issue in issues:
            if issue['type'] == 'unclosed':
                print(f"UNCLOSED COMMENT:")
                print(f"  Line {issue['line']}, Column {issue['column']}")
                print(f"  Opening comment at: {issue['context']}")
                print(f"\n  Surrounding context:")
                print(get_surrounding_lines(filename, issue['line']))
                print()
            elif issue['type'] == 'unmatched_closing':
                print(f"UNMATCHED CLOSING *):")
                print(f"  Line {issue['line']}, Column {issue['column']}")
                print(f"  Context: {issue['context']}")
                print()

if __name__ == "__main__":
    main()