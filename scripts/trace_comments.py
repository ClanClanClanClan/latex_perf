#!/usr/bin/env python3
"""
Script to trace all comment openings and closings in a Coq file.
"""

def trace_comments(filename):
    """
    Trace all comment openings and closings in a Coq file.
    """
    try:
        with open(filename, 'r') as f:
            content = f.read()
            lines = content.split('\n')
    except FileNotFoundError:
        print(f"Error: File '{filename}' not found.")
        return
    
    events = []
    i = 0
    line_num = 1
    col_num = 1
    
    while i < len(content):
        # Check for comment opening (*
        if i + 1 < len(content) and content[i] == '(' and content[i + 1] == '*':
            # Get context around the comment
            start = max(0, i - 10)
            end = min(len(content), i + 30)
            context = content[start:end].replace('\n', '\\n')
            
            events.append({
                'type': 'OPEN',
                'line': line_num,
                'column': col_num,
                'position': i,
                'context': context,
                'marker_at': i - start
            })
            i += 2
            col_num += 2
            continue
        
        # Check for comment closing *)
        if i + 1 < len(content) and content[i] == '*' and content[i + 1] == ')':
            # Get context around the comment
            start = max(0, i - 10)
            end = min(len(content), i + 30)
            context = content[start:end].replace('\n', '\\n')
            
            events.append({
                'type': 'CLOSE',
                'line': line_num,
                'column': col_num,
                'position': i,
                'context': context,
                'marker_at': i - start
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
    
    return events

def main():
    filename = "/Users/dylanpossamai/Library/CloudStorage/Dropbox/Work/Articles/Scripts/core/LatexExpanderFixed2.v"
    
    print(f"Tracing comments in {filename}...")
    print("-" * 80)
    
    events = trace_comments(filename)
    
    print(f"Found {len(events)} comment events:\n")
    
    depth = 0
    for i, event in enumerate(events):
        if event['type'] == 'OPEN':
            print(f"{i+1}. OPEN  at line {event['line']:4d}, col {event['column']:3d} (depth {depth} -> {depth+1})")
            depth += 1
        else:
            depth -= 1
            print(f"{i+1}. CLOSE at line {event['line']:4d}, col {event['column']:3d} (depth {depth+1} -> {depth})")
        
        # Show context with marker
        context = event['context']
        marker_pos = event['marker_at']
        print(f"   Context: {context[:marker_pos]}[{context[marker_pos:marker_pos+2]}]{context[marker_pos+2:]}")
        print()
    
    print(f"\nFinal depth: {depth}")
    if depth != 0:
        print(f"WARNING: Comments are not balanced! Final depth is {depth}")
    else:
        print("All comments are properly balanced.")

if __name__ == "__main__":
    main()