#!/usr/bin/env python3
import sys

filename = 'core/LatexExpanderUltimate.v'
with open(filename, 'r') as f:
    lines = f.readlines()

comment_stack = []
for i, line in enumerate(lines, 1):
    # Find all comment starts
    pos = 0
    while True:
        start = line.find('(*', pos)
        if start == -1:
            break
        comment_stack.append((i, start))
        pos = start + 2
    
    # Find all comment ends
    pos = 0
    while True:
        end = line.find('*)', pos)
        if end == -1:
            break
        if comment_stack:
            comment_stack.pop()
        else:
            print(f"Extra comment close at line {i}, column {end}")
        pos = end + 2

if comment_stack:
    print(f"Unclosed comments:")
    for line, col in comment_stack:
        print(f"  Line {line}, column {col}")
        print(f"  Content: {lines[line-1].strip()}")