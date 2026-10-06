#!/usr/bin/env python3
"""callers.py SAMPLE.txt REGEX: inclusive samples of the functions matching REGEX, grouped by
their nearest caller that does not match (macOS `sample` call tree; spike H.5 stage 1)."""
import re, sys, collections
txt = open(sys.argv[1]).read().split("Call graph:")[1].split("Total number in stack")[0]
pat = re.compile(sys.argv[2])
stack = []  # (depth, name)
agg = collections.Counter(); tot = 0
for l in txt.splitlines():
    m = re.match(r"^([\s+!:|]*)(\d+)\s+(\S+)", l)
    if not m: continue
    depth = len(m.group(1)); n = int(m.group(2)); f = m.group(3)
    while stack and stack[-1][0] >= depth: stack.pop()
    if pat.search(f) and not (stack and pat.search(stack[-1][1])):
        caller = next((s[1] for s in reversed(stack) if not pat.search(s[1])), "?")
        agg[caller] += n; tot += n
    stack.append((depth, f))
print(f"inclusive samples in {sys.argv[2]}: {tot}")
for k, v in agg.most_common(25): print(f"{v:8d} {100*v/max(tot,1):5.1f}%  {k}")
