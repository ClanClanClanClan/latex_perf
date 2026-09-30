#!/usr/bin/env python3
"""Map every function of the aarch64 reference build to its source file, and
join the -fwrapv and -fsigned-char change lists to it (review round 3, M2).

Input: `objdump -d -l` of the unstripped aarch64 build (arm64.dis, dis.sh in
../recipes.md), and scdiff.py's outputs wrapv_changed.txt, signedchar_changed.txt.
A function's file is the first DWARF line record after its symbol (its own
location; code gcc inlined from elsewhere follows it). No record: NOLINE (xpdf and
other code compiled without -g, and linker veneers).
scope: TRANSLATED = pdftex0.c or pdftexini.c, i.e. web2c's C for the tangled
Pascal program that H.2 translates (PS makes its UB Stuck); every other file is
BOUNDARY (hand-modelled in ADR-015's plan, so PS's rule does not reach it).
Output: functions.tsv, one row per function name#k of the union of the builds
compared (base plus the one-build-only rows of each change list)."""
import re, sys, collections
FN = re.compile(r'^[0-9a-f]+ <(.+)>:$')
LOC = re.compile(r'^(/[^ ]+):\d+')
dis, wv, sc, out = sys.argv[1:5]
seen = collections.Counter(); files = collections.OrderedDict(); cur = None
for raw in open(dis, errors='replace'):
    raw = raw.rstrip('\n')
    m = FN.match(raw)
    if m:
        seen[m.group(1)] += 1; cur = f"{m.group(1)}#{seen[m.group(1)]}"; files[cur] = 'NOLINE'; continue
    m = LOC.match(raw)
    if m and cur and files[cur] == 'NOLINE':
        p = m.group(1)
        p = re.sub(r'^.*/(\.\./)+', '', p) if '/../' in p else re.sub(r'^/work/repo/Work/', 'Work/', p)
        files[cur] = p
def lst(p):
    d = {}
    for l in open(p):
        k, f = l.rstrip('\n').split('\t'); d[f] = k
    return d
W, S = lst(wv), lst(sc)
names = list(files) + sorted((set(W) | set(S)) - set(files))
def scope(f):
    return 'TRANSLATED' if f in ('Work/texk/web2c/pdftex0.c', 'Work/texk/web2c/pdftexini.c') else 'BOUNDARY'
with open(out, 'w') as o:
    o.write('function\tfile\tscope\twrapv\tsignedchar\n')
    for n in names:
        f = files.get(n, 'NOT-IN-BASE')
        o.write(f"{n}\t{f}\t{scope(f)}\t{W.get(n, 'same')}\t{S.get(n, 'same')}\n")
