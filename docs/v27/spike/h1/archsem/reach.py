#!/usr/bin/env python3
"""Machine check for a NOT-REACHED verdict (review round 3): a function is
unreferenced in a build iff (1) no instruction outside its own body names it
(`<f>` or `<f+off>` in `objdump -d` output: direct calls, branches, adrp/add
address computations) and (2) no aarch64 adrp+add pair computes its entry address, and (3) its entry address does not occur as an 8-byte
little-endian word anywhere in the ELF file (a function pointer in data, or the
addend of a PIE RELATIVE relocation, over-approximated: any matching word counts).
Usage: reach.py <objdump -d output> <unstripped ELF> <function>...
Prints one line per function: <build> <function> UNREFERENCED|REFERENCED <why>."""
import re, sys, struct
dis, elf, names = sys.argv[1], sys.argv[2], sys.argv[3:]
FN = re.compile(r'^([0-9a-f]+) <(.+)>:$')
addr, refs, cur = {}, {n: [] for n in names}, None
pages, sums = {}, []
pat = re.compile(r'<(' + '|'.join(map(re.escape, names)) + r')(\+0x[0-9a-f]+)?>')
for line in open(dis, errors='replace'):
    m = FN.match(line.rstrip('\n'))
    if m:
        cur = m.group(2)
        if cur in refs:
            assert cur not in addr, f'{cur}: two symbols of that name; this check needs one'
            addr[cur] = int(m.group(1), 16)
        continue
    for mm in pat.finditer(line):
        if mm.group(1) != cur:
            refs[mm.group(1)].append(f'{cur}: {line.strip()}')
    # aarch64 address materialisation: adrp xR, PAGE then add xD, xR, #lo12
    # (objdump names only the page); every such pair's sum is checked below
    mi = re.match(r'\s+[0-9a-f]+:\s+(adrp|add)\s+(\w+),\s*(\w+|[0-9a-f]+)(?:,\s*#(0x[0-9a-f]+|\d+))?', line)
    if mi and mi.group(1) == 'adrp':
        pages[mi.group(2)] = int(mi.group(3).split()[0], 16)
    elif mi and mi.group(1) == 'add' and mi.group(4) and mi.group(3) in pages:
        sums.append((pages[mi.group(3)] + int(mi.group(4), 0), cur, line.strip()))
blob = open(elf, 'rb').read()
for n in names:
    if n not in addr:
        print(sys.argv[1], n, 'ABSENT', 'no symbol of that name in this build'); continue
    refs[n] += [f'{c}: {l}' for a, c, l in sums if a == addr[n] and c != n]
    word = struct.pack('<Q', addr[n])
    hits = blob.count(word)
    if refs[n] or hits:
        print(dis, n, 'REFERENCED', f'{len(refs[n])} text refs, {hits} data words', refs[n][:3])
    else:
        print(dis, n, 'UNREFERENCED', f'entry 0x{addr[n]:x}: no text ref, no data word')
