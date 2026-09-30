#!/usr/bin/env python3
"""Char-signedness census.  Plain `char` is unsigned on aarch64 and signed on
x86_64 (both psABIs).  The aarch64 build was repeated with -fsigned-char (C and
C++), everything else equal; a function whose normalised machine code changes is
one whose semantics MAY depend on the signedness of plain char (an
over-approximation: a changed function may still be equivalent).  A function
whose code is unchanged provably does not depend on it, for this compiler.
Normalisation: addresses, branch targets, PC-relative page/offset immediates and
symbol+offset annotations are removed; mnemonics, registers and other
immediates are kept."""
import re, sys, collections
FN = re.compile(r'^[0-9a-f]+ <(.+)>:$')
INS = re.compile(r'^\s+[0-9a-f]+:\s+(\S+)\s*(.*)$')
def load(p):
    """Functions keyed by name#k (k-th symbol of that name: static functions of
    different files may share a name, e.g. TeX's expand and kpathsea's).
    A branch into a linker veneer for Cortex-A53 erratum 843419
    (e843419@...: the linker moves one load there, by address) is replaced by
    the veneer's first instruction, so layout does not count as a change."""
    fns = collections.OrderedDict(); cur = None; seen = collections.Counter(); raw_ins = {}
    lines = open(p, errors='replace').read().split('\n')
    for raw in lines:
        m = FN.match(raw)
        if m:
            seen[m.group(1)] += 1; cur = f"{m.group(1)}#{seen[m.group(1)]}"; fns[cur] = []; continue
        m = INS.match(raw)
        if m and cur:
            op, a = m.group(1), m.group(2)
            v = re.search(r'<(e843419@[^>+]*)>', a)
            if op == 'b' and v:
                fns[cur].append(('VENEER', v.group(1))); continue
            a = re.sub(r'<[^>]*>', '<s>', a)
            a = re.sub(r'//.*', '', a)
            if op in ('adrp', 'adr', 'bl', 'b', 'cbz', 'cbnz', 'tbz', 'tbnz') or op.startswith('b.'):
                a = re.sub(r'\b[0-9a-f]{3,}\b', 'A', a)
            if op == 'ldr' and re.search(r',\s*[0-9a-f]+\s*<', m.group(2)):
                a = 'LITERAL'
            a = re.sub(r'#0x[0-9a-f]+\]', '#OFF]', a) if op in ('ldr', 'str', 'add') and ':lo12:' in a else a
            fns[cur].append(op + ' ' + a.strip())
    for f, ins in fns.items():
        for i, x in enumerate(ins):
            if isinstance(x, tuple):
                ins[i] = fns[x[1] + '#1'][0]
    return fns
base, sc = load(sys.argv[1]), load(sys.argv[2])
# adrp/add pairs: the low-12 page offset of a global moves when layout moves; drop add/ldr immediates that follow an adrp into the same register
def norm(ins):
    out = []; pagereg = set()
    for i in ins:
        op, _, a = i.partition(' ')
        regs = [r.strip() for r in a.split(',')]
        if op == 'adrp':
            pagereg.add(regs[0]); out.append('adrp ' + regs[0] + ',PAGE'); continue
        if op in ('add', 'ldr', 'str', 'ldrb', 'strb', 'ldrsw', 'ldrh', 'ldp', 'stp') and any(r.lstrip('[') in pagereg for r in regs[1:3]):
            a = re.sub(r'#(0x)?[0-9a-f]+', '#LO12', a)
        out.append(op + ' ' + a)
    return out
changed, same, only = [], 0, []
for f in sorted(set(base) | set(sc)):
    if f not in base or f not in sc:
        only.append(f); continue
    if norm(base[f]) == norm(sc[f]): same += 1
    else: changed.append(f)
print(f"functions: {len(set(base)|set(sc))}; identical after normalisation: {same}; changed: {len(changed)}; present in one build only: {len(only)}")
with open(sys.argv[3], 'w') as o:
    for f in changed: o.write('changed\t' + f + '\n')
    for f in only: o.write('one-build-only\t' + f + '\n')
