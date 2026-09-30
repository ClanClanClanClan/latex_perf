#!/usr/bin/env python3
"""Census of instruction-level semantic divergences between the x86_64 and aarch64
builds of pdfTeX r78081 (unstripped reference builds, byte-identical to the pinned
binaries after strip).  Input: `objdump -d -l --no-show-raw-insn` of each binary.

Classes (ISA facts, each a C construct whose result the C standard leaves
undefined or implementation-defined and whose hardware answer differs):
  F2I   floating -> integer conversion.  x86 cvtt*/cvt* return the 'integer
        indefinite' INT_MIN (0x80..0) for NaN and out-of-range; aarch64
        fcvtz*/fcvta*/... saturate, and give 0 for NaN.
  DIV   integer division / remainder.  x86 idiv/div raise #DE (SIGFPE) on a zero
        divisor and on INT_MIN / -1; aarch64 sdiv/udiv return 0 and INT_MIN
        (and the remainder, computed with msub, returns the dividend and 0).
  LDBL  long double.  x86: x87 80-bit extended; aarch64: IEEE binary128 in
        software (__*tf* calls).  Any use gives different roundings.
  FMA   fused multiply-add on aarch64 (census of review round 1, repeated here).
Output: one TSV row per instruction: arch class function file line insn."""
import re, sys, collections
FN = re.compile(r'^[0-9a-f]+ <(.+)>:$')
LOC = re.compile(r'^(/\S+):(\d+)')
INS = re.compile(r'^\s+[0-9a-f]+:\s+(\S+)\s*(.*)$')
X86 = [('F2I', re.compile(r'^v?cvtt?s[sd]2si[lq]?$|^v?cvtt?p[sd]2(pi|dq)$|^fistt?p?[slq]?$')),
       ('DIV', re.compile(r'^i?div[bwlq]?$')),
       ('LDBL', re.compile(r'^f(?!istt?p)[a-z0-9]*$'))]   # every x87 mnemonic (SSE ones do not start with f)
ARM = [('F2I', re.compile(r'^fcvt[zanmp][su]$|^fjcvtzs$')),
       ('DIV', re.compile(r'^[su]div$')),
       ('FMA', re.compile(r'^fn?m(add|sub)$'))]
LDBL_CALL = re.compile(r'<(__[a-z]+tf[0-9a-z]*|__[a-z]+tf)>')
def scan(path, arch):
    table = X86 if arch == 'x86_64' else ARM
    fn = file = None; line = 0
    for raw in open(path, errors='replace'):
        raw = raw.rstrip('\n')
        m = FN.match(raw)
        if m: fn = m.group(1); file = None; line = 0; continue
        m = LOC.match(raw)
        if m:
            file = m.group(1).split('/texk/')[-1].split('/libs/')[-1].split('/Work/')[-1]; line = int(m.group(2)); continue
        m = INS.match(raw)
        if not m: continue
        op, args = m.group(1), m.group(2)
        for cls, rx in table:
            if rx.match(op):
                yield arch, cls, fn, file or '-', line, op + ' ' + args.split('#')[0].strip()
        if arch == 'aarch64' and op == 'bl':
            c = LDBL_CALL.search(args)
            if c: yield arch, 'LDBL', fn, file or '-', line, 'bl ' + c.group(1)
rows = list(scan(sys.argv[1], 'x86_64')) + list(scan(sys.argv[2], 'aarch64'))
with open(sys.argv[3], 'w') as o:
    o.write('arch\tclass\tfunction\tfile\tline\tinsn\n')
    for r in rows: o.write('\t'.join(map(str, r)) + '\n')
cnt = collections.Counter((r[0], r[1]) for r in rows)
for k in sorted(cnt): print(*k, cnt[k])
