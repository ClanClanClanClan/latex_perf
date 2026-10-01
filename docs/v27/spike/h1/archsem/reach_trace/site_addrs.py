#!/usr/bin/env python3
"""Instruction addresses of the candidate DIVERGES sites (review round 4, MEDIUM-2).

usage: site_addrs.py <amd64.dis> <arm64.dis> <census_insns.tsv.gz> <classification.tsv> > site_addrs.tsv

Pure: reads the `objdump -d -l --no-show-raw-insn` listings of the two
unstripped reference builds (the same files census.py read: recipes.md,
archsem/dis.sh) and repeats census.py's scan, keeping each instruction's
ADDRESS. It writes one row per DIV/F2I instruction of every CANDIDATE site:
a site whose `argued` column in classification.tsv is DIVERGES (round 2/3's
hand attribution of a probe to the site). The candidates come from the argued
column, not the verdict, because the verdict is now computed FROM this trace
(classify.py): a candidate the trace does not confirm keeps its row here.
    class  site  arch  function  addr  offset  insn
and asserts that, site by site and architecture by architecture, the rows are
exactly census_insns.tsv.gz's rows (same multiset of function, file, line,
instruction): the addresses are those of the census's instructions, no more,
no fewer. addr is the link-time address (amd64: absolute, the build is not
PIE; arm64: an offset from the load base, the build is PIE); offset is addr
minus the entry of the function symbol, which is how gen_gdb.py places the
breakpoint (symbol + offset is right whatever the load base)."""
import collections
import csv
import gzip
import re
import sys

amd, arm, ins_path, cls_path = sys.argv[1:5]
FN = re.compile(r'^[0-9a-f]+ <(.+)>:$')
LOC = re.compile(r'^(/\S+):(\d+)')
INS = re.compile(r'^\s+([0-9a-f]+):\s+(\S+)\s*(.*)$')
TABLE = {'x86_64': [('F2I', re.compile(r'^v?cvtt?s[sd]2si[lq]?$|^v?cvtt?p[sd]2(pi|dq)$|^fistt?p?[slq]?$')),
                    ('DIV', re.compile(r'^i?div[bwlq]?$'))],
         'aarch64': [('F2I', re.compile(r'^fcvt[zanmp][su]$|^fjcvtzs$')),
                     ('DIV', re.compile(r'^[su]div$'))]}


def scan(path, arch):
    fn = file = None
    line = entry = 0
    for raw in open(path, errors='replace'):
        raw = raw.rstrip('\n')
        m = FN.match(raw)
        if m:
            fn, file, line, entry = m.group(1), None, 0, int(raw.split()[0], 16)
            continue
        m = LOC.match(raw)
        if m:
            file = m.group(1).split('/texk/')[-1].split('/libs/')[-1].split('/Work/')[-1]
            line = int(m.group(2))
            continue
        m = INS.match(raw)
        if not m:
            continue
        a, op, args = m.group(1), m.group(2), m.group(3)
        for cls, rx in TABLE[arch]:
            if rx.match(op):
                yield cls, fn, file or '-', line, op + ' ' + args.split('#')[0].strip(), int(a, 16), entry


def site(f, fn, line):
    return fn if f == '-' else f"{f.split('/')[-1]}:{line}"


div = {(r['class'], r['site']) for r in csv.DictReader(open(cls_path), delimiter='\t') if r['argued'] == 'DIVERGES'}
want = collections.Counter()
for r in csv.DictReader(gzip.open(ins_path, 'rt'), delimiter='\t'):
    k = (r['class'], site(r['file'], r['function'], r['line']))
    if k in div:
        want[(k, r['arch'], r['function'], r['file'], r['line'], r['insn'])] += 1
got, rows = collections.Counter(), []
for path, arch in ((amd, 'x86_64'), (arm, 'aarch64')):
    for cls, fn, f, line, insn, a, entry in scan(path, arch):
        k = (cls, site(f, fn, line))
        if k in div:
            got[(k, arch, fn, f, str(line), insn)] += 1
            rows.append((cls, k[1], 'amd64' if arch == 'x86_64' else 'arm64', fn, f'0x{a:x}', f'0x{a - entry:x}', insn))
assert got == want, ('the listings do not reproduce the census', got - want, want - got)
assert {(r[0], r[1]) for r in rows} == div, div - {(r[0], r[1]) for r in rows}
print('class\tsite\tarch\tfunction\taddr\toffset\tinsn')
for r in sorted(rows, key=lambda r: (r[1], r[0], r[2], int(r[4], 16))):
    print('\t'.join(r))
