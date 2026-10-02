#!/usr/bin/env python3
"""Compare two decompressed pdfTeX format streams section by section, as far as the string
pool (store_fmt_file's order in the tangled pdftex.p: the header, then poolptr, strptr,
strstart[], strpool[]); then the rest byte by byte. usage: fmtdiff.py A B"""
import json, struct, sys


def parse(d):
    o = 0

    def i32():
        nonlocal o
        v = struct.unpack('>i', d[o:o + 4])[0]
        o += 4
        return v
    r = {'magic': i32()}
    x = i32()
    r['engine'] = d[o:o + x].rstrip(b'\0').decode()
    o += x
    r['magic2'] = i32()
    o += 768                                   # xord, xchr, xprn
    for k in ('magic3', 'hashhigh', 'etex_mode', 'membot', 'memtop', 'eqtbsize', 'hashprime', 'hyphprime',
              'mltex_magic', 'mltex_on', 'enctex_magic', 'enctex_on'):
        r[k] = i32()
    if r['enctex_on']:
        o += 640
    pp, sp = i32(), i32()
    ss = struct.unpack('>%di' % (sp + 1), d[o:o + 4 * (sp + 1)])
    o += 4 * (sp + 1)
    return r, pp, sp, ss, d[o:o + pp], o + pp


a, b = open(sys.argv[1], 'rb').read(), open(sys.argv[2], 'rb').read()
ra, ppa, spa, ssa, pa, oa = parse(a)
rb, ppb, spb, ssb, pb, ob = parse(b)
out = {'sizes': [len(a), len(b)], 'header_differs': {k: [ra[k], rb[k]] for k in ra if ra[k] != rb[k]},
       'strings': [spa, spb], 'pool_bytes': [ppa, ppb],
       'A_strings_are_a_prefix_of_B': ssa[:spa + 1] == ssb[:spa + 1] and pa == pb[:ppa],
       'strings_only_in_B': [pb[ssb[s]:ssb[s + 1]].decode('latin-1') for s in range(spa, spb)]}
ta, tb = a[oa:], b[ob:]
out['after_pool'] = {'bytes': [len(ta), len(tb)],
                     'differing_bytes_at_equal_offsets': sum(1 for k in range(min(len(ta), len(tb))) if ta[k] != tb[k])}
print(json.dumps(out, indent=1))
