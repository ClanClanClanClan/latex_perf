#!/usr/bin/env python3
"""selfprof.py SAMPLE.txt: group macOS `sample`'s top-of-stack counts by cost class (spike H.5 stage 1)."""
import re, sys, collections
lines = open(sys.argv[1]).read().split("Sort by top of stack")[1].splitlines()[1:]
rows = []
for l in lines:
    m = re.match(r"\s+(\S+)\s+\(in ([^)]+)\)\s+(\d+)", l)
    if m: rows.append((m.group(1), int(m.group(3))))
def cls(f):
    if re.match(r"camlUint0\.|camlSint0\.", f): return "Uint63/Sint63 <-> Z conversion (extracted Coq library code)"
    if re.match(r"camlBinInt\.|camlBinPos\.|camlBinNat\.|camlBinPosDef\.", f): return "BinInt/BinPos (extracted Coq Z/positive library code)"
    if re.match(r"ml_z_|camlZ\.|camlBig_int_Z\.", f): return "zarith (Z arithmetic)"
    if re.match(r"camlParray\.|camlParrayc\.|camlPArray0\.", f): return "persistent arrays (Parray)"
    if re.match(r"camlInterp\.", f): return "interpreter (Interp)"
    if re.match(r"camlValues\.", f): return "values/storage (Values)"
    if re.match(r"camlBoundary\.", f): return "C boundary (Boundary)"
    if re.match(r"camlProg|camlMain0|camlCMain|camlPoolData", f): return "program data / main"
    if re.match(r"caml_alloc|caml_shared_try_alloc|caml_c_call|try_update_object_header|alloc_|caml_call_gc|caml_alloc_small", f): return "allocation"
    if re.match(r"oldify|caml_empty_minor|caml_minor|minor_|caml_oldify", f): return "minor GC (promotion)"
    if re.match(r"pool_sweep|mark|caml_major|sweep|caml_darken|ephe|caml_mark|do_some|major_|caml_compact|compact", f): return "major GC"
    if re.match(r"caml_modify|caml_remember|caml_ref_table|realloc_generic_table", f): return "write barrier"
    if re.match(r"__mmap|_tlv_get_addr|__bzero|_platform_mem|madvise|__munmap", f): return "system (mmap/TLS/memset)"
    return "other: " + f
agg = collections.Counter()
for f, n in rows: agg[cls(f)] += n
tot = sum(agg.values())
print(f"total top-of-stack samples: {tot}")
for k, v in agg.most_common(): print(f"{v:8d} {100*v/tot:5.1f}%  {k}")
