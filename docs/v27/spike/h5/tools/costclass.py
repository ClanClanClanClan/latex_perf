#!/usr/bin/env python3
"""costclass.py SAMPLE.txt...: macOS `sample` top-of-stack counts grouped by what a further change of
design would remove (spike H.5, stage-1 correction, H5-heap-design.md §3.4).

selfprof.py's classes follow the code's modules. These follow the candidate changes:
  Z     everything a native-int63 value representation would replace: zarith's OCaml and C code,
        the C-call trampoline into its stubs (caml_c_call, and the TLS lookup _tlv_get_addr the
        stubs make for the domain state), the custom blocks they allocate (boxed Z, boxed Int64),
        and the extracted BinInt/BinPos/Uint63/Sint63 code and the T1/T2 realizers (Zr);
  interp    the interpreter's own code (Interp): IR dispatch, labels, argument lists;
  storage   the arrays (Parray/Parrayc/PArray0) and the heap model over them (Values);
  gc        OCaml's own allocator slow path, minor and major GC, write barrier;
  io        the C boundary (Boundary), where the I/O lists are read and extended;
  other     the rest (named).
Prints, per file, the share of each class; with several files, also their sum.
"""
import collections, re, sys

RULES = [
    ("Z", r"camlZ\.|ml_z_|camlBig_int_Z\.|caml_c_call$|_tlv_get_addr|alloc_custom_gen|caml_alloc_custom|"
          r"caml_copy_int64|camlBinInt\.|camlBinPos\.|camlBinNat\.|camlBinPosDef\.|camlUint0\.|camlSint0\.|camlZr\.|"
          r"__gmpn_|__gmpz_|DYLD-STUB\$\$__gmp"),
    ("interp", r"camlInterp\."),
    ("storage", r"camlParray|camlPArray0\.|camlValues\.|caml_make_vect|caml_array_"),
    ("gc", r"caml_alloc_small|caml_alloc_shr|caml_alloc$|caml_call_gc|caml_garbage_collection|oldify|caml_empty_minor|"
           r"caml_minor|minor_|mark|sweep|caml_major|do_some|major_|ephe|caml_darken|caml_modify|DYLD-STUB\$\$caml_modify|"
           r"caml_remember|realloc_generic_table|caml_scan_stack|caml_find_frame_descr|caml_shared_try_alloc|"
           r"try_update_object_header|pool_|caml_process_pending|compact"),
    ("io", r"camlBoundary\."),
]


def cls(f):
    for name, rx in RULES:
        if re.search(rx, f):
            return name
    return "other"


def read(path):
    txt = open(path).read().split("Sort by top of stack")[1].splitlines()[1:]
    c, other = collections.Counter(), collections.Counter()
    for l in txt:
        m = re.match(r"\s+(\S+)\s+\(in ([^)]+)\)\s+(\d+)", l)
        if m:
            k = cls(m.group(1)); c[k] += int(m.group(3))
            if k == "other":
                other[m.group(1)] += int(m.group(3))
    return c, other


tot_c, tot_o = collections.Counter(), collections.Counter()
for p in sys.argv[1:]:
    c, o = read(p); tot_c.update(c); tot_o.update(o)
    n = sum(c.values())
    print(f"{p.split('/')[-1]}: {n} samples  " + "  ".join(f"{k} {100*c[k]/n:.1f}%" for k in ("Z", "interp", "storage", "gc", "io", "other")))
if len(sys.argv) > 2:
    n = sum(tot_c.values())
    print(f"ALL: {n} samples  " + "  ".join(f"{k} {100*tot_c[k]/n:.1f}%" for k in ("Z", "interp", "storage", "gc", "io", "other")))
ZSUB = [  # what the Z class is made of (top-of-stack function names)
    ("conversions Uint63/Sint63/Int64 <-> Z", r"camlUint0\.|camlSint0\.|camlZr\.|extract|of_int64|to_int64|copy_int64|int_of_big_int|camlZ\.to_int|camlZ\.of_int"),
    ("boxing (custom blocks)", r"alloc_custom"),
    ("C-call trampoline and TLS", r"caml_c_call$|_tlv_get_addr"),
    ("arithmetic and comparison", r"."),
]
zs = collections.Counter()
for p in sys.argv[1:]:
    txt = open(p).read().split("Sort by top of stack")[1].splitlines()[1:]
    for l in txt:
        m = re.match(r"\s+(\S+)\s+\(in ([^)]+)\)\s+(\d+)", l)
        if m and cls(m.group(1)) == "Z":
            zs[next(k for k, rx in ZSUB if re.search(rx, m.group(1)))] += int(m.group(3))
n = sum(tot_c.values())
print("Z class, of all samples: " + ", ".join(f"{k} {100*zs[k]/n:.1f}%" for k, _ in ZSUB))
print("largest 'other' entries: " + ", ".join(f"{f} {100*v/n:.1f}%" for f, v in tot_o.most_common(8)))
