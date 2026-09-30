#!/usr/bin/env python3
"""Recompute the H.1 report's numbers from the evidence committed beside it.

usage: python3 docs/v27/spike/h1/verify_h1.py [--report PATH]

Pure: reads only files under docs/v27/spike/h1/ and the report; runs no TeX.
Two kinds of check, both from PRIMARY committed data, never from a number
stored in the report itself:
  1. every comparison summary (diffs/r1/*.json) has the verdict counts the
     report quotes, and the report quotes them;
  2. every aarch64 FMA site outside xpdf (fma/fma_sites_aarch64.tsv, from the
     unstripped build's DWARF line table) is NAMED in the report's §5.1
     classification. A site the report does not classify fails (review round 1:
     round 0 classified two functions and generalised to the rest);
  3. (review round 2) every integer-division and float-to-int site of BOTH
     binaries (archsem/census_insns.tsv.gz) has exactly one verdict in
     archsem/classification.tsv, the verdict counts and the probes' recorded
     outcomes are the ones the report quotes, and diffs/r2 (every comparison
     re-run by the round-2 comparator) has r1's counts;
  4. (review round 3) a site's verdict follows from evidence: every DIVERGES
     row names a committed probe whose recorded outcomes DIFFER between the
     architectures (any line: rc, messages, /Rect, output hashes), every
     NOT-REACHED row's functions are UNREFERENCED in both builds (reach.out),
     scopes follow from the file; and every -fwrapv/-fsigned-char total is
     recomputed from functions.tsv.
Exit 0 when all hold, 1 otherwise, listing each failure."""
import json
import re
import sys
from collections import Counter
from pathlib import Path

H = Path(__file__).resolve().parent
report = Path(sys.argv[sys.argv.index("--report") + 1]) if "--report" in sys.argv else H.parent / "H1-report.md"
R = report.read_text()
fails = []


def diff(name):
    return json.loads((H / "diffs" / "r1" / f"diff_{name}.json").read_text())


def expect(name, documents, verdicts, rcs=None, quote=()):
    d = diff(name)
    if d["documents"] != documents or d["missing_on_b"] != 0:
        fails.append(f"{name}: {d['documents']} documents ({d['missing_on_b']} missing), expected {documents}")
    if d["verdicts"] != verdicts:
        fails.append(f"{name}: verdicts {d['verdicts']}, expected {verdicts}")
    if rcs is not None and d["final_rc_of_a"] != rcs:
        fails.append(f"{name}: final rcs {d['final_rc_of_a']}, expected {rcs}")
    for q in quote:
        if q not in R:
            fails.append(f"{name}: the report does not quote {q!r}")
    return d


# (i) evidence documents, pinned vs reference build, protocol clock
expect("strict__arm64-pinned__vs__strict__arm64-ref", 3907,
       {"IDENTICAL": 3697, "EQUAL_MASKED": 210}, {"rc0": 939, "rc1": 2968},
       ("**3,907**", "3,697 byte-identical", "210 equal", "939 × 0, 2,968 × 1"))
# (ii) real papers, protocol clock: 7 differ, 2 in a log and 5 in a PDF
d = expect("real__arm64-pinned__vs__real__arm64-ref", 200,
           {"IDENTICAL": 130, "EQUAL_MASKED": 63, "DIFF": 7}, {"rc0": 189, "rc1": 11},
           ("193 agree (130 byte-identical, 63 masked)", "**7 differ", "189 × 0, 11 × 1"))
kinds = Counter()
for notes in d["diffs"].values():
    exts = {re.match(r"p\d+ \S+\.(\w+):", n).group(1) for n in notes if re.match(r"p\d+ \S+\.(\w+):", n)}
    kinds["log" if "log" in exts else "pdf" if exts == {"pdf"} else "other"] += 1
if kinds != Counter({"pdf": 5, "log": 2}):
    fails.append(f"real protocol-clock DIFFs by file kind {dict(kinds)}, expected 5 pdf + 2 log")
elif "2 of them in the log" not in R or "5\nin the PDF" not in R and "5 in the PDF" not in R:
    fails.append("the report does not state the 2 log / 5 PDF split of the 7")
# (ii') real papers, fixed clock
expect("real-fixclock__arm64-pinned__vs__real-fixclock-refonly__arm64-ref", 200,
       {"IDENTICAL": 186, "EQUAL_MASKED": 14}, {"rc0": 189, "rc1": 11},
       ("**200 agree**: 186 byte-identical, 14 masked",))
# (iii) traces
expect("strict20-trace__arm64-pinned__vs__strict20-trace__arm64-ref", 20,
       {"IDENTICAL": 19, "EQUAL_MASKED": 1}, None, ("19 byte-identical, 1 banner-masked",))
expect("real20-trace__arm64-pinned__vs__real20-trace__arm64-ref", 20,
       {"DIFF": 14, "IDENTICAL": 3, "EQUAL_MASKED": 3}, None, ("Under the real clock, 14 differ",))
expect("real20-trace-fixclock__arm64-pinned__vs__real20-trace-fixclock-refonly__arm64-ref", 20,
       {"IDENTICAL": 17, "EQUAL_MASKED": 3}, {"rc0": 18, "rc1": 2}, ("20 agree**, 17 byte-identical",))
expect("strict20-trace-fixclock__arm64-pinned__vs__strict20-trace-fixclock-refonly__arm64-ref", 20,
       {"IDENTICAL": 20}, None, ())
# cross-architecture (amd64 emulated)
x = expect("real-fixclock__amd64-pinned__vs__real-fixclock__arm64-pinned", 200,
           {"IDENTICAL": 186, "EQUAL_MASKED": 14}, {"rc0": 189, "rc1": 11},
           ("**200 agree**: 186 byte-identical, 14 masked",))
if x["masks_needed"].get("pdf:pdf-canonical-subset-tag") != 4:
    fails.append(f"cross real: canonical PDF mask needed {x['masks_needed'].get('pdf:pdf-canonical-subset-tag')}, report says 4")
expect("strict8-fixclock__amd64-pinned__vs__strict8-fixclock__arm64-pinned", 489,
       {"IDENTICAL": 489}, None, ("**489 byte-identical**",))
expect("strict20-trace-fixclock__amd64-pinned__vs__strict20-trace-fixclock__arm64-pinned", 20,
       {"IDENTICAL": 20}, None, ("**20 byte-identical**",))
expect("real20-trace-fixclock__amd64-pinned__vs__real20-trace-fixclock__arm64-pinned", 20,
       {"IDENTICAL": 17, "EQUAL_MASKED": 3}, {"rc0": 18, "rc1": 2}, ("Final rc 18 × 0, 2 × 1 on both",))
# the 13 pre-guard amd64 grades, re-graded in a fresh guarded container
expect("real13-fixclock-regrade2__amd64-pinned__vs__real-fixclock__arm64-pinned", 13,
       {"IDENTICAL": 11, "EQUAL_MASKED": 2}, {"rc0": 12, "rc1": 1}, ("**13 of 13 agree**",))
expect("real13-fixclock-regrade2__amd64-pinned__vs__real-fixclock__amd64-pinned", 13,
       {"IDENTICAL": 11, "EQUAL_MASKED": 2}, {"rc0": 12, "rc1": 1}, ())
# disclosed superseded runs
expect("strict-fixclock__amd64-pinned__vs__strict-fixclock__arm64-pinned", 53, {"IDENTICAL": 53}, None,
       ("53 of 53 identical",))

# FMA sites
rows = [ln.split("\t") for ln in (H / "fma" / "fma_sites_aarch64.tsv").read_text().splitlines() if ln]
if len(rows) != 524 or "524" not in R:
    fails.append(f"FMA sites: {len(rows)} in the map, report quotes 524")
c_funcs = Counter(r[0] for r in rows if not r[0].startswith("_Z"))
if sum(c_funcs.values()) != 39 or "**39**" not in R:
    fails.append(f"FMA sites outside xpdf: {sum(c_funcs.values())}, report quotes 39")
sec = R[R.index("### 5.1"):R.index("### 5.2")]
for f, n in sorted(c_funcs.items()):
    if f"`{f}`" not in sec:
        fails.append(f"FMA site function `{f}` ({n} FMA) is not classified in §5.1")
for f, n in [("makeaccent", 2), ("hlistout", 2), ("pdfhlistout", 2), ("zpdfsetrule", 2), ("pdfsetmatrix", 8),
             ("do_matrixtransform", 2), ("read_jbig2_info", 2), ("read_pdf_info", 1), ("t1_scan_param", 4),
             ("ttf_read_post", 1)]:
    if c_funcs[f] != n or f"`{f}` ({n})" not in sec:
        fails.append(f"§5.1 count for `{f}`: map has {c_funcs[f]}, report must say `{f}` ({n})")
png = sum(n for f, n in c_funcs.items() if f.startswith("png_"))
if f"libpng ({png}:" not in sec:
    fails.append(f"§5.1 libpng count: map has {png}")
# the exhaustive/search outputs quoted in §5.1
for fn, pat in [("jbig2_exhaustive.out", r"differ: 0 \[\]"), ("pdfversion_exhaustive.out", r"with minor in 0\.\.9: 0$"),
                ("lexsim.out", r"N=300000 double-differs=29 float-differs=0 scaled-differs=0"),
                ("lexmid.out", r"float midpoints tried: 20000; numerals whose scaled width differs: 0"),
                ("matrix_search.out", r"tried 1705191; differing: 3")]:
    if not re.search(pat, (H / "fma" / fn).read_text(), re.M):
        fails.append(f"fma/{fn} does not show {pat!r}")
for q in ("29 of 300,000", "1,705,191", "109,092,170"):
    if q not in sec:
        fails.append(f"§5.1 does not quote {q}")

# ---- review round 2 ----------------------------------------------------------
# (a) the round-2 comparator (h1diff.py, canonical PDF form engaged only with a
#     Ghostscript intermediate) re-ran every comparison: same counts as r1
for f in sorted((H / "diffs" / "r1").glob("diff_*.json")):
    g = H / "diffs" / "r2" / f.name
    if not g.is_file():
        fails.append(f"diffs/r2/{f.name} missing")
        continue
    a, b = json.loads(f.read_text()), json.loads(g.read_text())
    for k in ("documents", "missing_on_b", "verdicts", "masks_needed", "final_rc_of_a"):
        if a[k] != b[k]:
            fails.append(f"{f.name}: r2 {k} {b[k]} != r1 {a[k]}")
    if sorted(a["diffs"]) != sorted(b["diffs"]):
        fails.append(f"{f.name}: r2 DIFF documents differ from r1")
# (b) the architecture-semantics census: every DIV/F2I site of both binaries
#     (recomputed from the instruction list) has exactly one verdict, and the
#     report's verdict counts are the classification's
import csv
import gzip
A = H / "archsem"
ins = list(csv.DictReader(gzip.open(A / "census_insns.tsv.gz", "rt"), delimiter="\t"))
nins = Counter((r["class"]) for r in ins if r["class"] in ("DIV", "F2I"))
sites = set()
for r in ins:
    if r["class"] not in ("DIV", "F2I"):
        continue
    f = r["file"]
    sites.add((r["class"], r["function"] if f == "-" else f"{f.split('/')[-1]}:{r['line']}"))
cls = list(csv.DictReader(open(A / "classification.tsv"), delimiter="\t"))
ck = Counter((r["class"], r["site"]) for r in cls)
for k in sorted(sites - set(ck)):
    fails.append(f"census site {k} has no verdict in archsem/classification.tsv")
for k in sorted(set(ck) - sites):
    fails.append(f"classification row {k} is not a census site")
for k, n in ck.items():
    if n != 1:
        fails.append(f"census site {k} has {n} verdicts")
if nins != Counter({"DIV": 620, "F2I": 474}) or "620 DIV\nand 474 F2I" not in R:
    fails.append(f"census instruction counts {dict(nins)}, report quotes 620 DIV and 474 F2I")
if len(sites) != 316 or "**316 sites**" not in R:
    fails.append(f"census sites {len(sites)}, report quotes 316")
# review round 3 (C-106): a verdict is computed from evidence, never argued
v = Counter(r["verdict"] for r in cls)
want = {"DIVERGES": 18, "NOT-REACHED": 4, "PS-STUCK": 76, "OPEN": 218}
if dict(v) != want:
    fails.append(f"classification verdicts {dict(v)}, report quotes {want}")
for r in cls:
    tr = r["site"].split(":")[0] in ("pdftex0.c", "pdftexini.c")
    if r["scope"] != ("TRANSLATED" if tr else "BOUNDARY"):
        fails.append(f"{r['site']}: scope {r['scope']} does not follow from its file")
    if r["verdict"] == "PS-STUCK" and r["scope"] != "TRANSLATED":
        fails.append(f"{r['site']}: PS-STUCK outside the translated program")
    if r["verdict"] == "OPEN" and r["scope"] != "BOUNDARY":
        fails.append(f"{r['site']}: OPEN in the translated program")
    if (r["verdict"] == "DIVERGES") != bool(r["probe"]):
        fails.append(f"{r['site']}: a DIVERGES row must name a probe, and only a DIVERGES row")
sc = Counter(r["scope"] for r in cls)
if sc != Counter({"TRANSLATED": 85, "BOUNDARY": 231}):
    fails.append(f"scopes {dict(sc)}, report quotes 85 translated, 231 boundary")
for q in ("| **DIVERGES** | **18** (9 translated, 9 boundary) |", "| NOT-REACHED | 4 |", "| PS-STUCK | 76 |",
          "| **OPEN** | **218** |", "the 227 boundary\n    division and conversion sites"):
    if q not in R:
        fails.append(f"§5.4 does not quote {q!r}")
op = Counter(r["group"] for r in cls if r["verdict"] == "OPEN")
if (op["xpdf"], op["libpng"], sum(op.values()) - op["xpdf"] - op["libpng"]) != (106, 46, 66):
    fails.append(f"OPEN by group {dict(op)}, report quotes 66 other, 46 libpng, 106 xpdf")
# NOT-REACHED: every function of the site UNREFERENCED in both builds (reach.out)
unref = {}
for ln in (A / "reach.out").read_text().splitlines():
    f = ln.split()
    unref.setdefault(f[2], set())
    if f[3] == "UNREFERENCED":
        unref[f[2]].add(f[1])
sites_fn = {(r["class"], r["site"]): r["functions"].split(",") for r in csv.DictReader(open(A / "census_sites.tsv"), delimiter="\t")}
for r in cls:
    if r["verdict"] == "NOT-REACHED":
        for fn in sites_fn[(r["class"], r["site"])]:
            if unref.get(fn) != {"arm64", "amd64"}:
                fails.append(f"{r['site']}: NOT-REACHED but {fn} is not UNREFERENCED in both builds (reach.out)")
# every DIVERGES row names a probe that exists and whose recorded outcomes differ
def blocks(arch):
    out, cur = {}, None
    for fn in sorted((A / "probes" / "out").glob(f"*-{arch}.out")):
        for ln in fn.read_text().splitlines():
            m = re.match(r"^(\S+) rc=(\d+)$", ln)
            if m:
                cur = m.group(1); out[cur] = [ln]
            elif re.match(r"^(\w+ )?RC=\d+$", ln) or ln in ("aarch64", "x86_64") or re.match(r"^[0-9a-f]{16}$", ln):
                cur = None
            elif cur:
                out[cur].append(ln)
    return {k: "\n".join(v).strip() for k, v in out.items()}
ba, bx = blocks("arm64"), blocks("amd64")
for r in cls:
    if r["verdict"] != "DIVERGES":
        continue
    pr = r["probe"]
    if not list((A / "probes").rglob(f"{pr}.tex")):
        fails.append(f"{r['site']}: probe {pr}.tex is not committed")
    if pr not in ba or pr not in bx:
        fails.append(f"{r['site']}: probe {pr} has no recorded outcome on both architectures")
    elif ba[pr] == bx[pr]:
        fails.append(f"{r['site']}: probe {pr}'s recorded outcomes are EQUAL on both architectures")
# the leaders set (review round 3): x diverges rc 0/136; every control equal
for d in ("hdvi", "vdvi", "hpdf", "vpdf"):
    if not (ba.get(f"lead-{d}-x", "").startswith(f"lead-{d}-x rc=0") and bx.get(f"lead-{d}-x", "").startswith(f"lead-{d}-x rc=136")):
        fails.append(f"probe lead-{d}-x: not rc 0 on aarch64 and 136 on x86_64")
    for c in ("xctl", "a", "c"):
        k = f"lead-{d}-{c}"
        if k not in ba or ba[k] != bx.get(k) or not ba[k].startswith(f"{k} rc=0"):
            fails.append(f"control {k}: not rc 0 with identical recorded output on both")
# functions.tsv: the -fwrapv / -fsigned-char totals, and their split by scope
fnr = list(csv.DictReader(open(A / "functions.tsv"), delimiter="\t"))
for col, lst, tot, ch, tr, bd in (("wrapv", "wrapv_changed.txt", 4280, 876, 413, 463),
                                   ("signedchar", "signedchar_changed.txt", 4280, 317, 3, 314)):
    listed = {ln.split("\t")[1] for ln in (A / lst).read_text().splitlines() if ln.startswith("changed\t")}
    rows_ch = [x for x in fnr if x[col] == "changed"]
    if {x["function"] for x in rows_ch} != listed:
        fails.append(f"functions.tsv {col}: changed set differs from {lst}")
    union = sum(1 for x in fnr if x["file"] != "NOT-IN-BASE" or x[col] != "same")
    got = (union, len(rows_ch), sum(x["scope"] == "TRANSLATED" for x in rows_ch), sum(x["scope"] == "BOUNDARY" for x in rows_ch))
    if got != (tot, ch, tr, bd):
        fails.append(f"functions.tsv {col}: (functions, changed, translated, boundary) = {got}, report quotes {(tot, ch, tr, bd)}")
wv_pdftex0 = sum(1 for x in fnr if x["wrapv"] == "changed" and x["file"].endswith("/pdftex0.c"))
wv_noline = sum(1 for x in fnr if x["wrapv"] == "changed" and x["file"] == "NOLINE")
bnd_union = sum(1 for x in fnr if x["scope"] == "BOUNDARY" and "changed" in (x["wrapv"], x["signedchar"]))
if (wv_pdftex0, wv_noline, bnd_union) != (396, 338, 649):
    fails.append(f"functions.tsv: wrapv pdftex0.c {wv_pdftex0}, NOLINE {wv_noline}, boundary union {bnd_union}; report quotes 396, 338, 649")
for q in ("**876 of 4,280 functions**", "**317 functions**", "**413 translated**", "**463 boundary**",
          "(338 in C++ without a line table", "(649 distinct, `functions.tsv`)", "3 translated, 314\nboundary"):
    if q not in R:
        fails.append(f"§5.4 does not quote {q!r}")
# (c) probe outcomes, from the recorded outputs of both architectures
def rcs(name):
    out = {}
    for ln in (A / "probes" / "out" / name).read_text().splitlines():
        m = re.match(r"^(\S+) rc=(\d+)$", ln)
        if m:
            out[m.group(1)] = int(m.group(2))
    return out
ra, rx = rcs("r-arm64.out"), rcs("r-amd64.out")
for doc, a, x in [("snapy0", 0, 136), ("snapy1", 0, 0), ("imgwide", 1, 0), ("jpgconv", 0, 1), ("jpgdiv", 1, 136),
                  ("jpgctrl", 0, 0), ("jpgbig", 0, 0), ("jpgconvneg", 1, 1), ("pdfboxnan", 1, 1), ("matnan", 0, 0)]:
    if (ra.get(doc), rx.get(doc)) != (a, x):
        fails.append(f"probe {doc}: recorded rc {ra.get(doc)}/{rx.get(doc)}, report says {a}/{x}")
qa = (A / "probes" / "out" / "q-arm64.out").read_text()
qx = (A / "probes" / "out" / "q-amd64.out").read_text()
if "[divself=-1]" not in qa or "[divself=1]" not in qx:
    fails.append("probe nh-intmin: divself is not -1 on aarch64 and 1 on x86_64")
# the full logs: identical once the one differing value (\\count3, printed by the
# \\message and again in the page's \\count0..9 list at shipout) is masked
def intmin_norm(arch, v):
    t = (A / "probes" / "out" / f"nh-intmin.{arch}.log").read_text().replace("\n", "")
    n0 = t.count(f"[divself={v}]") + t.count(f".-2147483648.{v}.0.2147483647.")
    t = t.replace(f"[divself={v}]", "[divself=V]").replace(f".-2147483648.{v}.0.2147483647.", ".-2147483648.V.0.2147483647.")
    return n0, t
na, la = intmin_norm("arm64", "-1")
nx, lx = intmin_norm("amd64", "1")
if (na, nx) != (2, 2) or la.split("(./nh-intmin.tex", 1)[1] != lx.split("(./nh-intmin.tex", 1)[1]:
    fails.append(f"probe nh-intmin: logs differ beyond \\count3 (masked {na}/{nx} occurrences)")
ta = (A / "probes" / "out" / "t-arm64.out").read_text()
tx = (A / "probes" / "out" / "t-amd64.out").read_text()
if "SlantFont value too big" not in ta or "SlantFont value too big" in tx:
    fails.append("probe slanthuge: the warning is not aarch64-only")
# (d) the full-range PDF-version check (review round 2 LOW)
pv = (H / "fma" / "pdfversion_full.out").read_text()
if "pairs 21474836470, differing 0; control (major=1, minor=-10) differs: yes" not in pv \
        or "self-check block (major 1..20000, minor -1000..-1): 100 differing" not in pv \
        or "21,474,836,470 pairs, 0 differ" not in R:
    fails.append("fma/pdfversion_full.out does not show 0 of 21,474,836,470 with a passing self-check, or the report does not quote it")

for f in fails:
    print("FAIL", f)
print(f"verify_h1: {'OK' if not fails else f'{len(fails)} failure(s)'} ({report})")
sys.exit(1 if fails else 0)
