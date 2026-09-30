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
     round 0 classified two functions and generalised to the rest).
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

for f in fails:
    print("FAIL", f)
print(f"verify_h1: {'OK' if not fails else f'{len(fails)} failure(s)'} ({report})")
sys.exit(1 if fails else 0)
