#!/usr/bin/env python3
"""Hand-checked region cases for simulate_fix_guard.py. Run before trusting its totals."""
import sys
sys.dont_write_bytecode = True
import pathlib
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import simulate_fix_guard as G  # noqa: E402

PRE = "\\documentclass{article}\n"
# (src, needle, expected set of regions containing needle start)
cases = [
 (PRE + "\\usepackage{x--y}\n\\begin{document}\nA -- b\n\\end{document}", "x--y", {"R1"}),
 (PRE + "\\begin{document}\nA -- b\n\\end{document}", "A --", set()),
 (PRE + "\\title{Big -- title}\n\\begin{document}\nx\n\\end{document}", "Big", set()),
 (PRE + "\\author[1]{Ann -- Bob}\n\\begin{document}x\\end{document}", "Ann", set()),
 (PRE + "\\author[a -- b]{Ann}\n\\begin{document}x\\end{document}", "a --", {"R1"}),
 (PRE + "\\email{a--b@x}\n\\begin{document}x\\end{document}", "a--b", {"R1"}),
 (PRE + "%\\begin{document}\n\\foo{q--r}\n\\begin{document}x\\end{document}", "q--r", {"R1"}),
 ("no document here \\foo{q--r}", "q--r", set()),
 (PRE + "\\DeclareMathSymbol{\\Q}{\\mathord}{AMSb}{\"51}\n\\begin{document}x\\end{document}", "AMSb", {"R1", "R2"}),
 ("body \\newcolumntype{L}[1]{>{\\raggedright}p{#1}} z", "raggedright", {"R2"}),
 ("body \\newcommand{\\foo}[1]{\\lstset{a=b}} z", "a=b", {"R2", "R3"}),
 ("body \\def\\foo#1{a -- #1} z", "a --", {"R2"}),
 ("body \\let\\a\\b z", "\\b", {"R2"}),
 ("body \\includegraphics[width=0.5\\textwidth]{f} z", "0.5", {"R3"}),
 ("body \\item[(ii)] z", "ii", set()),
 ("body \\hypersetup{pdftitle={A -- B}} z", "A --", {"R3"}),
 ("body \\typeout{x -- y} z", "x --", {"R3"}),
 ("body $\\left[ a=b \\right]$ z", "a=b", set()),
 ("body \\begin{quantikz} \\gate{H} \\\\ \\end{quantikz} z", "gate", {"R4"}),
 ("body \\begin{tikzpicture}\\begin{axis}[x=1] \\end{axis}\\end{tikzpicture} z", "x=1", {"R3", "R4"}),
 ("body $\\xymatrix@R=1em{A \\ar@{->}[r] & B}$ z", "->", {"R4"}),
 ("body \\xymatrix{A \\ar[r]^{f'} & B} z", "f'", {"R4"}),
 ("body \\tikz[baseline] \\draw (0,0) -- (1,1); after -- x", "(1,1)", {"R4"}),
 ("body \\tikz[baseline] \\draw (0,0) -- (1,1); after -- x", "after", set()),
 ("body \\tikz{\\node{a -- b};} after", "a --", {"R4"}),
 ("% \\begin{quantikz}\n body -- x", "body", set()),
 ("\\\\title{x} y", "x}", set()),
]
ok = 0
for src, needle, exp in cases:
    regs, _ = G.regions_for(src)
    st = {k: [a for a, _ in regs[k]] for k in G.REGIONS}
    p = src.index(needle)
    got = {k for k in G.REGIONS if G.hits(regs[k], st[k], p, p + 1)}
    good = got == exp
    ok += good
    print("OK " if good else "BAD", repr(src)[:70], "|", needle, "->", sorted(got), "" if good else f"expected {sorted(exp)}")
# insertion semantics
src = PRE + "\\begin{document}x\\end{document}"
regs, _ = G.regions_for(src)
st = {k: [a for a, _ in regs[k]] for k in G.REGIONS}
ins_ok = G.hits(regs["R1"], st["R1"], 0, 0) and not G.hits(regs["R1"], st["R1"], src.index("x\\end"), src.index("x\\end"))
print("OK " if ins_ok else "BAD", "insertion semantics"); ok += ins_ok
# reconstruction round trip on a synthetic edit
O = (PRE + "\\usepackage[a=b]{x--y}\n\\begin{document}\nA -- b  c\n\\end{document}\n").encode()
F = (PRE + "\\usepackage[a=b]{x\u2013y}\n\\begin{document}\nA \u2013 b c\n\\end{document}\n").encode()
o, enc, hs, rows, coarse, diag = G.analyse_file(O, F)
guard = G.rebuild(o, hs, lambda i: rows[i]["ws"] or not rows[i]["regions"]).encode(enc)
exp = (PRE + "\\usepackage[a=b]{x--y}\n\\begin{document}\nA \u2013 b c\n\\end{document}\n").encode()
rt = guard == exp
print("OK " if rt else "BAD", "rebuild guard arm", guard if not rt else "")
ok += rt
total = len(cases) + 2
print(ok, "/", total)
sys.exit(0 if ok == total else 1)
