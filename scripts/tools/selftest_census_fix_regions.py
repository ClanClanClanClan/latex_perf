#!/usr/bin/env python3
"""Hand-checked region cases for census_fix_regions.py. Run before trusting its totals."""
import pathlib, sys
sys.dont_write_bytecode = True
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from census_fix_regions import Locator  # noqa: E402
cases = [
 (r"\ctrl[wire style={"+'"'+r"\theta_1"+'"'+r"}]{1} x", "theta", "A1", "ctrl"),
 (r"\includegraphics[width=0.5\textwidth]{fig--a}", "0.5", "A1", "includegraphics"),
 (r"\begin{enumerate}[label=(\roman*)] \item x", "roman", "A1", "begin{enumerate}"),
 (r"\item[(ii)] text -- here", "ii", "A2t", "item"),
 (r"\section[Short -- title]{Long}", "Short", "A2t", "section"),
 (r"\cite[p.~5]{key}", "p.", "A2t", "cite"),
 (r"\begin{theorem}[Main -- result] body", "Main", "A2t", "begin{theorem}"),
 (r"\newtheorem{mythm}{Thm}\begin{mythm}[Foo bar] x", "Foo", "A2t", "begin{mythm}"),
 (r"\begin{figure}[htbp] x", "htbp", "A2o", "begin{figure}"),
 (r"\typeout{a -- b}", "a --", "B", "typeout"),
 (r"\PackageWarning{pkg}{some -- msg}", "some", "B", "PackageWarning"),
 (r"\hypersetup{pdftitle={A -- B}, colorlinks}", "A --", "B", "hypersetup"),
 (r"\csname foo bar\endcsname", "foo", "B", "csname"),
 (r"\def\foo#1{a -- #1} rest", "a --", "C", "def"),
 (r"\newcommand{\foo}[1]{\textbf{a -- b}}", "a --", "C", "newcommand"),
 (r"\newcommand\foo{x -- y}", "x --", "C", "newcommand"),
 (r"\newenvironment{e}{\begin{center}}{\end{center} -- z}", "-- z", "C", "newenvironment"),
 (r"\newcommand{\foo}{\item[a b]}", "a b", "A2t", "item"),
 (r"text \textbf{a -- b} end", "a --", "D", "textbf"),
 (r"$\E[X] = 1$ and $\mathbb{R}[x]$", "X]", "D", None),
 (r"$\mathbb{R}[x]$", "x]", "D", None),
 (r"a\\[2pt] b", "2pt", "A2o", "\\"),
 (r"$\sqrt[3]{x}$", "3]", "A2o", "sqrt"),
 (r"x % \item[q] comment" + "\n" + "y", "q]", "COMMENT", "%"),
 (r"\verb|\item[a=b]| z", "a=b", "VERB", "verb"),
 (r"$\left[ a \right]$", " a ", "D", None),
 (r"\item [$a=b$] x", "a=b", "A2t", "item"),
 (r"\footnote[3]{text}", "3]", "A2t", "footnote"),
 (r"\section{A}" + "\n\n" + "[b] x", "b]", "D", None),
 (r"\foo%" + "\n" + "[k=v]{x}", "k=v", "A1", "foo"),
 (r"\begin{tabular}[t]{cc} a & b \end{tabular}", "t]", "A2o", "begin{tabular}"),
]
ok=0
for src, needle, reg, own in cases:
    L=Locator(src); pos=src.index(needle)
    r,o,uc,m = L.attribute(pos)
    good = (r==reg) and (own is None or o==own)
    ok+=good
    print("OK " if good else "BAD", repr(src)[:60], needle, "->", r, o, "underC" if uc else "")
print(ok, "/", len(cases))
