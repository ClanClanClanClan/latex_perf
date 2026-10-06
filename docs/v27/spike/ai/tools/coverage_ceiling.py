#!/usr/bin/env python3
# AI-scoping (OPEN-129) revision: the first version's COVERAGE CEILING on sample 2.
# The first version of the page treatment (AI-scoping.md §3.3) is Stuck on floats, marks beyond
# the kernel's own, \vsplit and inserts other than footnotes. This counts, per paper, which of
# those the paper's own sources use. Same reading as census.py: every .tex of the paper,
# comments stripped per line, class from the first \documentclass. A regex screen: it sees only
# what the paper's .tex files spell; what a class or package does on its own (amsart's running
# heads use \markboth; longtable and many packages patch \output) is NOT counted, so the
# fraction it reports as "uses none" is an UPPER bound on what the first version can admit.
import collections, glob, json, os, re

ROOT = os.environ["LP_REAL_CORPUS"]   # scripts/tools/regrade_sample.py's CORP
REPO = os.environ.get("LP_REPO", os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                              "../../../../.."))
docs = json.load(open(REPO + "/corpora/real_roots/results_sample2.json"))["docs"]

FEATURES = {
    # LaTeX floats: the standard float environments (starred too), the float/algorithm
    # package's, rotating's, wrapfig is NOT a float (it is not listed); \marginpar is a float
    # in LaTeX's implementation (it takes a float box from \@freelist).
    "float": re.compile(r"\\begin\s*\{\s*(figure|table|algorithm|sidewaysfigure|sidewaystable"
                        r"|SCfigure|SCtable|listing)\*?\s*\}|\\marginpar\b|\\newfloat\b"
                        r"|\\DeclareFloatingEnvironment\b"),
    # marks, spelled in the paper's own sources
    "mark": re.compile(r"\\(markboth|markright|mark|marks|markleft|sectionmark|subsectionmark"
                       r"|chaptermark|leftmark|rightmark|firstmark|botmark|topmark"
                       r"|firstmarks|botmarks|topmarks)\b"
                       r"|\\pagestyle\s*\{\s*(headings|myheadings|fancy)\s*\}"
                       r"|\\(usepackage|RequirePackage)\s*(\[[^\]]*\])?\s*\{[^}]*\bfancyhdr\b[^}]*\}"),
    # multicol (its environments split columns with \vsplit) or an explicit \vsplit
    "multicol_vsplit": re.compile(r"\\(usepackage|RequirePackage)\s*(\[[^\]]*\])?\s*\{[^}]*"
                                  r"\bmulticol\b[^}]*\}|\\begin\s*\{\s*multicols\*?\s*\}"
                                  r"|\\vsplit\b"),
}

rows = []
for r in docs:
    p = os.path.join(ROOT, r["arxiv_id"])
    src = ""
    for f in sorted(glob.glob(p + "/**/*.tex", recursive=True)):
        try:
            src += open(f, errors="replace").read() + "\n"
        except OSError:
            pass
    src = "\n".join(l.split("%")[0] if not l.lstrip().startswith("%") else ""
                    for l in src.splitlines())
    c = re.findall(r"\\documentclass\s*(?:\[[^\]]*\])?\s*\{([^}]*)\}", src)
    c = c[0].strip() if c else "?"
    rows.append((r["arxiv_id"], c, {k: bool(rx.search(src)) for k, rx in FEATURES.items()}))

n = len(rows)
art = [x for x in rows if x[1] == "article"]
print(f"papers {n}; class article {len(art)}")
for k in FEATURES:
    print(f"uses {k:16s}: {sum(x[2][k] for x in rows):3d}/{n}   article: "
          f"{sum(x[2][k] for x in art):3d}/{len(art)}")
none = [x for x in rows if not any(x[2].values())]
print(f"uses NONE of them: {len(none)}/{n} = {100*len(none)/n:.1f}%")
none_art = [x for x in none if x[1] == "article"]
print(f"uses none AND class article (AI-4's scope): {len(none_art)}/{n} = "
      f"{100*len(none_art)/n:.1f}%")
print("classes of the papers that use none:",
      collections.Counter(x[1] for x in none).most_common())
print("article papers that use none:", sorted(x[0] for x in none_art))
# Classes whose DEFAULT page style puts marks in the running heads (\pagestyle{headings} or
# their own heads read \leftmark/\rightmark or set \markboth in \maketitle): the screen above
# cannot see these, since the paper spells nothing. Read from the classes' sources [R].
MARK_CLASSES = {"amsart", "amsproc", "amsbook"}
none_cls = [x for x in none if x[1] not in MARK_CLASSES]
print(f"uses none, and the class's default page style sets no marks ({sorted(MARK_CLASSES)} "
      f"excluded): {len(none_cls)}/{n} = {100*len(none_cls)/n:.1f}%")
