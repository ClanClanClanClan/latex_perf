#!/usr/bin/env python3
"""Unit tests of scripts/tools/gen_contract.py, and completeness checks of the
committed kernel file and contracts. Pure: no docker, no TeX; wired into the
required spec-drift workflow.

Parser tests run on RECORDED logs: every fixture under
corpora/contracts/parser_fixtures/ is an excerpt of a real log the generator
produced under the pinned TeX Live image (see its README). Nothing is
synthesised except the byte strings that test the name encoders, the
web2c-format parser's header layout, and the fake runner that tests the pass
protocol; each is marked SYNTHETIC where it is built.

Each check asserts the KIND of the outcome, in each direction where there is
one (a record is read AND a quantity is not; an error is found AND a printed
meaning that merely contains "! LaTeX Error" is not).

The completeness checks read the committed files: the kernel file must hold
every name the 2026-09-27 adversarial reviews found missing (24 names), its
closure evidence must say complete (TeX's own hash count, uncovered = 0, and
the primitive count equal to TeX's), and every complete contract must carry
the same evidence. `--kernel PATH` checks another kernel file (e.g. the
pre-fix one, which fails on all 24 names).

Exit 0 all checks pass; 1 a check failed.
"""
import argparse
import gzip
import json
import struct
import sys
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import gen_contract as gc  # noqa: E402

REPO = HERE.parent.parent
FIX = REPO / "corpora" / "contracts" / "parser_fixtures"
ap = argparse.ArgumentParser(description=__doc__.split("\n")[1])
ap.add_argument("--kernel", help="kernel file to check (default: every committed one)")
ARGS = ap.parse_args()
fails = 0
count = 0


def check(name, cond, detail=""):
    global fails, count
    count += 1
    if not cond:
        fails += 1
        print("FAIL %s %s" % (name, detail))


def rd(n):
    return (FIX / n).read_bytes()


# --- trace parser -----------------------------------------------------------
tr = gc.parse_trace(rd("trace_excerpt.log"))
names = tr["names"]
check("trace: no unparsed records", tr["unparsed"] == 0, tr["unparsed"])
check("trace: no error in a clean trace", tr["first_error"] is None, tr["first_error"])
check("trace: mid-line record is read (after a file-open parenthesis)",
      ("cs", b"reserved@a") in names)
check("trace: control symbol named = is read as `=`", names.get(("cs", b"=")) == 5,
      names.get(("cs", b"=")))
check("trace: a register assignment is a quantity, not a name",
      ("cs", b"count255") not in names and ("cs", b"toks18") not in names)
check("trace: names printed while \\escapechar=-1 are read",
      ("cs", b"csnameendcsname") in names and ("cs", b"article.cls") in names
      and ("cs", b"protect") in names)
check("trace: a one-byte name under \\escapechar=-1 yields both candidates",
      ("cs", b"~") in names and ("active", b"~") in names)
check("trace: escape restored to 92 is tracked (no `\\`-less name after it)",
      ("cs", b"\\escapechar") not in names and ("cs", b"CurrentFilePathUsed") in names)
tagname = [n for (k, n) in names if k == "cs" and n.startswith(b"tag cannot be used")]
check("trace: a name holding line feeds is re-joined across log lines",
      len(tagname) == 1 and tagname[0].count(b"\n") == 2
      and tagname[0].endswith(b"I'll forget what happened."), tagname)
check("trace: continuation lines are not records (gobble@tag keeps its segment)",
      names.get(("cs", b"gobble@tag")) == 1, names.get(("cs", b"gobble@tag")))
check("trace: our own tracing toggles are the only ones",
      [(t[0], t[1], t[2]) for t in tr["tracing_toggles"]] ==
      [(-1, "into", "tracingassigns"), (7, "changing", "tracingassigns")],
      tr["tracing_toggles"])
check("trace: multiline records counted", tr["multiline"] >= 3, tr["multiline"])

trf = gc.parse_trace(rd("trace_fatal_excerpt.log"))
check("trace: a fatal error is attributed to the segment it happened in",
      trf["first_error"] == (3, "Package cleveref Error: cleveref must be loaded after "
                                "hyperref!."), trf["first_error"])

# --- errors and their classes -------------------------------------------------
lf = rd("load_fatal_excerpt.log")
msg = gc.first_error(lf)
check("error: first `!` line with TeX context is found",
      msg == "Package cleveref Error: cleveref must be loaded after hyperref!.", msg)
check("error: classified by message, not rc",
      gc.classify_error(msg) == "package_error:cleveref", gc.classify_error(msg))
out = gc.classify_outcome(1, lf, False)
check("outcome: fatal with class", out["outcome"] == "fatal" and
      out["error_class"] == "package_error:cleveref", out)
check("outcome: rc 0 and no PDF is fatal E0 (no_pdf)",
      gc.classify_outcome(0, b"", False) == {"outcome": "fatal", "error_class": "no_pdf"})
check("outcome: rc 0 and a PDF is ok", gc.classify_outcome(0, b"", True) == {"outcome": "ok"})
check("outcome: timeout is its own class",
      gc.classify_outcome(gc.TIMEOUT_RC, b"", False)["outcome"] == "timeout")
for m, c in [("Undefined control sequence.", "undefined_cs"),
             ("Missing $ inserted.", "missing_dollar"),
             ("LaTeX Error: \\mathbb allowed only in math mode.", "math_only"),
             ("LaTeX Error: Command \\textFax unavailable in encoding OT1.",
              "unavailable_in_encoding"),
             ("Paragraph ended before \\footref was complete.", "par_in_argument"),
             ("LaTeX Error: Environment foo undefined.", "undefined_env"),
             ("Something nobody has seen.", "other")]:
    check("error class %s" % c, gc.classify_error(m) == c, gc.classify_error(m))

# --- dump parser ----------------------------------------------------------------
dump = rd("dump_excerpt.log")
d = gc.parse_dump(dump)
check("dump: every dump primitive is itself",
      len(d["prims"]) == len(gc.DUMP_PRIMITIVES) and
      all(v == "\\" + k for k, v in d["prims"].items()), d["prims"])
check("dump: catcode table has 256 cells", d["catcodes"] is not None and
      len(d["catcodes"]) == 256)
cc = d["catcodes"] or [None] * 256
check("dump: body-start catcodes of \\ { } % @ are 0 1 2 14 12",
      [cc[92], cc[123], cc[125], cc[37], cc[64]] == [0, 1, 2, 14, 12],
      [cc[92], cc[123], cc[125], cc[37], cc[64]])
check("dump: a plain meaning", d["meanings"].get(0) == b"macro:->\\ ", d["meanings"].get(0))
check("dump: an undefined name is None", 309 in d["meanings"] and d["meanings"][309] is None)
mfe = d["meanings"].get(1062) or b""
check("dump: a meaning with raw line feeds is re-joined with them",
      mfe.startswith(b"macro:#1#2->\\typeout {\n! LaTeX Error: File `#1.#2' not found.\n"),
      mfe[:60])
check("dump: `! LaTeX Error` inside a meaning is not an error", d["error"] is None, d["error"])
check("dump: naive first_error also refuses it (no TeX context)",
      gc.first_error(dump) is None, gc.first_error(dump))
check("dump: active characters", d["actives"].get(120) == b"undefined", d["actives"].get(120))
sc = gc.parse_dump(rd("selfcheck_excerpt.log"))
check("selfcheck: LPS lines parse to booleans",
      len(sc["tests"]) == 20 and all(isinstance(v, bool) for v in sc["tests"].values()),
      sc["tests"])

# --- meaning classification (recorded kernel meanings) -----------------------------
km = json.loads(rd("kernel_meanings_excerpt.json"))["meanings"]


def cls(n):
    return gc.classify_meaning(gc.name_bytes(n), gc.name_bytes(km[n]))


check("meaning: robust wrapper", cls("textbf")["robust"] and
      cls("textbf")["robust_inner"] == "textbf ", cls("textbf"))
check("meaning: \\long macro with #1", cls("textbf ")["long"] and
      cls("textbf ")["arity_hint"] == 1 and not cls("textbf ")["robust"], cls("textbf "))
check("meaning: \\protected\\long macro", cls("NewDocumentCommand")["protected"] and
      cls("NewDocumentCommand")["long"] and cls("NewDocumentCommand")["arity_hint"] == 3)
check("meaning: ltcmd spec", cls("AddToHook").get("ltcmd_spec") == "mo+m", cls("AddToHook"))
check("meaning: expandable ltcmd spec", cls("@gobble@om").get("ltcmd_spec") == "+o+m")
check("meaning: primitive via alias", cls("tex_badness:D") ==
      {"kind": "Primitive", "primitive": "badness"})
check("meaning: control space is a primitive", cls("tex_space:D")["kind"] == "Primitive")
check("meaning: relax", cls("tex_relax:D") == {"kind": "Relax"})
check("meaning: implicit char", cls("bgroup")["kind"] == "Char" and
      cls("bgroup")["form"] == "implicit")
check("meaning: registers", cls("z@") == {"kind": "Register", "register": "dimen",
                                          "index": 12} and
      cls("@tempcnta")["register"] == "count" and cls("toks@")["register"] == "toks")
check("meaning: mathchardef", cls("@M") == {"kind": "MathChar", "code": 0x2710})
check("meaning: font", cls("@circlefnt") == {"kind": "Font", "font": "lcircle10"})
check("meaning: undefined", gc.classify_meaning(b"x", None) == {"kind": "Undefined"})
refs = gc.referenced_names(gc.name_bytes(km["dospecials"]))
check("refs: names printed inside a meaning", b"do" in refs, refs)
check("refs: a primitive meaning names the primitive",
      gc.referenced_names(b"\\badness") == {b"badness"})

# --- .fls -----------------------------------------------------------------------
pwd, ins = gc.parse_fls(rd("load.fls"))
check("fls: PWD", pwd == "/lpwork/r1_load", pwd)
check("fls: INPUT lines", any(p.endswith("/amsmath/amsmath.sty") for p in ins) and
      ins == sorted(set(ins)))
check("fls: texmf-relative paths",
      gc.texmf_rel("/usr/local/texlive/2026/texmf-dist/x.sty", "/usr/local/texlive/2026")
      == "texmf-dist/x.sty")

# --- encoders and the dump writer ------------------------------------------------------
check("carets: hex, ^^M style and ^^?",
      gc.decode_carets(b"a^^0db^^Mc^^?d^^e9") == b"a\rb\rc\x7fd\xe9")
for raw in [b"u8:\xc3\xa9", b"tag\nx", b"\x01\x7f", b"@tempa", b"\xff\xfe"]:
    check("name round-trip %r" % raw, gc.name_bytes(gc.name_str(raw)) == raw,
          gc.name_str(raw))
check("name_str: UTF-8 kept as text", gc.name_str(b"u8:\xc3\xa9") == "u8:é")
line = gc._name_line(b"abc", lambda n: b"<" + n + b">\n")
check("writer: a plain name is written literally", line == b"<abc>\n", line)
nasty = bytes([1, 2, 3, 4, 5, 10, 13]) + b"x"
line = gc._name_line(nasty, lambda n: b"<" + n + b">\n")
check("writer: a name with every reserved byte goes through \\lowercase",
      line is not None and b"lowercase" in line and
      not any(c in gc.UNWRITABLE for c in line[line.index(b"<") + 1:line.index(b">")]),
      line[-40:] if line else line)
block, unw = gc.dump_block([b"a", nasty], actives=False, u8_sweep=False, tests=[b"b"])
check("writer: nothing unwritable", unw == [])
check("writer: dump records carry the sentinel", block.count(gc.END) == 2)

# --- canonical JSON ---------------------------------------------------------------
obj = {"defined_names": {"b": {"kind": "Macro"}, "a": {"kind": "Relax"}}, "z": [1, 2],
       "files_read": [{"path": "p", "sha256": "h"}]}
txt = gc.canonical_json(obj)
check("json: round-trips", json.loads(txt) == obj)
check("json: one line per entry, sorted", '  "a": {"kind":"Relax"},\n  "b": {"kind":"Macro"}'
      in txt, txt)
check("json: deterministic", txt == gc.canonical_json(json.loads(txt)))

# --- review defects of 2026-09-27, on recorded traces ---------------------------
# Defect 2: the null control sequence prints as `\csname\endcsname` (and as
# `csnameendcsname` under \escapechar=-1); both readings must be candidates.
tn = gc.parse_trace(rd("trace_nullcs_excerpt.log"))
check("null cs: the empty name is a candidate", ("cs", b"") in tn["names"], tn["names"])
check("null cs: set in the definer that defined it (segment 1)",
      tn["names"].get(("cs", b"")) == 1, tn["names"].get(("cs", b"")))
check("null cs: both printed forms are one ambiguous record",
      (b"", b"csname\\endcsname") in tn["ambiguous"] and
      (b"", b"csnameendcsname") in tn["ambiguous"], tn["ambiguous"])
# Defect 3: a name holding `=` (a real kernel pattern: l3file's
# \__file_name=<file>) must not be cut at its first `=`.
te = gc.parse_trace(rd("trace_eqname_excerpt.log"))
check("= in a name: lpa=b is a candidate", ("cs", b"lpa=b") in te["names"], te["names"])
check("= in a name: the kernel's __file_name=article.cls is a candidate",
      ("cs", b"__file_name=article.cls") in te["names"])
check("= in a name: the first-`=` reading is kept only as an ambiguous alternative",
      (b"lpa", b"lpa=b") in te["ambiguous"] and b"lpa" not in te["sure"], te["ambiguous"])
check("= in a name: under \\escapechar=-1 too",
      ("cs", b"__file_name=size10.clo") in te["names"])
# Defect 4: set_in follows the value the name keeps, not a local \def that a
# group end undoes.
ts = gc.parse_trace(rd("trace_setin_excerpt.log"))
check("set_in: a restored value keeps the segment that assigned it",
      ts["names"].get(("cs", b"lpset")) == 1, ts["names"].get(("cs", b"lpset")))
check("set_in: a restore to a value from before the trace is marked so",
      gc.parse_trace(b"LPSEG:3\n{changing \\x=undefined}\n{into \\x=macro:->a}\n"
                     b"{restoring \\x=undefined}\n")["names"].get(("cs", b"x"))
      == gc.SEG_BEFORE_TRACE)
check("set_in: a value truncated with ETC. still matches its restore",
      gc._same_value(b"macro:#1.def@nil ->def reserved@a {ETC.",
                     b"macro:#1.def@nil ->def reserved@a {#1}")
      and not gc._same_value(b"macro:->a", b"macro:->b"))
# Re-review LOW item a (SYNTHETIC traces, in TeX's record format): the value a
# group end restores is looked up in the stack of values local assignments
# replaced, not as the last history entry with the same printed value.
t_same = gc.parse_trace(b"LPSEG:1\n{changing \\x=undefined}\n{into \\x=macro:->a}\n"
                        b"LPSEG:3\n{changing \\x=macro:->a}\n{into \\x=macro:->a}\n"
                        b"{restoring \\x=macro:->a}\n")
check("set_in: an in-group re-set of the same value is not the restored one",
      t_same["names"].get(("cs", b"x")) == 1, t_same["names"].get(("cs", b"x")))
t_nest = gc.parse_trace(b"LPSEG:1\n{globally changing \\y=undefined}\n"
                        b"{globally into \\y=macro:->A}\n"
                        b"LPSEG:2\n{changing \\y=macro:->A}\n{into \\y=macro:->B}\n"
                        b"LPSEG:3\n{changing \\y=macro:->B}\n{into \\y=macro:->A}\n"
                        b"{restoring \\y=macro:->B}\n{restoring \\y=macro:->A}\n")
check("set_in: nested groups restore through the save stack",
      t_nest["names"].get(("cs", b"y")) == 1, t_nest["names"].get(("cs", b"y")))
t_ret = gc.parse_trace(b"LPSEG:1\n{changing \\z=undefined}\n{into \\z=macro:->A}\n"
                       b"LPSEG:2\n{changing \\z=macro:->A}\n{into \\z=macro:->B}\n"
                       b"LPSEG:3\n{globally changing \\z=macro:->B}\n"
                       b"{globally into \\z=macro:->C}\n{retaining \\z=macro:->C}\n")
check("set_in: a global value retained at a group end keeps its own segment",
      t_ret["names"].get(("cs", b"z")) == 3, t_ret["names"].get(("cs", b"z")))
# ... and the real hit, RECORDED: hyperref's \WriteBookmarks, set to `0` by
# the package (segment 5), re-set to `0` inside a begin-document group
# (segment 6) and restored at its end. The value it keeps is the package's.
t_wb = gc.parse_trace(rd("trace_resetsame_excerpt.log"))
check("set_in: hyperref's \\WriteBookmarks keeps the package's segment (recorded)",
      t_wb["names"].get(("cs", b"WriteBookmarks")) == 5,
      t_wb["names"].get(("cs", b"WriteBookmarks")))
# Found while regenerating: under \escapechar=-1 the active `~` prints like
# the control symbol `\~`; its assignment and group end must not move the
# control symbol's set_in (hyperref's \~ is set in segment 4, not 6).
tt = gc.parse_trace(rd("trace_tilde_excerpt.log"))
check("ambiguous one-byte record: the control symbol keeps its own segment",
      tt["names"].get(("cs", b"~")) == 4, tt["names"].get(("cs", b"~")))
check("ambiguous one-byte record: the active character is still read",
      ("active", b"~") in tt["names"])
# Defect 1a/1b: mark primitives print with a trailing colon; \nullfont's
# meaning names it.
check("mark primitive: \\topmark: names topmark",
      b"topmark" in gc.referenced_names(b"\\topmark:"))
check("mark primitive: classified as the primitive topmark",
      gc.classify_meaning(b"tex_topmark:D", b"\\topmark:") ==
      {"kind": "Primitive", "primitive": "topmark"})
check("font: select font nullfont names nullfont",
      b"nullfont" in gc.referenced_names(b"select font nullfont"))

# --- re-review defect 1: names from the files a job wrote ------------------------------
import tempfile  # noqa: E402
with tempfile.TemporaryDirectory() as td:
    tdp = Path(td)
    # SYNTHETIC job directory: the .aux line the re-review's lpq7 definer
    # writes, and a log whose tokens must NOT be read (it is not job-written).
    (tdp / "job.aux").write_bytes(b"\\relax \n\\expandafter\\gdef\\csname lpq7\\endcsname{}\n"
                                  b"\\newlabel{LastPage}{{}{1}{}{}{}}\n")
    (tdp / "job.log").write_bytes(b"\\lpfromthelog \\csname lplog\\endcsname\n")
    (tdp / "job.tex").write_bytes(b"\\lpfromthetex\n")
    jw = gc.job_written_names(tdp)
check("job-written names: a \\csname literal of the .aux", b"lpq7" in jw, sorted(jw))
check("job-written names: tokens of the .aux", {b"newlabel", b"gdef"} <= jw, sorted(jw))
check("job-written names: the log and the source are not job-written",
      not {b"lpfromthelog", b"lplog", b"lpfromthetex"} & jw, sorted(jw))

# --- review defect R1.8: the batch classifier uses the solo test ----------------------
dump_log = rd("dump_excerpt.log")
batch_log = b"LPPROBE:0\n" + dump_log + b"\nLPPROBE:1\n! Undefined control sequence.\n" \
    b"l.7 \\foo\n\nLPPROBE:end\n"
pol = gc.batch_polarity(batch_log, [0, 1, 2], 1)
check("batch: `! LaTeX Error` inside a printed meaning is not a fatal", pol[0] == "ok", pol)
check("batch: a `!` line with TeX context is a fatal", pol[1] == "fatal", pol)
check("batch: a probe without a marker is unreached", pol[2] == "unreached", pol)

# --- review defect R1.2: the oracle's pass protocol (SYNTHETIC runner) ----------------
sys.path.insert(0, str(HERE))
import diff_real_roots as drr  # noqa: E402
check("fixpoint: MAX_PASSES equals the grader's", gc.MAX_PASSES == drr.MAX_PASSES,
      (gc.MAX_PASSES, drr.MAX_PASSES))


class FakeTex(gc.Tex):
    def __init__(self, rcs):  # SYNTHETIC: a scripted sequence of pass rcs
        self.rcs, self.calls = list(rcs), 0

    def pdflatex(self, jobdir, tex, **kw):
        rc = self.rcs[self.calls]
        self.calls += 1
        return {"rc": rc, "log": b"", "fls": b"%d" % self.calls, "pdf": rc == 0,
                "secs": 0.0, "tex_sha256": ""}


for rcs, want in [([0, 0], (0, 2)), ([1, 0, 0], (0, 3)), ([0, 1], (1, 2)),
                  ([1, 1, 1], (1, 3)), ([1, 1, 0, 1], (1, 4)),
                  ([gc.TIMEOUT_RC], (gc.TIMEOUT_RC, 1))]:
    ft = FakeTex(rcs)
    r = ft.fixpoint(Path("."), b"")
    check("fixpoint %s -> rc,passes %s" % (rcs, want), (r["rc"], r["passes"]) == want and
          ft.calls == want[1] and r["first_fls"] == b"1", (r["rc"], r["passes"]))

# --- re-review 2 defect 1: every pass the protocol can grade (SYNTHETIC runner) --------
# The pass histories are derived from the fixpoint implementation itself: every
# rc sequence is run through Tex.fixpoint, and the history (S = rc 0, F = not)
# before each pass it runs must be one of protocol_histories(), and each of
# those must occur.
seen_hist = set()
for n in range(1, gc.MAX_PASSES + 2):
    for bits in range(2 ** n):
        rcs = [(bits >> i) & 1 for i in range(n)]
        ft = FakeTex(rcs + [0] * (gc.MAX_PASSES + 2))
        r = ft.fixpoint(Path("."), b"")
        ran = "".join("S" if rc == 0 else "F" for rc in ft.rcs[:ft.calls])
        seen_hist |= {ran[:i] for i in range(len(ran))}
check("pass histories: exactly the histories the fixpoint can run a pass after",
      set(gc.protocol_histories()) == seen_hist, (gc.protocol_histories(), sorted(seen_hist)))
check("pass histories: '', F, S, FF, FS, FFS, i.e. passes 1 to MAX_PASSES+1",
      gc.protocol_histories() == ["", "F", "S", "FF", "FS", "FFS"] and
      max(len(h) for h in gc.protocol_histories()) + 1 == gc.MAX_PASSES + 1,
      gc.protocol_histories())
fv = gc.failing_variant(b"pre\\begin{document}\nX\n\\end{document}\n")
check("pass histories: the failing variant fails after the body, before \\end{document}",
      fv == b"pre\\begin{document}\nX\n" + gc.FAIL_LINE + b"\\end{document}\n", fv)


class TreeTex(gc.Tex):
    """SYNTHETIC: each run reads the history job.aux holds and appends its own
    letter (F when the document is the failing variant)."""
    def __init__(self, host):
        self.host, self._jobs = host, 0
        import threading
        self._lock = threading.Lock()

    def pdflatex(self, jobdir, tex, **kw):
        aux = jobdir / "job.aux"
        hist = aux.read_bytes() if aux.exists() else b""
        aux.write_bytes(hist + (b"F" if gc.FAIL_LINE in tex else b"S"))
        (jobdir / "job.log").write_bytes(hist)
        return {"rc": 1 if gc.FAIL_LINE in tex else 0, "log": hist, "fls": b"",
                "pdf": False, "secs": 0.0, "tex_sha256": ""}


with tempfile.TemporaryDirectory() as td:
    tree = gc.run_history_tree(TreeTex(Path(td)), "t", b"\\begin{document}\n\\end{document}\n",
                               gc.protocol_histories())
    got = {h: node["S"]["log"].decode() for h, node in tree.items()}
    check("pass-history tree: each pass runs on the files its history wrote",
          got == {h: h for h in gc.protocol_histories()} and
          all(node["pass"] == len(h) + 1 for h, node in tree.items()), got)

# --- review defect R1.3: the grading environment is the graders' ----------------------
# There is ONE definition of the oracle's TeX environment, _oracle.ORACLE_TEX_VARS
# (with the private TEXMFHOME/TEXMFVAR of oracle_tex_vars). The graders get it
# through _oracle's tex_env/oracle_tex_env and the generator through
# oracle_tex_vars; each check below reads that single source, never a copy.
# (The previous form compared gen_contract.TEX_ENV with the graders' SOURCE
# TEXT, and failed three checks the day #617 moved the graders' copy into
# _oracle.py although no environment had changed.)
import re  # noqa: E402
import _oracle  # noqa: E402
W = "/lp-work-root/run"
base = _oracle.oracle_tex_vars(W)
check("env: the oracle's one TeX environment is the recorded protocol "
      "(openin_any=p, openout_any=p, SOURCE_DATE_EPOCH=0, no forced date)",
      _oracle.ORACLE_TEX_VARS == {"openin_any": "p", "openout_any": "p",
                                  "SOURCE_DATE_EPOCH": "0"}, _oracle.ORACLE_TEX_VARS)
check("env: a private TEXMFHOME/TEXMFVAR below the work directory",
      {k: base.get(k) for k in ("TEXMFHOME", "TEXMFVAR")} ==
      {"TEXMFHOME": W + "/th", "TEXMFVAR": W + "/tv"}, base)
grader_env = _oracle._Base.tex_env(None, W)
check("env: the graders' tex_env carries the one environment",
      all(grader_env.get(k) == v for k, v in base.items()), base)
want_over = {"grading": dict(gc.LOG_WIDTH),
             "forced": dict(gc.LOG_WIDTH, **gc.FORCE_DATE),
             "second_date": dict(gc.LOG_WIDTH, **gc.FORCE_DATE,
                                 SOURCE_DATE_EPOCH=gc.SECOND_EPOCH)}
for env in gc.ENVS:
    v = gc.tex_vars(env, W)
    over = {k: x for k, x in v.items() if base.get(k) != x}
    check("env %s: exactly the oracle's environment plus its documented overrides"
          % env, set(base) <= set(v) and over == want_over[env], over)
check("env: the grading environment does not force the date",
      "FORCE_SOURCE_DATE" not in gc.tex_vars("grading", W) and "FORCE_SOURCE_DATE" not in base)
check("env: the log-width overrides change no graded variable",
      not set(gc.LOG_WIDTH) & set(base) and not set(gc.LOG_WIDTH) & {"FORCE_SOURCE_DATE"})
check("env: every generator variable is one the oracle forwards",
      all(_oracle._ENV_FORWARD.match(k) for e in gc.ENVS for k in gc.tex_vars(e, W)))
# No tool restates the environment: an assignment of one of these variables to
# a literal anywhere under scripts/ but _oracle.py is a second definition that
# can drift. (Explicit overrides by NAME, like gen_contract's
# SOURCE_DATE_EPOCH=SECOND_EPOCH, are not literals.)
_PY_RESTATE = re.compile(r"""\b(openin_any|openout_any|SOURCE_DATE_EPOCH)\s*=\s*[rbuRBU]?["']"""
                         r"""|["'](openin_any|openout_any|SOURCE_DATE_EPOCH)["']\s*:""")
_SH_RESTATE = re.compile(r"^[^#]*\b(openin_any|openout_any|SOURCE_DATE_EPOCH)=")
# Skipped: the definition itself; this gate and the selftest harness (their
# kill-test payloads are restatements, written out); check_oracle_infra_grading
# (it sets a HOSTILE host value, openin_any=a, to prove it does NOT cross).
_SKIP = {"_oracle.py", "check_gen_contract_parsers.py", "check_gate_selftests.py",
         "check_oracle_infra_grading.py"}
restated = []
for f in sorted((REPO / "scripts").rglob("*")):
    if not f.is_file() or f.name in _SKIP or f.suffix not in (".py", ".sh", ".bash"):
        continue
    rx = _PY_RESTATE if f.suffix == ".py" else _SH_RESTATE
    for n, line in enumerate(f.read_text(encoding="utf-8", errors="replace").split("\n"), 1):
        if rx.search(line):
            restated.append("%s:%d" % (f.relative_to(REPO), n))
check("env: no tool restates the oracle's TeX environment (one definition, _oracle.py)",
      not restated, restated[:10])

# --- the engine's own name lists ----------------------------------------------------------
check("cs_count: the statistics line", gc.cs_count(
    b" 29447 multiletter control sequences out of 15000+600000\n") == 29447)
check("cs_count: the \\dump line", gc.cs_count(b"551 multiletter control sequences\n") == 551)
check("cs_count: absent", gc.cs_count(b"no stats") is None)
# SYNTHETIC web2c format: magic, engine name, 5 constants, pool_ptr, str_ptr,
# str_start, pool; strings 0..255 are TeX's printable forms.
reps = []
for k in range(256):
    reps.append(bytes([k]) if 32 <= k < 127 else
                (b"^^" + bytes([k + 64 if k < 64 else k - 64]) if k < 128 else
                 b"^^%02x" % k))
strs = reps + [b"topmark", b"lpa=b", b""]
pool = b"".join(strs)
starts = [0]
for x in strs:
    starts.append(starts[-1] + len(x))
fmt = (b"W2TX" + struct.pack(">i", 8) + b"pdftex\0\0" + struct.pack(">5i", 1, 2, 3, 4, 5)
       + struct.pack(">ii", len(pool), len(strs)) + struct.pack(">%di" % len(starts), *starts)
       + pool + b"trailer")
got = gc.fmt_pool_strings(gzip.compress(fmt))
check("fmt pool: every string, in order, through gzip", got == strs, got[-3:])
try:
    gc.fmt_pool_strings(b"W2TX" + b"\0" * 64)
    check("fmt pool: no pool is an error, not an empty list", False)
except ValueError:
    check("fmt pool: no pool is an error, not an empty list", True)
sn = gc.source_names(b"\\def\\foo@bar_baz:N{\\relax}\\c@x \\a")
sg = gc.source_names(b"\\def\\Gin@rule@*#1{x} \\!!stringa ")
check("source names: a run cut at each non-letter (found by TeX's hash count)",
      {b"Gin", b"Gin@rule", b"Gin@rule@", b"Gin@rule@*", b"!!stringa"} <= sg, sg)
check("source names: every letter-set reading", {b"def", b"foo", b"foo@bar",
      b"foo@bar_baz:N", b"relax", b"c", b"c@x"} - {b"c"} <= sn and b"a" not in sn, sn)

# --- completeness of the committed kernel file and contracts ---------------------------
# The names the 2026-09-27 reviews MEASURED as defined in format state and
# missing from the kernel (review 0 item 1; review 1 item 1).
REVIEW_MISSING = json.loads(rd("review_missing_names.json"))["names"]
check("completeness: the reviewers' list has 24 distinct names",
      len(set(REVIEW_MISSING)) == 24)
CDIR = REPO / gc.CONTRACT_DIR
kfiles = [Path(ARGS.kernel)] if ARGS.kernel else sorted((CDIR / "kernel").glob("*.json"))
check("completeness: there is a kernel file to check", bool(kfiles))
for kf in kfiles:
    k = json.loads(kf.read_text(encoding="utf-8"))
    for n in REVIEW_MISSING:
        check("kernel %s holds %s" % (kf.name, n), n in k.get("names", {}))
    cov = k.get("coverage") or {}
    check("kernel %s: TeX's hash count finds no name outside the candidates" % kf.name,
          cov.get("uncovered") == 0 and cov.get("covered") == cov.get("hash_entries")
          and isinstance(cov.get("hash_entries"), int), cov)
    pr = k.get("primitives") or {}
    check("kernel %s: primitive count equals TeX's own count" % kf.name,
          pr.get("complete") is True and pr.get("multiletter") == pr.get("tex_cs_count")
          and isinstance(pr.get("tex_cs_count"), int), {x: pr.get(x) for x in
                                                         ("multiletter", "tex_cs_count")})
    missing_prims = [x for x in pr.get("names", []) if x not in k.get("names", {})
                     and x not in pr.get("undefined_in_format", [])]
    check("kernel %s: every engine primitive is a kernel name or listed as undefined"
          % kf.name, not missing_prims, missing_prims[:5])
    check("kernel %s: complete, and says so" % kf.name, k.get("complete") is True and
          k.get("incomplete_reasons") == [], k.get("incomplete_reasons"))
    # MEASURED: 0 format-state meanings change with the job name (the l3
    # names that hold it, \c_sys_jobname_str and \g_file_curr_name_str, are
    # \let to the \jobname primitive, so their MEANING is job-independent).
    check("kernel %s: job-name-dependent meanings are listed, under job name `job`"
          % kf.name, k.get("jobname") == "job" and
          isinstance(k.get("jobname_dependent_names"), list) and
          k.get("names", {}).get("c_sys_jobname_str") == "Primitive",
          (k.get("jobname"), k.get("jobname_dependent_names")))
    check("kernel %s: \\everyjob names are recorded" % kf.name,
          "sys_if_shell:TF" in k.get("everyjob_names", []))
    check("kernel %s: count matches its names" % kf.name,
          k.get("count") == len(k.get("names", {})))
if not ARGS.kernel:
    for cf in sorted(CDIR.glob("*.json")):
        c = json.loads(cf.read_text(encoding="utf-8"))
        if c.get("schema") != gc.SCHEMA:
            continue
        check("contract %s: generator version is current" % cf.name,
              c["generator"]["version"] == gc.GENERATOR_VERSION)
        check("contract %s: states what `complete` attests" % cf.name,
              c.get("complete_scope") == gc.COMPLETE_SCOPE)
        check("contract %s: complete iff no reasons" % cf.name,
              c["complete"] == (not c["incomplete_reasons"]))
        kref = REPO / c["kernel"]["file"]
        check("contract %s: its kernel file exists" % cf.name, kref.is_file())
        if not c["complete"]:
            # The only incomplete contract committed on purpose is a
            # configuration that does not load (the fatal-load example).
            check("contract %s: incomplete only because it does not load" % cf.name,
                  c["load_outcome"]["status"] == "fatal" and
                  c["incomplete_reasons"][0].startswith("load_fatal"),
                  c["incomplete_reasons"][:2])
            continue
        cov = c.get("coverage") or {}
        check("contract %s: TeX's hash count at body start finds nothing undumped"
              % cf.name, cov.get("uncovered") == 0 and cov.get("unwritable") == 0, cov)
        # Re-review 2: TeX's count on EVERY pass the protocol can grade, in
        # the forced, grading and second-job-name environments.
        cps = c.get("coverage_passes") or []
        want = {(e, j, gc.hist_label(h)) for e, j in
                [("forced", "job"), ("grading", "job"), ("grading", gc.SECOND_JOBNAME)]
                for h in gc.protocol_histories()}
        have = {(x.get("env"), x.get("jobname"), x.get("history")) for x in cps}
        check("contract %s: TeX's hash count on every pass of every pass history, in "
              "all three environments" % cf.name, have == want and len(cps) == len(want),
              sorted(want - have))
        bad_cp = [x for x in cps if x.get("uncovered") != 0 or "error" in x or
                  (x.get("env") == "forced" and x.get("jobname") == "job" and
                   (x.get("unwritable") != 0 or not isinstance(x.get("hash_entries"), int)))]
        check("contract %s: ... and it finds nothing undumped on any of them" % cf.name,
              not bad_cp, bad_cp[:2])
        check("contract %s: ... up to pass MAX_PASSES+1" % cf.name,
              max((x.get("pass", 0) for x in cps), default=0) == gc.MAX_PASSES + 1)
        check("contract %s: states its job name" % cf.name, c.get("jobname") == "job")
        sc = c["self_check"]
        check("contract %s: the self-check samples the universe, both directions"
              % cf.name, sc.get("sample_from") == "universe" and
              0 < sc["sampled_members"] < sc["sampled"], sc.get("sampled"))
        check("contract %s: no bogus null-cs or split names in reverted_names" % cf.name,
              not {"csnameendcsname", "csname\\endcsname", "__file_name"}
              & set(c["reverted_names"]))
        check("contract %s: load outcome attested with the pass protocol" % cf.name,
              c["load_outcome"].get("passes", 0) >= 2)

# --- M1 slice 2: signature probes (contract_signatures.py) ---------------------------
import copy  # noqa: E402
import re  # noqa: E402
import time  # noqa: E402
import contract_signatures as sg  # noqa: E402
# The sentinel's error, as TeX prints it (recorded in the probe runs of
# 2026-09-27; the message text is TeX's, the classes are ours).
check("sig: the sentinel taken as an argument is a grab",
      gc.classify_error("Forbidden control sequence found while scanning use of \\@xdblarg.")
      == "forbidden_cs_use" and sg.outcome_of({"outcome": "fatal", "error_class":
      "forbidden_cs_use", "message": "x"})["o"] == "grab")
check("sig: any other scan meeting it is not a grab",
      gc.classify_error("Forbidden control sequence found while scanning definition of \\x.")
      == "forbidden_cs" and sg.outcome_of({"outcome": "fatal", "error_class":
      "forbidden_cs", "message": "x"})["o"] == "fatal")
# The follow probe's two errors (TeX prints `! <text>.` for \errmessage{<text>}).
check("sig: the follow probe's own error reads as follow, a state change as fatal",
      sg.outcome_of({"outcome": "fatal", "error_class": "other", "message": "LPFOLLOW."})
      == {"o": "follow"} and
      sg.outcome_of({"outcome": "fatal", "error_class": "other", "message": "LPSTATE."})["e"]
      == "lp_state_changed" and
      sg.outcome_of({"outcome": "fatal", "error_class": "undefined_cs",
                     "message": "Undefined control sequence."})["o"] == "fatal")
check("sig: a missing counter is its own class (the payload search keys on classes only)",
      sg.refine_class("latex_error", "LaTeX Error: No counter 'a' defined.") == "no_counter"
      and sg.refine_class("latex_error", "LaTeX Error: x") == "latex_error")
check("sig: a letter after the sentinel is separated (\\lpstopa is another name)",
      sg.build_use("\\begin{x}", [], stop=True, tail="a\\end{x}") ==
      "\\begin{x}\\lpstop a\\end{x}" and
      sg.build_use("\\begin{x}", [], stop=True, tail="\\item a") == "\\begin{x}\\lpstop\\item a")
check("sig: argument syntax per kind",
      sg.build_use("\\c", [("opt", "a"), ("req", "b"), ("gopt", "c")], star=True) ==
      "\\c*[a]{b}{c}")
pre = b"\\documentclass{article}\n"
d1 = sg.cell_doc(pre, "text", "\\c{a}\\lpstop")
d2 = sg.cell_doc(pre, "math", "\\c{a}")
d3 = sg.cell_doc(pre, "text", "\\c{a}\\lpstopx")
d4 = sg.cell_doc(pre, "preamble", "\\c\\lpstop")
check("sig: the sentinel is defined iff the use names it",
      d1.count(b"\\outer\\def\\lpstop{}") == 1 and b"\\outer" not in d2 and
      b"\\outer" not in d3 and d4.index(b"\\outer") < d4.index(b"\\begin{document}"))
check("sig: cells place the use", b"x \\c{a}\\lpstop y" in d1 and b"x $\\c{a}$" in d2 and
      d4.endswith(b"\\begin{document}\nx\n\\end{document}\n"))
d5 = sg.cell_doc(pre, "list", sg.follow_use("\\c"))
check("sig: the follow probe: state saved before the use, \\lpfollow and \\lpnocs after it, "
      "its macros defined iff it is used",
      sg.follow_use("\\c{a}") == "\\lpfsave \\c{a}\\lpfollow\\lpnocs" and
      d5.count(sg.FOLLOW_DEF.encode()) == 1 and b"\\item x \\lpfsave \\c\\lpfollow\\lpnocs y" in d5
      and sg.FOLLOW_DEF.encode() not in d1 and b"\\outer\\def\\lpfollow" in d5)
d6 = sg.cell_doc(pre, sg.CONS + "vertical", "\\c{a}")
d7 = sg.cell_doc(pre, sg.CONS + "preamble", "\\c{a}")
check("sig: the consumer cell: a \\title first, toc/lof/lot and headings before the use, "
      "\\maketitle, a new page and both marks after it",
      d6.startswith(pre + b"\\title{t}\n\\begin{document}\n\\pagestyle{headings}"
                    b"\\tableofcontents\\listoffigures\\listoftables\n\\c{a}\\par x\n"
                    b"\\maketitle\\newpage x\\leftmark\\rightmark\n\\end{document}")
      and d7.startswith(pre + b"\\title{t}\n\\c{a}\n\\begin{document}\n\\pagestyle{headings}"))
LET = set(range(65, 91)) | set(range(97, 123))
# Version 3 (review round 2): the follow probe's new arms, read from SYNTHETIC
# log text in TeX's printed form (\tracingassigns/\tracingrestores records).
_MEM = {"thesection": "Macro", "baselineskip": "Primitive", "everypar": "Register:toks",
        "title": "Macro+robust", "reserved@a": "Macro"}
_LOG = "\n".join([
    "LPFX<", "{into \\tracingassigns=1}",
    "{changing \\reserved@a=macro:->x}", "{into \\reserved@a=macro:->y}",
    "{changing \\baselineskip=12.0pt}", "{into \\baselineskip=10.0pt}",
    "{globally changing \\thesection=macro:->\\@arabic \\c@section }",
    "{into \\thesection=macro:->\\@Alph \\c@section }",
    "{changing \\lpnew=undefined}", "{into \\lpnew=\\skip51}",
    "{changing \\title=macro:->a}", "{into \\title=macro:->b}",
    "{restoring \\title=macro:->a}",
    "{changing \\tracingassigns=1}", "LPFX>"])
check("sig v3: redefinitions are the NET meaning changes of body-typeable names, not of "
      "internal quantities, @-names, the probe's own switches, or a group-local change",
      sg.redefined_names(_LOG, _MEM, LET) == ["lpnew", "thesection"],
      sg.redefined_names(_LOG, _MEM, LET))
_R1 = "{changing \\\\=macro:->" + "v" * (79 - len("{changing \\\\=macro:->}")) + "}"
check("sig v3: a whole record of exactly 79 characters followed by another is two records "
      "(measured on \\centering)", len(_R1) == 79 and
      sg.redefined_names("LPFX<\n" + _R1 + "\n{into \\\\=macro:->w}\nLPFX>", {}, LET) == ["\\"])
check("sig v3: a marker after a 79-character line is still found; a trace without markers "
      "fails closed", sg.redefined_names("x" * 79 + "\nLPFX<\n{changing \\lpq=undefined}\n"
                                         "{into \\lpq=\\relax}\nLPFX>\n", {}, LET) == ["lpq"]
      and sg.redefined_names("no markers", {}, LET) == [sg.UNREADABLE])
check("sig v3: a truncated value counts as changed after an assignment, not after a group "
      "end restored it (\\\\ inside center)",
      sg.redefined_names("LPFX<\n{changing \\\\=macro:->x\\ETC.}\n{into \\\\=macro:->y}\n"
                         "{restoring \\\\=macro:->x\\ETC.}\nLPFX>", {}, LET) == [] and
      sg.redefined_names("LPFX<\n{changing \\lpy=macro:->x\\ETC.}\n"
                         "{into \\lpy=macro:->x\\ETC.}\nLPFX>", {}, LET) == ["lpy"])
_W = "{changing \\lpnew=macro:->" + "u" * 70 + "}"
check("sig v3: a wrapped log line (79 characters) is rejoined before reading",
      sg.redefined_names("LPFX<\n" + _W[:79] + "\n" + _W[79:] + "\n" +
                         _W.replace("changing", "into") + "\nLPFX>", {}, LET) == [] and
      sg._unwrap_log("a" * 79 + "\nb\nc") == ["a" * 79 + "b", "c"])
check("sig v3: the mode a follow probe reports, and the pseudo-cells",
      sg.mode_after({"o": "fatal", "e": "lp_mode_changed", "m": "LPMODE v."}) == "v" and
      sg.mode_after({"o": "follow"}) is None and
      sg.refine_class("other", "LPMODE hi.") == "lp_mode_changed" and
      sg.refine_class("other", "LPREDEFINES x.") == "lp_redefines" and
      sg.split_cell("ctr-1:text") == ("ctr-1:", "text") and
      sg.split_cell(sg.VMID + "vertical") == (sg.VMID, "vertical") and
      sg.split_cell("listv") == ("", "listv"))
d8 = sg.cell_doc(pre, "ctr27:text", "\\c", ["enumi", "page"])
d9 = sg.cell_doc(pre, sg.VMID + "vertical", "\\c")
d10 = sg.cell_doc(pre, "listv", "\\c{\\lpfragile}")
check("sig v3: the counter, mid-page and list-vertical documents, and the moving witness "
      "defined iff used",
      b"\\setcounter{enumi}{27}\\setcounter{page}{27}x \\c y" in d8 and
      b"x\\par \\c\\par x" in d9 and
      b"\\item x\\par " + sg.FRAGILE_DEF.encode() + b"" not in d10 and
      sg.FRAGILE_DEF.encode() in d10 and b"\\item x\\par \\c{\\lpfragile}\\par y" in d10
      and sg.FRAGILE_DEF.encode() not in d8)
check("sig v3: an optional argument after a space", sg.build_use("\\\\", [("sopt", "a")]) ==
      "\\\\ [a]")
check("sig: names a body can type (letters run, or one non-letter byte)",
      sg.user_facing("textbf", LET) and sg.user_facing("\\", LET) and sg.user_facing("i", LET)
      and not sg.user_facing("@gobble", LET) and not sg.user_facing("c@page", LET)
      and not sg.user_facing("cs_new:Npn", LET) and not sg.user_facing("", LET))
# Witnesses (review C-82): the text witness must not toggle math.
check("sig: the text witness does not toggle math, the none witness is fatal typeset",
      "$" not in sg.TEXT_CONTENT and "&" in sg.NONE_CONTENT and "^" in sg.MATH_CONTENT)
W_OK, W_TX, W_MA, W_CS, W_TAB = "ok", "missing_dollar", "math_accent", "missing_endcsname", \
    "misplaced_tab"
check("sig: content kinds by the error class of each witness (typesetting evidence only)",
      [sg.content_kind("text", m, t, n) for m, t, n in (
          (W_TX, W_OK, W_TAB), (W_OK, W_MA, W_TAB), (W_OK, W_MA, W_OK), (W_OK, W_CS, W_OK),
          (W_OK, W_OK, W_OK), (W_OK, W_OK, W_TAB), (W_TX, W_MA, W_TAB), (W_CS, W_CS, W_CS))] ==
      ["text", "math", "math", "none", "none", "opaque", "restricted", "restricted"])
check("sig: \\\"a typeset in math is its own class",
      sg.refine_class("other", "Please use \\mathaccent for accents in math mode.") ==
      "math_accent")
check("sig: argty table (TyLabel only when no cell typesets the payload)",
      [sg.argty_of(k) for k in (
          {"text": "text", "math": "text"}, {"text": "text", "math": "math"},
          {"math": "math"}, {"text": "none", "math": "none"}, {"text": "math", "math": "math"},
          {"text": "text", "list": "math"}, {"text": "restricted"}, {},
          {"text": "none", "math": "math"}, {"text": "opaque", "math": "opaque"})] ==
      ["TyText", "TyInherit", "TyMath", "TyLabel", "TyMath", None, None, None, None, None])
check("sig: an environment body has a mode only when a witness shows typesetting",
      [sg.body_mode_of(m, t) for m, t in ((W_OK, W_OK), (W_OK, W_MA), (W_TX, W_OK),
                                          (W_TX, W_MA))] == [None, "math", "text", None])
# SYNTHETIC meanings in TeX's printed form: hints only, never attestation.
mh = {"x": b"macro:->\\protect \\x  ", "x ": b"\\long macro:#1->\\textbf {#1}",
      "y": b"macro:->\\@ifstar \\ys \\yn ", "z": b"macro:->\\@protected@testopt \\z \\\\z {}"}
check("sig: meaning hints (robust inner, star, optional)",
      sg.meaning_hint("x", mh)["arity"] == 1 and sg.meaning_hint("x", mh)["via"] == "x "
      and sg.meaning_hint("y", mh)["star"] and sg.meaning_hint("z", mh)["opt"]
      and sg.meaning_hint("q", {})["source"] == "undefined")


# SYNTHETIC: the discovery logic on a fake TeX (no engine). A model macro \lpx
# takes its first `r` tokens (a brace group is one token) as arguments; the
# sentinel among them is a grab; a payload other than `a` is judged by
# `pay(cell, payload, consumers)`; the follow probe passes unless `follow`
# says otherwise for the cell. Each case is a shape one of the 2026-09-27
# review's findings is about.
class FakeSession(sg.Session):
    def __init__(self, model):
        super().__init__(None)
        self.model = model

    def p(self, cell, use):
        key = (cell, use)
        if key not in self.memo:
            self.memo[key] = self.model(cell, use)
            self.log.append(key)
        return self.memo[key]


def fake_macro(r, cells_ok=sg.CELLS, follow=None, pay=None, special=None):
    """`follow(cell)`: True (follows), False (the next token is consumed), or
    a string: `mode:<m>` (the use leaves mode m), `redef`, `state`.
    `special(cell, use)`: an outcome for a pseudo-cell probe, a repetition or
    a transition probe (None = the ordinary model)."""
    def model(cell, use):
        prefix, base = sg.split_cell(cell)
        cons = prefix == sg.CONS
        if special is not None:
            o = special(cell, use)
            if o is not None:
                return o
        pre = "\\lpfsave "
        if use.startswith(pre):
            o = model(cell, use[len(pre):-len("\\lpfollow\\lpnocs")])
            if o["o"] != "ok":
                return o
            ok = follow(base) if follow else True
            if ok is True:
                return {"o": "follow"}
            if isinstance(ok, str) and ok.startswith("mode:"):
                return {"o": "fatal", "e": "lp_mode_changed", "m": "LPMODE %s." % ok[5:]}
            if ok == "redef":
                return {"o": "fatal", "e": "lp_redefines", "m": "LPREDEFINES lpy."}
            if ok == "state":
                return {"o": "fatal", "e": "lp_state_changed", "m": "LPSTATE."}
            return {"o": "fatal", "e": "undefined_cs", "m": "Undefined control sequence."}
        rest = use[len("\\lpx"):]
        toks, i = [], 0
        while i < len(rest):
            if rest.startswith("\\lpstop", i):
                toks.append("STOP")
                i += len("\\lpstop")
            elif rest[i] == "{":
                j = rest.index("}", i)
                toks.append(("G", rest[i + 1:j]))
                i = j + 1
            else:
                toks.append(("C", rest[i]))
                i += 1
        taken = toks[:r]
        if "STOP" in taken or ("G", "\\lpstop") in taken:
            return {"o": "grab", "e": "forbidden_cs_use", "m": "Forbidden control sequence."}
        if len(taken) < r:
            return {"o": "fatal", "e": "missing_open", "m": "Missing { inserted."}
        if base not in cells_ok:
            return {"o": "fatal", "e": "wrong_mode", "m": "You can't use that here."}
        for t in taken:
            if t[0] == "G":
                res = pay(base, t[1], cons) if pay else "ok"
                if res != "ok":
                    return {"o": "fatal", "e": res, "m": "M " + res}
        return {"o": "ok"}
    return model


def fake_sig(model, lat=()):
    S = FakeSession(model)
    rec = sg._record(sg.signature_for(S, "\\lpx", "", list(lat)), S, None)
    return rec


def label_pay(cons_none="ok", stored="undefined_cs"):
    def pay(cell, p, cons):
        if p == sg.TEXT_CONTENT:
            return "missing_endcsname"
        if p == sg.NONE_CONTENT and cons:
            return cons_none
        if p == sg.STORED_CONTENT:
            return stored
        return "ok"
    return pay


r_string = fake_sig(fake_macro(0, follow=lambda c: False))
check("sig: an r=0 use whose next token is consumed (\\string, \\index) is unresolved "
      "(review HIGH-1)", r_string["status"] == "unresolved" and
      {a["reason"] for a in r_string["attempts"].values()} == {sg.EXACT_REASONS["follow"]},
      r_string.get("attempts"))
r_relax = fake_sig(fake_macro(0))
check("sig: an r=0 use whose next token follows is attested",
      r_relax["status"] == "attested" and r_relax["variants"][0]["r"] == 0)
r_part = fake_sig(fake_macro(0, follow=lambda c: c != "list"))
v_part = r_part["variants"][0]
check("sig: an accepting cell whose follow probe fails is not shape-checked, and gives no "
      "content", r_part["status"] == "attested" and
      v_part["cells"]["list"]["shape_checked"] is False and
      v_part["cells"]["list"]["follow"] == "undefined_cs" and
      v_part["cells"]["text"]["shape_checked"] is True)
r_label = fake_sig(fake_macro(1, pay=label_pay()))
check("sig: a key slot (not typeset, processed at the use, no consumer typesets it) is TyLabel",
      r_label["status"] == "attested" and r_label["variants"][0]["args"][0]["argty"] == "TyLabel",
      r_label["variants"][0]["args"][0] if r_label["status"] == "attested" else r_label)
r_title = fake_sig(fake_macro(1, pay=label_pay(cons_none="misplaced_tab")))
a_title = r_title["variants"][0]["args"][0]
check("sig: a slot a consumer typesets later (\\title, \\section[..]) is not TyLabel "
      "(review HIGH-2)", a_title["argty"] is None and
      (a_title.get("refuted") or {}).get("argty") == "TyLabel"
      and (a_title.get("refuted") or {}).get("by", [""])[0].startswith(sg.CONS), a_title)
r_blank = fake_sig(fake_macro(1, pay=label_pay(stored="ok")))
a_blank = r_blank["variants"][0]["args"][0]
check("sig: a slot whose payload is stored or discarded (a branch not taken) is not TyLabel",
      a_blank["argty"] is None and
      (a_blank.get("refuted") or {}).get("by", ["", ""])[1] == "\\lpx{\\lpnocs}", a_blank)


def math_pay(cell, p, cons):
    return {sg.TEXT_CONTENT: "math_accent", sg.NONE_CONTENT: "misplaced_tab"}.get(p, "ok")


r_pmod = fake_sig(fake_macro(1, cells_ok=("math",), pay=math_pay))
r_matrix = fake_sig(fake_macro(1, cells_ok=("math",), pay=lambda c, p, k: {
    sg.TEXT_CONTENT: "math_accent"}.get(p, "ok")))
check("sig: an alignment's body (a&b compiles there) is TyMath, not TyLabel (\\matrix, \\cases)",
      r_matrix["variants"][0]["args"][0]["argty"] == "TyMath", r_matrix.get("variants"))
check("sig: a math-only command's argument is TyMath (\\pmod{\\\"a} is fatal; version 1's "
      "$a$ toggled out of math and read it as not typeset)",
      r_pmod["status"] == "attested" and r_pmod["variants"][0]["base_cell"] == "math" and
      r_pmod["variants"][0]["args"][0]["argty"] == "TyMath", r_pmod.get("variants"))
# Signature version 3 (review round 2). Each case is one of its findings'
# shapes, on the fake TeX.
def _cell(rec, c):
    return rec["variants"][0]["cells"][c] if rec["status"] == "attested" else {}


def _fails(pred):
    return lambda cell, use: ({"o": "fatal", "e": "other", "m": "X."} if pred(cell, use)
                              else None)


r_parlike = fake_sig(fake_macro(0, follow=lambda c: {"text": "mode:v", "list": "mode:v"}
                                .get(c, True)))
check("sig v3: a use that leaves the paragraph (\\par, \\section, \\item) records the mode "
      "after it and composes through the transition to the cell of that mode (HIGH-1)",
      _cell(r_parlike, "text").get("mode_after") == "v" and
      _cell(r_parlike, "text").get("follower_cell") == "vertical" and
      _cell(r_parlike, "text").get("shape_checked") is True and
      _cell(r_parlike, "list").get("follower_cell") == "listv" and
      _cell(r_parlike, "list").get("shape_checked") is True, r_parlike.get("variants"))
r_tomath = fake_sig(fake_macro(0, follow=lambda c: "mode:mi" if c == "text" else True))
check("sig v3: a mode change with no attested transition is not shape-checked",
      _cell(r_tomath, "text").get("shape_checked") is False and
      _cell(r_tomath, "vertical").get("shape_checked") is True)
r_hss = fake_sig(fake_macro(0, cells_ok=("vertical",),
                            follow=lambda c: "mode:h" if c == "vertical" else True))
check("sig v3: a mode change whose target cell rejects the use (\\hss) leaves no composing "
      "cell: unresolved (HIGH-5)", r_hss["status"] == "unresolved" and
      any(a.get("reason") == sg.NO_COMPOSE for a in r_hss["attempts"].values()), r_hss)
r_hss2 = fake_sig(fake_macro(0, follow=lambda c: "mode:h" if c == "vertical" else True,
                             special=_fails(lambda c, u: c == "vertical" and
                                            u.endswith(sg.FOLLOWER["text"]))))
check("sig v3: the transition probe (the use then the target cell's material) must compile",
      _cell(r_hss2, "vertical").get("shape_checked") is False and
      _cell(r_hss2, "text").get("shape_checked") is True)
r_redef = fake_sig(fake_macro(0, follow=lambda c: "redef"))
r_alloc = fake_sig(fake_macro(0, follow=lambda c: "state"))
check("sig v3: a use that redefines a body-typeable name or allocates a register is "
      "unresolved (HIGH-4)", r_redef["status"] == "unresolved" and
      r_alloc["status"] == "unresolved")
r_rep = fake_sig(fake_macro(0, special=_fails(lambda c, u: u.count("\\lpx") > 1)))
check("sig v3: a use whose repetition fails is unresolved (definers, nesting, dead cycles)",
      r_rep["status"] == "unresolved" and
      {a.get("reason") for a in r_rep["attempts"].values()} == {sg.EXACT_REASONS["repeat"]},
      r_rep.get("attempts"))
r_ctr = fake_sig(fake_macro(0, special=_fails(lambda c, u: c.startswith(sg.CTR + "27:"))))
check("sig v3: a use that fails with the counters at 27 is unresolved (\\fnsymbol, \\Alph)",
      r_ctr["status"] == "unresolved" and
      {a.get("reason") for a in r_ctr["attempts"].values()} == {sg.EXACT_REASONS["counters"]})
r_vss = fake_sig(fake_macro(0, special=_fails(lambda c, u: c == sg.VMID + "vertical")))
check("sig v3: a vertical outcome that differs after a paragraph is position-dependent and "
      "unchecked (\\vss, HIGH-5)", "position_dependent" in _cell(r_vss, "vertical") and
      _cell(r_vss, "vertical").get("shape_checked") is False and
      _cell(r_vss, "text").get("shape_checked") is True)


def text_pay(moving_fails):
    def pay(cell, p, cons):
        if p == sg.MATH_CONTENT:
            return "missing_dollar"
        if p == sg.NONE_CONTENT:
            return "misplaced_tab"
        if p == sg.MOVING_CONTENT and cons and moving_fails:
            return "undefined_cs"
        return "ok"
    return pay


r_sect = fake_sig(fake_macro(1, cells_ok=("text", "vertical"), pay=text_pay(True)))
r_bf = fake_sig(fake_macro(1, cells_ok=("text", "vertical"), pay=text_pay(False)))
a_sect = r_sect["variants"][0]["args"][0]
check("sig v3: a text slot whose payload is moved (a fragile command is fatal in the "
      "consumer document) is not TyText; one only typeset is (HIGH-3)",
      a_sect["argty"] is None and (a_sect.get("refuted") or {}).get("argty") == "TyText" and
      (a_sect["refuted"]["by"][1]).endswith("{%s}" % sg.MOVING_CONTENT) and
      r_bf["variants"][0]["args"][0]["argty"] == "TyText", a_sect)
LAT3 = [("TyNumber", "1"), ("TyCounter", "enumi"), ("TyEnvName", "center")]
r_value = fake_sig(fake_macro(1, pay=lambda c, p, k: "missing_number" if p == "enumi" else
                              label_pay()(c, p, k)), LAT3)
a_value = r_value["variants"][0]["args"][0]
check("sig v3: a key slot that fails when the key names a counter (\\value) is not TyLabel "
      "(HIGH-2)", a_value["argty"] is None and
      (a_value.get("refuted") or {}).get("argty") == "TyLabel", a_value)
r_key = fake_sig(fake_macro(1, pay=label_pay()), LAT3)
check("sig v3: a key slot taking a punctuated key and the configuration's counter and "
      "environment names is TyLabel", r_key["variants"][0]["args"][0]["argty"] == "TyLabel")
r_sym = fake_sig(fake_macro(1, pay=lambda c, p, k: "ok" if p in ("1", "0") else
                            ("bad_char_code" if p in ("300", "-1") else "missing_number")), LAT3)
a_sym = r_sym["variants"][0]["args"][0]
check("sig v3: a number slot whose value matters (\\symbol{300}) is not TyNumber (MEDIUM)",
      a_sym["argty"] is None and (a_sym.get("refuted") or {}).get("argty") == "TyNumber", a_sym)
V3 = (r_parlike, r_tomath, r_hss, r_hss2, r_redef, r_alloc, r_rep, r_ctr, r_vss, r_sect, r_bf)
# The replay verifier on the synthetic records: exact, and it sees a changed field.
check("sig: replay re-derives the synthetic records exactly",
      all(sg.replay(r, "\\lpx", []) == [] for r in (r_string, r_relax, r_part, r_label, r_title,
                                                     r_blank, r_pmod) + V3) and
      all(sg.replay(r, "\\lpx", LAT3) == [] for r in (r_value, r_key, r_sym)))
m_label = copy.deepcopy(r_label)
m_label["variants"][0]["args"][0]["argty"] = "TyText"
m_title = copy.deepcopy(r_title)
m_title["variants"][0]["args"][0].pop("refuted", None)
m_title["variants"][0]["args"][0]["argty"] = "TyLabel"
check("sig: replay sees a changed argty and an erased refutation",
      sg.replay(m_label, "\\lpx", []) != [] and sg.replay(m_title, "\\lpx", []) != [])
# The reproducibility sample rotates with its seed and always holds the
# adversarial names (review MEDIUM-2).
_pool = ["n%04d" % i for i in range(2000)] + list(sg.ADVERSARIAL_NAMES)
s_a, s_b = sg.signature_sample(_pool, "k:a", 60), sg.signature_sample(_pool, "k:b", 60)
check("sig: the reproducibility sample rotates with its seed and holds the adversarial names",
      s_a != s_b and set(sg.ADVERSARIAL_NAMES) <= set(s_a) and set(sg.ADVERSARIAL_NAMES) <= set(s_b)
      and s_a == sg.signature_sample(_pool, "k:a", 60))


# The committed sidecars: bound to their contract's bytes, every record
# re-derived in full from its own probe log (replay), the calibration and the
# definer table checked, the summary recomputed.
def _first(side, pred):
    for n in sorted(side["signatures"]):
        r = side["signatures"][n]
        if r["status"] == "attested":
            for vi, v in enumerate(r["variants"]):
                # A variant with no argument is still a candidate (\\vss).
                for ai, a in enumerate(v["args"] or [{}]):
                    if pred(r, v, a):
                        return n, vi, ai
    return None


SDIR = REPO / sg.SIG_DIR
sidecars = sorted(SDIR.glob("*.json")) if SDIR.is_dir() else []
for sf in sidecars:
    side = json.loads(sf.read_text(encoding="utf-8"))
    cp = REPO / side.get("contract", "")
    cbytes = cp.read_bytes() if cp.is_file() else None
    t0 = time.monotonic()
    probs = sg.check_sidecar(side, cbytes, REPO)
    check("sidecar %s: consistent with its contract, its calibration and its own probe log "
          "(every record re-derived by replay)" % sf.name, not probs, probs[:5])
    check("sidecar %s: solo count = calibration + name/environment probes + definer rows"
          % sf.name, side["solo"]["probes"] == len(side.get("calibration", [])) +
          side["summary"]["solo_probes"] + len(side["definer_rules"]),
          (side["solo"], side["summary"]["solo_probes"], len(side["definer_rules"])))
    check("sidecar %s: covers its whole scope" % sf.name,
          side["scope"].get("names") != "subset" and side["summary"]["names"] > 0)
    lat = [(x["argty"], x["payload"]) for x in side.get("lattice", [])]

    # In-gate kill-tests of the check itself: each attested field, changed in
    # one record, must be seen (review MEDIUM-1: version 1 re-derived only the
    # use, r, the drop-last grab and the per-cell polarity).
    def killed(label, name, mutate, env=False):
        rec = copy.deepcopy((side["environments"] if env else side["signatures"])[name])
        mutate(rec)
        if env:
            p = sg.replay(rec, "", lat, env=name)
        else:
            p = sg.replay(rec, sg.cs(name), lat)
            for v in rec.get("variants", []):
                p += sg.check_variant(v, rec["probes"], sg.cs(name), "")
        check("sidecar kill: %s (%s) is seen" % (label, name), bool(p))

    def arg_at(loc):
        n, vi, ai = loc
        return lambda rec: rec["variants"][vi]["args"][ai]

    kills = [
        ("a changed argty", lambda r, v, a: a.get("argty") == "TyText",
         lambda loc: lambda rec: arg_at(loc)(rec).update(argty="TyMath")),
        ("a changed lattice argty", lambda r, v, a: a.get("argty") == "TyDimen",
         lambda loc: lambda rec: arg_at(loc)(rec).update(argty="TyNumber")),
        ("a changed negative", lambda r, v, a: bool(a.get("negative")),
         lambda loc: lambda rec: arg_at(loc)(rec).update(negative="ok")),
        ("a flipped long", lambda r, v, a: a.get("long") is True,
         lambda loc: lambda rec: arg_at(loc)(rec).update(long=False)),
        ("a changed content kind", lambda r, v, a: bool(a.get("content")),
         lambda loc: lambda rec: arg_at(loc)(rec)["content"].update(
             {sorted(arg_at(loc)(rec)["content"])[0]: "opaque"})),
        ("an erased refutation", lambda r, v, a: bool(a.get("refuted")),
         lambda loc: lambda rec: arg_at(loc)(rec).pop("refuted")),
        ("a flipped star flag", lambda r, v, a: r["star"] is True,
         lambda loc: lambda rec: rec.update(star=False)),
        ("a dropped starred variant", lambda r, v, a: len(r["variants"]) > 1,
         lambda loc: lambda rec: rec["variants"].pop()),
        ("a flipped shape_checked", lambda r, v, a: any(
            c.get("allowed") == "ok" and c.get("shape_checked") for k, c in v["cells"].items()
            if k != v["base_cell"]),
         lambda loc: lambda rec: [c.update(shape_checked=False) for k, c in
                                  rec["variants"][loc[1]]["cells"].items()
                                  if c.get("shape_checked") and
                                  k != rec["variants"][loc[1]]["base_cell"]][:1]),
        ("a changed follow outcome", lambda r, v, a: any(
            c.get("follow") == "follow" for c in v["cells"].values()),
         lambda loc: lambda rec: [c.update(follow="undefined_cs") for c in
                                  rec["variants"][loc[1]]["cells"].values()
                                  if c.get("follow") == "follow"][:1]),
        # Version 3: the new per-cell fields.
        ("a changed mode_after", lambda r, v, a: any(
            c.get("mode_after") for c in v["cells"].values()),
         lambda loc: lambda rec: [c.update(mode_after="mi") for c in
                                  rec["variants"][loc[1]]["cells"].values()
                                  if c.get("mode_after")][:1]),
        ("a changed follower cell", lambda r, v, a: any(
            c.get("follower_cell") for c in v["cells"].values()),
         lambda loc: lambda rec: [c.update(follower_cell="math") for c in
                                  rec["variants"][loc[1]]["cells"].values()
                                  if c.get("follower_cell")][:1]),
        ("an unchecked accepting cell marked checked", lambda r, v, a: any(
            c.get("allowed") == "ok" and not c.get("shape_checked") for c in v["cells"].values()),
         lambda loc: lambda rec: [c.update(shape_checked=True) for c in
                                  rec["variants"][loc[1]]["cells"].values()
                                  if c.get("allowed") == "ok" and not c.get("shape_checked")][:1]),
        ("an erased position dependence", lambda r, v, a: any(
            "position_dependent" in c for c in v["cells"].values()),
         lambda loc: lambda rec: [c.pop("position_dependent") for c in
                                  rec["variants"][loc[1]]["cells"].values()
                                  if "position_dependent" in c][:1]),
        ("a flipped after_space", lambda r, v, a: any(
            p.get("after_space") is not None for p in v["optional_positions"].values()),
         lambda loc: lambda rec: [p.update(after_space=not p["after_space"]) for p in
                                  rec["variants"][loc[1]]["optional_positions"].values()
                                  if p.get("after_space") is not None][:1]),
        ("a changed optional position", lambda r, v, a: v["r"] >= 1,
         lambda loc: lambda rec: rec["variants"][loc[1]]["optional_positions"]["0"].update(
             count=rec["variants"][loc[1]]["optional_positions"]["0"]["count"] + 1)),
    ]
    for label, pred, mk in kills:
        loc = _first(side, pred)
        check("sidecar %s: the sidecar has a record for the kill-test '%s'" % (sf.name, label),
              loc is not None)
        if loc is not None:
            killed(label, loc[0], mk(loc))
    unres = sorted(n for n, r in side["signatures"].items() if r["status"] == "unresolved"
                   and r.get("attempts"))
    if unres:
        killed("a changed unresolved reason", unres[0], lambda rec: [
            a.update(reason="x") for a in rec["attempts"].values()][:1])
    envs = sorted(e for e, r in side["environments"].items() if r["status"] == "attested")
    if envs:
        killed("a changed body mode", envs[0], lambda rec: rec.update(
            body_mode="text" if rec["body_mode"] != "text" else "math"), env=True)
        killed("a changed push", envs[0], lambda rec: rec.update(
            pushes=sorted(set(rec["pushes"]) ^ {"caption"})), env=True)
    n0 = _first(side, lambda r, v, a: a.get("kind") == "req")[0]
    bad = copy.deepcopy(side["signatures"][n0])
    bad["probes"] = [p for p in bad["probes"] if p[2] != "grab"]
    check("sidecar kill: dropping %s's grab probes is seen" % n0,
          any("grab" in x for v in bad["variants"]
              for x in sg.check_variant(v, bad["probes"], sg.cs(n0), "")))
    # Global claims: the whole check on a mutated copy.
    mut = copy.deepcopy(side)
    mut["calibration"][0][2] = "fatal" if mut["calibration"][0][2] == "ok" else "ok"
    mut["definer_rules"][0] = dict(mut["definer_rules"][0], outcome="fatal")
    mut["definer_rules"][0].pop("error_class", None)
    mut["definer_rules"][0].pop("message", None)
    fl = sg.check_sidecar(mut, cbytes)
    check("sidecar kill: a failed calibration premise is seen",
          any(x.startswith("calibration") for x in fl), fl[:3])
    check("sidecar kill: a definer row flipped to fatal with no class is seen",
          any(x.startswith("definer") and "without an error class" in x for x in fl), fl[:3])
    # Version 3 (review round 2, LOW): fields the replay never reads are
    # bound to the contract and to the probe design.
    for label, mutate, prefix in [
            ("a letter added (@)", lambda m: m["letters"].append(64), "binding: the signatures"),
            ("the pin's format hash", lambda m: m["pin"].update(fmt_sha256="0" * 64),
             "binding: pin"),
            ("the pin's image", lambda m: m["pin"].update(image="x"), "binding: pin"),
            ("the config key", lambda m: m.update(config_key="x"), "binding: config_key"),
            ("the follow probe's definitions",
             lambda m: m["follow_probe"].update(definitions="x"), "design: recorded follow_probe"),
            ("the consumers", lambda m: m["consumers"].update(body_after="x"),
             "design: recorded consumers"),
            ("the sentinel", lambda m: m.update(sentinel="x"), "design: recorded sentinel"),
            ("the protocol", lambda m: m.update(protocol="x"), "design: recorded protocol"),
            ("the long/stored witnesses", lambda m: m["witnesses"].update(long="x", stored="y"),
             "design: recorded witnesses"),
            ("the counters set", lambda m: m["counters_set"].append("zz"),
             "binding: counters_set")]:
        mm = copy.deepcopy(side)
        mutate(mm)
        fl = sg.check_sidecar(mm, cbytes, REPO)
        check("sidecar kill: %s is seen" % label, any(x.startswith(prefix) for x in fl), fl[:3])
    check("sidecar kill: a stale contract is seen",
          cbytes is not None and any("stale" in x for x in sg.check_sidecar(side, cbytes + b" ",
                                                                               REPO)))
    print("check_gen_contract_parsers: sidecar %s checked in %.1f s"
          % (sf.name, time.monotonic() - t0))
DFILE = REPO / sg.DECL_DIR / "newtheorem.json"
if DFILE.is_file():
    dt = json.loads(DFILE.read_text(encoding="utf-8"))
    check("decl templates: schema and the three owner combinations",
          dt.get("schema") == sg.DECL_SCHEMA and
          sorted(dt["owners"]) == sorted(o for o, _ in sg.DECL_OWNERS))
    for owner, ent in dt["owners"].items():
        check("decl templates %s: every form from two complete closed worlds" % owner,
              ent["base_complete"] and all(f["complete"] or "load_outcome" in f
                                           for f in ent["forms"].values()),
              {k: f.get("incomplete_reasons") for k, f in ent["forms"].items()})
        check("decl templates %s: `defines` holds only names carrying the declared name, "
              "the rest are incidental (review LOW)" % owner,
              all(sg.DECL_FRESH in n for f in ent["forms"].values()
                  for n in f.get("defines", {})) and
              all(sg.DECL_FRESH not in n for f in ent["forms"].values()
                  for n in f.get("incidental_defines", {})) and
              all("incidental_defines" in f for f in ent["forms"].values() if "defines" in f))

print("check_gen_contract_parsers: %d checks, %d failed" % (count, fails))
sys.exit(1 if fails else 0)
