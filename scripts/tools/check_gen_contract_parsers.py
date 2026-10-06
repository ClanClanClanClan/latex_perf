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
# There is ONE definition of the oracle's TeX environment, in _oracle.py:
# ORACLE_TEX_VARS, the fixed run variables and the clock (OPEN-128), which
# run_engine imposes. The generator passes the protocol's own values plus the
# log width, and chooses a CLOCK per environment; each check below reads that
# single source, never a copy. (The previous form compared gen_contract.TEX_ENV
# with the graders' SOURCE TEXT, and failed three checks the day #617 moved
# the graders' copy into _oracle.py although no environment had changed.)
import re  # noqa: E402
import _oracle  # noqa: E402
base = _oracle.oracle_tex_vars()
check("env: the oracle's one TeX environment is the recorded protocol "
      "(openin_any=p, openout_any=p; the clock is the clock's)",
      _oracle.ORACLE_TEX_VARS == {"openin_any": "p", "openout_any": "p"},
      _oracle.ORACLE_TEX_VARS)
check("env: the private TEXMFHOME/TEXMFVAR/TEXMFCONFIG are the run container's, "
      "at fixed paths (OPEN-128)",
      {k: base.get(k) for k in ("TEXMFHOME", "TEXMFVAR", "TEXMFCONFIG")}
      == _oracle.FIXED_TREES, base)
grader_env = _oracle._Base.tex_env(None)
check("env: the graders' tex_env carries the one environment",
      all(grader_env.get(k) == v for k, v in base.items()), base)
for env in gc.ENVS:
    v = gc.tex_vars(env)
    over = {k: x for k, x in v.items() if base.get(k) != x}
    check("env %s: exactly the oracle's environment plus the log width"
          % env, set(base) <= set(v) and over == dict(gc.LOG_WIDTH), over)
check("env: the grading environment runs under the protocol's FIXED clock "
      "(ADR-015 E10), never the real one",
      gc.CLOCKS["grading"] == _oracle.PROTOCOL_CLOCK
      and base.get("FORCE_SOURCE_DATE") == "1"
      and base.get("LP_CLOCK_EPOCH") == str(_oracle.PROTOCOL_EPOCH)
      and base.get("SOURCE_DATE_EPOCH") == str(_oracle.PROTOCOL_EPOCH), gc.CLOCKS)
# The date-dependent names are found by VARYING the fixed clock (OPEN-128 (6)):
# the second clock is a fixed clock every calendar field of which differs from
# the protocol's, so a name that depends on any one field (l3's
# \c_sys_year_int, \c_sys_minute_int, ...) differs between the two.
import datetime as _dt  # noqa: E402
_a = _dt.datetime.fromtimestamp(_oracle.clock_epoch(gc.CLOCKS["grading"]), _dt.timezone.utc)
_b = _dt.datetime.fromtimestamp(_oracle.clock_epoch(gc.CLOCKS["second_date"]), _dt.timezone.utc)
_same = [f for f in ("year", "month", "day", "hour", "minute", "second")
         if getattr(_a, f) == getattr(_b, f)] + (
    ["weekday"] if _a.weekday() == _b.weekday() else [])
check("env: the second clock is a FIXED clock differing from the protocol's in every "
      "calendar field (year, month, day, weekday, hour, minute, second)",
      gc.CLOCKS["second_date"].startswith(_oracle.CLOCK_PREFIX) and not _same, _same)
check("env: the log-width overrides change no graded variable",
      not set(gc.LOG_WIDTH) & set(base) and not set(gc.LOG_WIDTH) & {"FORCE_SOURCE_DATE"})
check("env: every generator variable is one the oracle forwards",
      all(_oracle._ENV_FORWARD.match(k) for e in gc.ENVS for k in gc.tex_vars(e)))
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
        # the three state environments (OPEN-128: the protocol clock, the
        # second fixed clock, the second job name).
        cps = c.get("coverage_passes") or []
        want = {(e, j, gc.hist_label(h)) for e, j in gc.STATE_ENVS
                for h in gc.protocol_histories()}
        have = {(x.get("env"), x.get("jobname"), x.get("history")) for x in cps}
        check("contract %s: TeX's hash count on every pass of every pass history, in "
              "all three environments" % cf.name, have == want and len(cps) == len(want),
              sorted(want - have))
        bad_cp = [x for x in cps if x.get("uncovered") != 0 or "error" in x or
                  ((x.get("env"), x.get("jobname")) == gc.STATE_ENVS[0] and
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

print("check_gen_contract_parsers: %d checks, %d failed" % (count, fails))
sys.exit(1 if fails else 0)
