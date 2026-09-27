#!/usr/bin/env python3
"""Unit tests for the parsers of scripts/tools/gen_contract.py, on RECORDED logs.

Every fixture under corpora/contracts/parser_fixtures/ is an excerpt of a real
log the generator produced under the pinned TeX Live image (see its README);
nothing here is synthesised except the few byte strings that test the name
encoders. Pure: no docker, no TeX. Run it after any change to the parsers.

Each check asserts the KIND of the outcome, in each direction where there is
one (a record is read AND a quantity is not; an error is found AND a printed
meaning that merely contains "! LaTeX Error" is not).
"""
import json
import sys
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import gen_contract as gc  # noqa: E402

FIX = HERE.parent.parent / "corpora" / "contracts" / "parser_fixtures"
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

print("selftest_gen_contract: %d checks, %d failed" % (count, fails))
sys.exit(1 if fails else 0)
