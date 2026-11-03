#!/usr/bin/env python3
"""Unit tests of the P2 diagnostics baseline: the oracle-side record
(_p2_diag.diag_record), the CLI-side prediction (_p2_diag.cli_prediction), the
pre-registered matching and metrics, the sample-3 seal (_sample_seal), and the
producer's refusals (p2_baseline.py). Pure: no docker, no TeX, no CLI.

FIXTURES. corpora/p2_diag/fixtures/<case>/ holds a SYNTHETIC document (written
for this test, no corpus paper) and the main.log that pdfTeX
3.141592653-2.6-1.40.29 (TeX Live 2026) wrote for it with
`-interaction=nonstopmode -halt-on-error`, run on the LAPTOP TeX Live on
2026-11-03 -- NOT the oracle (ADR-012 decision 7). They test log PARSING
only: the log format is pdfTeX's, the same at the pin; no grade is taken from
them. Further SYNTHETIC logs are built inline where a case needs a shape the
fixtures do not have; each is marked SYNTHETIC.

THE SEAL TESTS never touch a sample-3 document or output. They defeat-test the
refusal against a SYNTHETIC sealed manifest in a temporary repo; against the
real seal they assert only counts (the sealed set has exactly 200 ids; samples
1-2 share none of them), never an id.

Exit 0 all checks pass; 1 a check failed. The last line prints the number of
checks run, floored, so an empty run cannot read as a pass.
"""
from __future__ import annotations

import io
import json
import os
import sys
import tempfile
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import _oracle  # noqa: E402
import _p2_diag as d  # noqa: E402
import _sample_seal as seal  # noqa: E402
import p2_baseline  # noqa: E402

REPO = HERE.parent.parent
FIX = REPO / "corpora" / "p2_diag" / "fixtures"
MIN_CHECKS = 120
fails = count = 0


def check(name, cond, detail=""):
    global fails, count
    count += 1
    if not cond:
        fails += 1
        print(f"FAIL {name} {detail}")


def fixture(case):
    root = FIX / case

    def rs(rel):
        f = root / rel
        return f.read_bytes() if f.is_file() else None
    return d.diag_record((root / "main.log").read_bytes(), read_source=rs,
                         in_tree=lambda n: (root / n).is_file())


# ── 1. the oracle-side record on recorded logs ───────────────────────────────
# case: (has_error, consistent, class, object, file, line, frame, author_file, verified)
EXPECT = {
    "clean": (False, None, None, None, None, None, None, None, None),
    "undef_cs_root": (True, True, "undefined-cs", "\\undefinedmacro", "main.tex", 5,
                      "document", "main.tex", True),
    "undef_cs_child": (True, True, "undefined-cs", "\\nosuchcs", "sec/intro.tex", 4,
                       "document", "sec/intro.tex", True),
    "missing_sty": (True, True, "missing-file", "nosuchpackagexyz", "main.tex", 4,
                    "document", "main.tex", True),
    "error_in_system_file": (True, True, "command-already-defined", "\\iint", None, 630,
                             "system", "main.tex", None),
    "runaway_eof": (True, True, "brace-imbalance", None, None, None, "none", None, None),
    "missing_dollar": (True, True, "math-mode", None, "main.tex", 3, "document", "main.tex", True),
    "macro_context": (True, True, "undefined-cs", "\\alsoundefined", "main.tex", 4,
                      "document", "main.tex", True),
    "overfull_then_error": (True, True, "undefined-cs", "\\undefinedafterbox", "main.tex", 5,
                            "document", "main.tex", True),
    "forged_message": (True, False, "other", None, "main.tex", 2, "document", "main.tex", False),
    "long_line": (True, True, "undefined-cs", "\\badcsinlongline", "main.tex", 3,
                  "document", "main.tex", True),
    "env_undefined": (True, True, "undefined-env", "nosuchenv", "main.tex", 3,
                      "document", "main.tex", True),
    "deep_path_child": (True, True, "undefined-cs", "\\deepundefined",
                        "a_very_long_directory_name_to_force_wrapping/"
                        "another_long_subdirectory_name/child_file_name.tex", 2,
                        "document", "a_very_long_directory_name_to_force_wrapping/"
                        "another_long_subdirectory_name/child_file_name.tex", True),
    "latin1_line": (True, True, "other", None, "main.tex", 4, "document", "main.tex", True),
}
cases_on_disk = sorted(p.name for p in FIX.iterdir() if p.is_dir())
check("fixtures: every case on disk has an expectation and vice versa",
      cases_on_disk == sorted(EXPECT), f"{cases_on_disk} vs {sorted(EXPECT)}")
for case, exp in EXPECT.items():
    r = fixture(case)
    L = r["location"] or {}
    got = (r["has_error"], r["consistent"], (r["cause"] or {}).get("class"),
           (r["cause"] or {}).get("object"), L.get("file"), L.get("line"), L.get("frame"),
           L.get("author_file"), L.get("verified"))
    for i, field in enumerate(("has_error", "consistent", "class", "object", "file", "line",
                               "frame", "author_file", "verified")):
        check(f"record {case}.{field}", got[i] == exp[i], f"{got[i]!r} != {exp[i]!r}")

r = fixture("undef_cs_root")
check("record: the message is the full first paragraph, untruncated",
      r["first_error"]["message"] == "! Undefined control sequence.", r["first_error"]["message"])
check("record: the file stack at the error is the tree root only",
      r["location"]["file_stack"] == ["./main.tex"], r["location"]["file_stack"])
r = fixture("undef_cs_child")
check("record: the child is on top of the root",
      r["location"]["file_stack"] == ["./main.tex", "./sec/intro.tex"], r["location"]["file_stack"])
r = fixture("error_in_system_file")
check("record: a TeX Live frame on top is 'system', its path kept",
      r["location"]["top"].endswith("/amsmath.sty"), r["location"]["top"])
check("record: the multi-line LaTeX message keeps its second line",
      "Or name \\end... illegal" in r["first_error"]["message"], r["first_error"]["message"])
check("record: help text after the blank line is not the message",
      "See the LaTeX manual" not in r["first_error"]["message"])
r = fixture("missing_sty")
check("record: the missing-file l.N comes from the Emergency-stop block",
      r["location"]["line_from_block"] == 1, r["location"]["line_from_block"])
check("record: the halting message is the Emergency stop",
      r["halting_message"].startswith("! Emergency stop."), r["halting_message"])
r = fixture("long_line")
check("record: a 79-byte context line is not glued to the help text",
      "The control sequence" not in (r["first_error"]["l_after"] or ""),
      r["first_error"]["l_after"])
r = fixture("forged_message")
check("record: a \\message-forged `!` block makes the record inconsistent",
      r["consistent"] is False and "2 error blocks" in r["consistent_why"], r["consistent_why"])
check("record: the forged block's l.N fails source verification",
      r["location"]["verified"] is False)
r = fixture("deep_path_child")
check("record: a stack path wrapped at 79 bytes is un-wrapped",
      r["location"]["file_stack"][-1].endswith("child_file_name.tex"), r["location"]["file_stack"])

# SYNTHETIC logs for shapes the fixtures lack.
SYN_PAREN = (b"(./main.tex\n"
             b"Missing character: There is no ( in font cmr10!\n"
             b"Overfull \\hbox (3.0pt too wide) in paragraph at lines 4--5\n"
             b"[]\\OT1/cmr/m/n/10 (unbalanced text in the box dump\n"
             b"\n"
             b"(./sec.tex) (./sec2.tex\n"
             b"! Undefined control sequence.\n"
             b"l.2 \\foo\n"
             b"        \n")
r = d.diag_record(SYN_PAREN, in_tree=lambda n: True)
check("stack: unbalanced document text in a box dump / missing-character line is skipped",
      r["location"]["file_stack"] == ["./main.tex", "./sec2.tex"], r["location"]["file_stack"])
check("stack: the skipped lines are counted",
      r["location"]["stack_stats"]["skipped_lines"] == 2, r["location"]["stack_stats"])
SYN_UNDER = b"(./main.tex)) extra close\n! Undefined control sequence.\nl.1 \\x\n      \n"
r = d.diag_record(SYN_UNDER)
check("stack: an underflow is counted, not hidden",
      r["location"]["stack_stats"]["underflow"] == 1 and r["location"]["frame"] == "none",
      r["location"])
check("record: no log -> no error", d.diag_record(None)["has_error"] is False)
check("record: a log with no `!` line -> no error",
      d.diag_record(b"(./main.tex)\nNo pages of output.\n")["has_error"] is False)
check("record: the final-report line alone is not an error block",
      d.diag_record(b"!  ==> Fatal error occurred, no output PDF file produced!\n")["has_error"]
      is False)
check("record: the module reuses the oracle's line model (one implementation)",
      d._unwrap_log is _oracle._unwrap_log)
check("tree_path: an absolute path under the run directory is in the tree",
      d.tree_path("/tmp/lp-oracle-x/w/sec/a.tex", ("/tmp/lp-oracle-x/w",)) == "sec/a.tex")
check("tree_path: a TeX Live path is outside the tree",
      d.tree_path("/usr/local/texlive/2026/texmf-dist/tex/latex/base/article.cls") is None)
check("tree_path: ../ escapes are outside the tree", d.tree_path("./../x.tex") is None)

# ── 2. source-line verification ──────────────────────────────────────────────
check("unprint ^^e9", d.tex_unprint("Caf^^e9") == b"Caf\xe9")
check("unprint ^^M / ^^I", d.tex_unprint("a^^Mb^^I") == b"a\rb\t")
check("unprint ^^? (DEL)", d.tex_unprint("^^?") == b"\x7f")
src = b"line one\n\\foo bar baz   \nthree\n"
check("verify: exact", d.verify_location(src, 2, "\\foo", " bar baz")[0])
check("verify: wrong line", not d.verify_location(src, 1, "\\foo", " bar baz")[0])
check("verify: beyond the file", not d.verify_location(src, 9, "\\foo", "")[0])
check("verify: left-truncated before-text", d.verify_location(src, 2, "...oo", " bar baz")[0])
check("verify: right-truncated after-text", d.verify_location(src, 2, "\\foo", " bar...")[0])
check("verify: an edited source fails",
      not d.verify_location(src.replace(b"bar", b"BAR"), 2, "\\foo", " bar baz")[0])
check("verify: CRLF line ends", d.verify_location(b"a\r\n\\foo x\r\n", 2, "\\foo", " x^^M")[0])
check("verify: unreadable source fails", not d.verify_location(None, 1, "", "")[0])

# ── 3. the cause taxonomy ────────────────────────────────────────────────────
CLS = [
    ("! LaTeX Error: File `foo.sty' not found.", "missing-file", "foo"),
    ("! I can't find file `sec/intro'.", "missing-file", "intro"),
    ("! Package pdftex.def Error: File `fig-eps-converted-to.pdf' not found: using draft "
     "setting.", "missing-file", "fig-eps-converted-to.pdf"),
    ("! Undefined control sequence.", "undefined-cs", None),
    ("! LaTeX Error: Command \\iint already defined.", "command-already-defined", "\\iint"),
    ("! LaTeX Error: Environment proofx undefined.", "undefined-env", "proofx"),
    ("! LaTeX Error: \\begin{itemize} on input line 4 ended by \\end{enumerate}.",
     "env-mismatch", "itemize"),
    ("! LaTeX Error: Missing \\begin{document}.", "missing-begin-document", None),
    ("! LaTeX Error: Option clash for package xcolor.", "option-clash", "xcolor"),
    ("! Package inputenc Error: Invalid UTF-8 byte \"E9.", "encoding", None),
    ("! LaTeX Error: Unicode character Π (U+03A0)", "encoding", None),
    ("! Fatal Package fontspec Error: The fontspec package requires either XeTeX or "
     "LuaTeX.", "engine-incompatible", "fontspec"),
    ("! Missing } inserted.", "brace-imbalance", None),
    ("! Paragraph ended before \\@tempa was complete.", "brace-imbalance", None),
    ("! Missing \\right. inserted.", "left-right-imbalance", None),
    ("! Double superscript.", "math-mode", None),
    ("! Misplaced alignment tab character &.", "alignment", None),
    ("! TeX capacity exceeded, sorry [grouping levels=255].", "tex-capacity", None),
    ("! Package cleveref Error: cleveref must be loaded after hyperref!.", "package-error",
     "cleveref"),
    ("! Class amsart Error: No counter 'foo' defined.", "class-error", "amsart"),
    ("! LaTeX Error: Something else.", "latex-error", None),
    ("! Emergency stop.", "emergency-stop", None),
    ("! Whatever pdfTeX says.", "other", None),
]
for msg, cls, obj in CLS:
    c = d.classify_message(msg)
    check(f"class of {msg[:48]!r}", (c["class"], c["object"]) == (cls, obj), c)
check("class: a non-error line has no class", d.classify_message("hello")["class"] is None)
check("class: every taxonomy class is exercised",
      {c for _, c, _ in CLS} == set(d.CLASSES), set(d.CLASSES) - {c for _, c, _ in CLS})

# ── 4. the CLI-side prediction (renderings of validators_cli.ml's printf formats) ──
MODEL_OK = ("MODEL-CONNECTED\tPREMISE-CERTIFIED\ttier=lp-core\tbuild-graph closure and "
            "engine-feature admissibility verified over the abstract model; NOT a "
            "compilation guarantee (docs/COMPILATION_GUARANTEE.md)\n")
TAIL = ("TIER\theuristic\tLIKELY-FAIL\tLIKELY FAIL (heuristic) — not a proof\n"
        "  why not strict: \\def at main.tex:3 — rewrite \\def\\T1{x} as \\newcommand\n")
p = d.cli_prediction(MODEL_OK + "READY\t/p/main.tex\n" + TAIL)
check("cli: READY has no predictions", p["verdict"] == "READY" and p["predictions"] == [], p)
p = d.cli_prediction(MODEL_OK + "NOT-READY\t/p/main.tex\n"
                     "  T5 rule violations: [DELIM-003; PRT-001]\n" + TAIL)
check("cli: a T5 line gives one prediction per rule, in order",
      [(x["code"], x["class"]) for x in p["predictions"]]
      == [("DELIM-003", "left-right-imbalance"), ("PRT-001", None)], p["predictions"])
check("cli: why-not-strict file:line after TIER is not a prediction",
      all(x["file"] is None for x in p["predictions"]), p["predictions"])
p = d.cli_prediction(MODEL_OK + "NOT-READY\tmain.tex\n"
                     "  T0 LP-Foreign construct(s) in main.tex (outside every supported tier; "
                     "not a parse failure): \\catcode direct mutation detected; LP-Foreign "
                     "(line 3)\n")
x = p["predictions"][0]
check("cli: an LP-Foreign reason is a located claim with no cause class",
      (x["code"], x["class"], x["file"], x["line"]) == ("T0", None, "main.tex", 3), x)
p = d.cli_prediction(MODEL_OK + "NOT-READY\t/p/main.tex\n"
                     "  T2 project not closed: missing file sec/fig.tex\n")
x = p["predictions"][0]
check("cli: T2 missing file -> missing-file, object by basename",
      (x["class"], x["object"], x["file"]) == ("missing-file", "fig", None), x)
p = d.cli_prediction(
    "MODEL-CONNECTED\tPREMISE-REJECTED\ttier=lp-core\ta compilability-bearing obligation "
    "failed\n  T3 body-required feature(s) [opentype_fonts] not admitted by engine pdflatex\n"
    "READY\t/p/main.tex\n")
check("cli: verdict READY is read even when the model line rejected (as printed)",
      p["verdict"] == "READY")
p = d.cli_prediction(
    "MODEL-CONNECTED\tPREMISE-REJECTED\ttier=lp-core\ta compilability-bearing obligation "
    "failed\n  T3 body-required feature(s) [opentype_fonts] not admitted by engine pdflatex\n"
    "NOT-READY\t/p/main.tex\n  (model-connected checks reject; see MODEL-NOT-READY above)\n")
x = p["predictions"][0] if p["predictions"] else {}
check("cli: a model rejection's own line is the prediction (the pointer line is not)",
      len(p["predictions"]) == 1 and x.get("source") == "model"
      and x.get("object_set") == ["fontspec"], p["predictions"])
p = d.cli_prediction(MODEL_OK + "NOT-READY\t/p/main.tex\n"
                     "  structural-fatal (will not compile): [double superscript in math "
                     "(x^a^b): ! Double superscript; no \\documentclass (nor \\documentstyle) "
                     "in document: ! LaTeX Error: Missing \\begin{document}.]\n")
check("cli: structural-fatal reasons are classified by the TeX message they predict",
      [x["class"] for x in p["predictions"]] == ["math-mode", "missing-begin-document"],
      p["predictions"])
p = d.cli_prediction("", "NOT-READY\n  T0 parse fails in /p/x.tex: file not found\n"
                     "TIER\theuristic\tLIKELY-FAIL\tx\n")
check("cli: the file-not-found branch is read from stderr",
      p["verdict"] == "NOT-READY" and p["predictions"][0]["code"] == "T0", p)
p = d.cli_prediction(MODEL_OK + "NOT-READY\t/p/main.tex\n  artefact-fatal (main.aux): bad\n")
check("cli: artefact-fatal names its file",
      (p["predictions"][0]["class"], p["predictions"][0]["file"]) == ("artefact", "main.aux"))
check("cli: T5 classes only name compile-blocking rules",
      set(d.T5_CLASS) <= set(f"DELIM-{i:03d}" for i in range(1, 12))
      | set(f"ENC-{i:03d}" for i in range(1, 25)))

# ── 5. matching ──────────────────────────────────────────────────────────────
G = {"class": "missing-file", "object": "fig"}
check("match: class and object", d.cause_correct({"class": "missing-file", "object": "fig"}, G))
check("match: object differs", not d.cause_correct({"class": "missing-file", "object": "x"}, G))
check("match: class differs", not d.cause_correct({"class": "encoding", "object": None}, G))
check("match: no class never matches", not d.cause_correct({"class": None}, G))
check("match: a T3 feature set holds the gold package",
      d.cause_correct({"class": "engine-incompatible", "object_set": ["fontspec"]},
                      {"class": "engine-incompatible", "object": "fontspec"}))
check("match: a T3 feature set lacking the gold package",
      not d.cause_correct({"class": "engine-incompatible", "object_set": ["fontspec"]},
                          {"class": "engine-incompatible", "object": "polyglossia"}))
GL = {"file": "sec/a.tex", "line": 7}
check("loc: exact", d.location_correct({"file": "./sec/a.tex", "line": 7}, GL))
check("loc: off by one is wrong", not d.location_correct({"file": "sec/a.tex", "line": 8}, GL))
check("loc: other file", not d.location_correct({"file": "a.tex", "line": 7}, GL))
check("loc: file level", d.location_correct({"file": "sec/a.tex", "line": None}, GL, "file"))
check("loc: no line is not line-correct",
      not d.location_correct({"file": "sec/a.tex", "line": None}, GL))

# ── 6. bounds and metrics ────────────────────────────────────────────────────
lo, hi = d.clopper_pearson(0, 28)
check("cp: 0/28 upper = 1 - 0.05^(1/28)", abs(hi - (1 - 0.05 ** (1 / 28))) < 1e-6, hi)
lo, hi = d.clopper_pearson(28, 28)
check("cp: 28/28 lower = 0.05^(1/28)", abs(lo - 0.05 ** (1 / 28)) < 1e-6, lo)
lo, hi = d.clopper_pearson(5, 10)
check("cp: 5/10 is symmetric", abs(lo - (1 - hi)) < 1e-6 and abs(lo - 0.2224) < 1e-3, (lo, hi))
check("cp: n = 0 has no bound", d.clopper_pearson(0, 0) == (None, None))


def gold(cls, obj, file, line, verified=True, consistent=True):
    return {"has_error": True, "consistent": consistent, "cause": {"class": cls, "object": obj},
            "location": {"file": file, "line": line, "verified": verified}}


def pred(verdict, *ps):
    return {"verdict": verdict, "predictions": list(ps)}


NOGOLD = {"has_error": False}
ROWS = [
    # FAILS, cause right, location right
    {"graded": True, "agrees_with_record": True, "compiles": False,
     "gold": gold("missing-file", "fig", "main.tex", 4),
     "pred": pred("NOT-READY", {"class": "missing-file", "object": "fig", "file": "main.tex",
                                "line": 4})},
    # FAILS, cause wrong at top-1, right at any; no location
    {"graded": True, "agrees_with_record": True, "compiles": False,
     "gold": gold("brace-imbalance", None, "main.tex", 9),
     "pred": pred("NOT-READY", {"class": "encoding"}, {"class": "brace-imbalance"})},
    # FAILS, predicted READY (a false-READY): counts in the recall denominators
    {"graded": True, "agrees_with_record": True, "compiles": False,
     "gold": gold("undefined-cs", "\\x", "main.tex", 2), "pred": pred("READY")},
    # FAILS, gold location unverified: in cause, out of location
    {"graded": True, "agrees_with_record": True, "compiles": False,
     "gold": gold("undefined-cs", "\\y", "main.tex", 3, verified=False),
     "pred": pred("NOT-READY", {"class": None, "file": "main.tex", "line": 3})},
    # FAILS, inconsistent record: out of both
    {"graded": True, "agrees_with_record": True, "compiles": False,
     "gold": gold("other", None, "main.tex", 1, consistent=False),
     "pred": pred("NOT-READY", {"class": None})},
    # COMPILES, but a located, classed NOT-READY claim: wrong in both precisions
    {"graded": True, "agrees_with_record": True, "compiles": True, "gold": NOGOLD,
     "pred": pred("NOT-READY", {"class": "encoding", "file": "main.tex", "line": 1})},
    # disagrees with the grade of record / ungraded: excluded
    {"graded": True, "agrees_with_record": False, "compiles": False, "gold": NOGOLD,
     "pred": pred("READY")},
    {"graded": False, "gold": NOGOLD, "pred": pred("TIMEOUT")},
]
S = d.score_rows(ROWS)
check("score: inputs", S["inputs"] == {"rows": 8, "fails": 5, "compiles": 1, "cause_scored": 4,
                                       "location_scored": 3}, S["inputs"])
check("score: exclusions are counted",
      (S["excluded"]["ungraded"], S["excluded"]["disagrees_with_record"],
       S["excluded"]["cause_inconsistent"], S["excluded"]["location_unverified"]) == (1, 1, 1, 1),
      S["excluded"])
check("score: cause recall top-1 1/4", (S["cause_recall_top1"]["k"], S["cause_recall_top1"]["n"])
      == (1, 4), S["cause_recall_top1"])
check("score: cause recall any 2/4", (S["cause_recall_any"]["k"], S["cause_recall_any"]["n"])
      == (2, 4), S["cause_recall_any"])
check("score: cause precision counts a cause named on a compiling document as wrong",
      (S["cause_precision_top1"]["k"], S["cause_precision_top1"]["n"]) == (1, 3),
      S["cause_precision_top1"])
check("score: location precision 1/2 (the compiling claim is wrong; the unverified row "
      "is out)", (S["location_precision_line"]["k"], S["location_precision_line"]["n"])
      == (1, 2), S["location_precision_line"])
check("score: location recall 1/3", (S["location_recall_line"]["k"],
                                     S["location_recall_line"]["n"]) == (1, 3))
check("score: every rate carries its bounds",
      all({"k", "n", "lower95", "upper95"} <= set(v) for k, v in S.items()
          if isinstance(v, dict) and "k" in v))

# ── 7. the pre-registration and the producer's refusals ──────────────────────
PRE = REPO / p2_baseline.PREREG
block = p2_baseline.read_lines_block(PRE)
check("prereg: the lines block names this code's definitions version",
      block.get("definitions") == d.DEFINITIONS_VERSION, block.get("definitions"))
check("prereg: the committed lines are PROPOSED, not FIXED (nothing is scored yet)",
      block.get("status") == "PROPOSED", block.get("status"))
check("prereg: every line names a known metric and stat",
      all((ln["metric"] in S or ln["metric"].split(".", 1)[0] in ("inputs", "excluded"))
          and ln["stat"] in ("k", "n", "point", "lower95", "upper95") for ln in block["lines"])
      and len(block["lines"]) >= 5, [ln.get("id") for ln in block["lines"]])
check("prereg: the document states the definitions version in prose",
      d.DEFINITIONS_VERSION in PRE.read_text())


def run_main(argv):
    out, err = io.StringIO(), io.StringIO()
    with redirect_stdout(out), redirect_stderr(err):
        rc = p2_baseline.main(argv)
    return rc, err.getvalue()


with tempfile.TemporaryDirectory() as td:
    td = Path(td)
    rec = {"schema": d.SCHEMA, "definitions": d.DEFINITIONS_VERSION, "sample": 1,
           "rows": [{**r, "arxiv_id": f"0000.{i:05d}v1"} for i, r in enumerate(ROWS)]}
    (td / "rec1.json").write_text(json.dumps(rec))
    rc, err = run_main(["score", "--records", str(td / "rec1.json"), "--prereg", str(PRE),
                        "--out", str(td / "s.json")])
    check("producer: score refuses while the lines are PROPOSED",
          rc == 2 and "not 'FIXED'" in err and not (td / "s.json").exists(), (rc, err))
    fixed = dict(block, status="FIXED")
    (td / "pre.md").write_text(f"x\n{p2_baseline.LINES_BEGIN}\n```json\n{json.dumps(fixed)}\n```\n"
                               f"{p2_baseline.LINES_END}\n")
    rc, err = run_main(["score", "--records", str(td / "rec1.json"), "--prereg",
                        str(td / "pre.md"), "--out", str(td / "s.json")])
    check("producer: score runs end to end once the lines are FIXED (SYNTHETIC rows)",
          rc == 0 and (td / "s.json").is_file(), (rc, err))
    if rc == 0:
        sj = json.loads((td / "s.json").read_text())
        check("producer: every line is evaluated", len(sj["lines"]) == len(block["lines"]))
    stale = dict(fixed, definitions="p2-defs/0")
    (td / "pre0.md").write_text(f"{p2_baseline.LINES_BEGIN}\n{json.dumps(stale)}\n"
                                f"{p2_baseline.LINES_END}\n")
    rc, err = run_main(["score", "--records", str(td / "rec1.json"), "--prereg",
                        str(td / "pre0.md"), "--out", str(td / "s0.json")])
    check("producer: score refuses lines fixed for other definitions", rc == 2, (rc, err))
    (td / "rec_empty.json").write_text(json.dumps(dict(rec, rows=[])))
    rc, err = run_main(["score", "--records", str(td / "rec_empty.json"), "--prereg",
                        str(td / "pre.md"), "--out", str(td / "s1.json")])
    check("producer: zero rows is refused, not a result", rc == 2 and "zero rows" in err,
          (rc, err))

# ── 8. the sample-3 seal: try to defeat it ───────────────────────────────────
real = seal.sealed_ids(REPO)
check("seal: the real sealed set holds exactly 200 base ids", len(real) == 200, len(real))
for k in (1, 2):
    off, n, res = seal.sample_spec(k)
    rows = json.loads((REPO / "corpora/real_roots" / res).read_text())["docs"]
    check(f"seal: sample {k} has {n} rows and shares no id with the seal",
          len(rows) == n and not any(seal.base_id(r["arxiv_id"]) in real for r in rows))
    try:
        seal.refuse_window(off, n)
        ok = True
    except seal.SealError:
        ok = False
    check(f"seal: sample {k}'s window is allowed", ok)


def refused(fn, *a):
    try:
        fn(*a)
    except seal.SealError:
        return True
    return False


for k in (3, "3", " 3", "03", 3.0, True, False, 0, 4, None, "1 ", "sample3", [1]):
    check(f"seal: sample number {k!r} refused", refused(seal.sample_spec, k))
for k in (1, 2, "1", "2"):
    check(f"seal: sample number {k!r} allowed", not refused(seal.sample_spec, k))
for off, n in ((720, 200), (719, 2), (919, 1), (900, 1000), (0, 721), (700, 21),
               (720, 0), (-1, 5), (1000, -300), (720.0, 200), ("720", 200), (True, 200)):
    check(f"seal: window ({off!r}, {n!r}) refused", refused(seal.refuse_window, off, n))
for off, n in ((0, 200), (200, 200), (0, 720), (920, 10), (400, 320)):
    check(f"seal: window ({off}, {n}) allowed", not refused(seal.refuse_window, off, n))

with tempfile.TemporaryDirectory() as td:
    # A SYNTHETIC repo with a SYNTHETIC sealed manifest: no real sample-3 id.
    trepo = Path(td)
    (trepo / "corpora/real_roots").mkdir(parents=True)
    (trepo / "corpora/oracle_baseline").mkdir(parents=True)
    fake = [f"9999.{i:05d}v1" for i in range(200)]
    man = {"frame": {"offset": 720, "n": 200}, "docs": [{"arxiv_id": x} for x in fake]}
    (trepo / seal.SEALED_MANIFEST).write_text(json.dumps(man))
    S3 = seal.sealed_ids(trepo)
    check("seal(syn): loads 200", len(S3) == 200)
    sid = fake[17]
    for variant in (sid, " " + sid + " ", sid.upper(), sid[:-2] + "v9", sid[:-2],
                    "../papers/" + sid, sid + "/", "/abs/corpus/papers/" + sid):
        check(f"seal(syn): id variant {variant!r} refused",
              refused(seal.refuse_ids, ["0000.00001v1", variant], S3))
    check("seal(syn): unsealed ids pass", not refused(seal.refuse_ids, ["0000.00001v1"], S3))
    # artefacts
    s3 = trepo / "corpora/real_roots/results_sample3.json"
    s3.write_text(json.dumps({"frame": {"offset": 720}, "docs": [{"arxiv_id": sid}]}))
    (trepo / "innocuous.json").symlink_to(s3)
    # A sealed artefact with no ids and no frame (a boundary-scan-like file),
    # hard-linked under an innocent name: only its inode identifies it.
    bare = trepo / "corpora/oracle_baseline/strict_boundary_sample3.json"
    bare.write_text(json.dumps({"summary": {}}))
    os.link(bare, trepo / "plain.json")
    copy = trepo / "copy.json"
    copy.write_text(json.dumps({"docs": [{"arxiv_id": "0000.1v1"}, {"arxiv_id": sid}]}))
    off720 = trepo / "w.json"
    off720.write_text(json.dumps({"frame": {"offset": 720, "n": 200}, "docs": []}))
    named = trepo / "x.json"
    named.write_text(json.dumps({"sample": "sample 3 of the frame", "docs": []}))
    rowsart = trepo / "r.json"
    rowsart.write_text(json.dumps({"rows": [{"arxiv_id": sid.upper()}]}))
    for pth, why in ((s3, "by name"), (trepo / "innocuous.json", "via a symlink"),
                     (copy, "a renamed copy holding a sealed id"),
                     (off720, "frame offset 720"), (named, "records sample 3"),
                     (rowsart, "a `rows` artefact with a sealed id"),
                     (trepo / "plain.json", "a hard link with an innocent name"),
                     (trepo / "Results_Sample_03.json", "case/underscore/zero-padded name")):
        check(f"seal(syn): artefact refused {why}",
              refused(seal.refuse_artefact, pth, S3, trepo))
    ok = trepo / "ok.json"
    ok.write_text(json.dumps({"frame": {"offset": 0, "n": 200},
                              "docs": [{"arxiv_id": "0000.1v1"}]}))
    check("seal(syn): an unsealed artefact loads", not refused(seal.refuse_artefact, ok, S3, trepo))
    # The seal set itself: unreadable / short / wrong offset -> refuse everything.
    (trepo / seal.SEALED_MANIFEST).write_text(json.dumps(dict(man, docs=man["docs"][:199])))
    check("seal(syn): 199 sealed ids -> every request refused", refused(seal.sealed_ids, trepo))
    (trepo / seal.SEALED_MANIFEST).write_text(json.dumps(dict(man, frame={"offset": 0})))
    check("seal(syn): wrong recorded offset -> refused", refused(seal.sealed_ids, trepo))
    (trepo / seal.SEALED_MANIFEST).write_text("{not json")
    check("seal(syn): unreadable -> refused", refused(seal.sealed_ids, trepo))
    (trepo / seal.SEALED_MANIFEST).unlink()
    check("seal(syn): missing -> refused", refused(seal.sealed_ids, trepo))

# The producer refuses before it builds an oracle or reads the corpus, and has
# no option that disables the seal.
calls = []
_saved = _oracle.get_oracle
_oracle.get_oracle = lambda *a, **k: calls.append(1) or (_ for _ in ()).throw(
    RuntimeError("oracle built"))
try:
    for argv in (["record", "--sample", "3", "--corpus-root", "/nonexistent", "--out", "/x.json"],
                 ["record", "--sample", "03", "--corpus-root", "/nonexistent", "--out", "/x.json"],
                 ["record", "--sample", "1", "--corpus-root", "/nonexistent",
                  "--out", "/tmp/p2_sample3.json"]):
        rc, err = run_main(argv)
        check(f"producer: {argv[2]} {argv[-1]} refused by the seal (exit 3) before any oracle",
              rc == 3 and not calls and "REFUSED (sample-3 seal)" in err, (rc, err, calls))
finally:
    _oracle.get_oracle = _saved
src = (HERE / "p2_baseline.py").read_text()
check("producer: no option, flag or env var names the seal (no bypass)",
      not any(w in src for w in ("--allow", "--force", "--unseal", "--no-seal",
                                 "LP_P2_UNSEAL", "SEAL_OFF")))

# ── 9. the recorded grades still name current grading code ───────────────────
# The P2 extension must not change the blobs the recorded grades of samples 1-2
# name (_oracle.py 6b4ce94e, diff_real_roots.py 9859cccf on the base branch).
for rel in ("corpora/real_roots/results.json", "corpora/real_roots/results_sample2.json"):
    gc = json.loads((REPO / rel).read_text())["oracle"].get("grading_code")
    findings, _notes = _oracle.grading_code_drift(gc, REPO)
    check(f"grading code: {rel} still names this tree's grading code", not findings, findings)
for core in _oracle.GRADING_CODE_CORE:
    check(f"grading code: the P2 modules are not oracle core ({core})",
          not core.endswith(("_p2_diag.py", "_sample_seal.py", "p2_baseline.py")))

if count < MIN_CHECKS:
    fails += 1
    print(f"FAIL only {count} checks ran (floor {MIN_CHECKS}): the suite lost inputs")
print(f"[p2-diag] {count - fails}/{count} checks passed over {len(EXPECT)} recorded logs, "
      f"{len(CLS)} taxonomy messages, {len(ROWS)} scored rows")
sys.exit(1 if fails else 0)
