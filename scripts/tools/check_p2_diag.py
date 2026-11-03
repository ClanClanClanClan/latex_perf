#!/usr/bin/env python3
"""Unit and defeat tests of the P2 diagnostics baseline: the oracle-side
record (_p2_diag.diag_record), the CLI-side prediction (cli_prediction), the
pre-registered matching and metrics, the sample-3 seal (_sample_seal), and
the producer's refusals (p2_baseline.py). Pure: no docker, no TeX, no CLI;
it needs git (temporary repositories) and fetch-depth 0 (§10).

FIXTURES. corpora/p2_diag/fixtures/<case>/ holds a SYNTHETIC document (written
for this test, no corpus paper) and the main.log that pdfTeX
3.141592653-2.6-1.40.29 (TeX Live 2026) wrote for it with
`-interaction=nonstopmode -halt-on-error`, run on the LAPTOP TeX Live on
2026-11-03 -- NOT the oracle (ADR-012 decision 7). They test log PARSING
only. The eng_* cases are every package FEATURE_PACKAGES names (review H6).
Further SYNTHETIC logs are built inline (each marked); the review's
reproducers (~/.cache/lp-review-E/exp1-4.py, review of 758e0e18) are
restated here as defeat tests, labelled with the finding they defeat.

THE SEAL TESTS never touch a sample-3 document or output. They run against
SYNTHETIC repositories (git, in a temporary directory) whose "sealed" ids are
invented; against the real seal they assert only counts.

Exit 0 all checks pass; 1 a check failed. The last line prints the number of
checks run, floored, so an empty run cannot read as a pass.
"""
from __future__ import annotations

import io
import json
import os
import subprocess
import sys
import tempfile
import types
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import _oracle  # noqa: E402
import _p2_diag as d  # noqa: E402
import _sample_seal as seal  # noqa: E402
import diff_real_roots  # noqa: E402
import p2_baseline  # noqa: E402

REPO = HERE.parent.parent
FIX = REPO / "corpora" / "p2_diag" / "fixtures"
MIN_CHECKS = 250
fails = count = 0


def check(name, cond, detail=""):
    global fails, count
    count += 1
    if not cond:
        fails += 1
        print(f"FAIL {name} {str(detail)[:400]}")


def fixture(case):
    root = FIX / case

    def rs(rel):
        f = root / rel
        return f.read_bytes() if f.is_file() else None
    return d.diag_record((root / "main.log").read_bytes(), read_source=rs,
                         in_tree=lambda n: (root / n).is_file())


def syn(log: bytes, files: dict):
    """A record of a SYNTHETIC log over in-memory files."""
    return d.diag_record(log, read_source=lambda rel: files.get(rel),
                         in_tree=lambda n: d.canon_path(n) in files)


def _msg(fn, *a):
    try:
        fn(*a)
    except Exception as e:  # noqa: BLE001
        return str(e)
    return ""


def refused(fn, *a, exc=seal.SealError):
    try:
        fn(*a)
    except exc:
        return True
    return False


# ── 1. the oracle-side record on recorded logs ───────────────────────────────
# case: (has_error, consistent, class, object, file, line, frame, author_file, verified)
SYS = ("system", "main.tex", None)
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
    # H6: every FEATURE_PACKAGES package, as pdfTeX reports it
    "eng_fontspec": (True, True, "engine-incompatible", "fontspec", None, 100) + SYS,
    "eng_polyglossia": (True, True, "engine-incompatible", "fontspec", None, 100) + SYS,
    "eng_unicode_math": (True, True, "engine-incompatible", "unicodemath", None, 40) + SYS,
    "eng_luacode": (True, True, "engine-incompatible", "luacode", None, 51) + SYS,
    "eng_luatexbase": (True, True, "engine-incompatible", "ltluatex", None, 55) + SYS,
    "eng_luatexja": (True, True, "engine-incompatible", "luatexjacore", None, 79) + SYS,
    "eng_xecjk": (True, True, "engine-incompatible", "xecjk", None, 44) + SYS,
    "eng_ctex": (True, True, "engine-incompatible", "ctex", None, 133) + SYS,
    # missing-file objects compare without the extension the author omitted
    "fig_missing_noext": (True, True, "missing-file", "nofig", "main.tex", 4, "document",
                          "main.tex", True),
    "fig_missing_pdf": (True, True, "missing-file", "nofig", "main.tex", 4, "document",
                        "main.tex", True),
    "input_missing_subdir": (True, True, "missing-file", "nosuch", "main.tex", 3, "document",
                             "main.tex", True),
    # L3: names with a space and with parentheses, as pdfTeX prints them
    "name_space": (True, True, "undefined-cs", "\\spaceundefined", "my file.tex", 2,
                   "document", "my file.tex", True),
    "name_paren": (True, True, "undefined-cs", "\\parenundefined", "fig(1).tex", 2,
                   "document", "fig(1).tex", True),
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
    if r["has_error"]:
        st = L.get("stack_stats") or {}
        check(f"record {case}: a real pdfTeX log has a certain stack (no suspect pop, "
              f"no underflow)", st.get("suspect_file_pops") == 0 and st.get("underflow") == 0, st)

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
r = fixture("long_line")
check("record: a 79-byte context line is not glued to the help text",
      "The control sequence" not in (r["first_error"]["l_after"] or ""),
      r["first_error"]["l_after"])
r = fixture("forged_message")
check("record: a \\message-forged `!` block makes the record inconsistent",
      r["consistent"] is False and "2 error blocks" in r["consistent_why"], r["consistent_why"])
r = fixture("deep_path_child")
check("record: a stack path wrapped at 79 bytes is un-wrapped",
      r["location"]["file_stack"][-1].endswith("child_file_name.tex"), r["location"]["file_stack"])
r = fixture("eng_polyglossia")
check("record (H6): polyglossia's error is raised by fontspec, and the message is read "
      "flat across the (pkg) continuation", "LuaTeX" in d.flat_message(
          r["first_error"]["message"]), r["first_error"]["message"])

# ── 1b. SYNTHETIC logs: the review's exp3 shapes and others ──────────────────
FATAL = b"!  ==> Fatal error occurred, no output PDF file produced!\n"
long_msg = b"Package foo Info: " + b"x" * (79 - 18)
assert len(long_msg) == 79
logA = (b"(./main.tex\n" + long_msg + b"\n! that was emphatic\n"
        b"! Undefined control sequence.\nl.3 \\foo\n        \n" + FATAL)
r = syn(logA, {"main.tex": b"a\nb\n\\foo\n"})
check("M2 (exp3 A): a wrapped continuation starting with `!` is not a block",
      len(d.error_blocks(d.log_lines(logA))) == 1, d.error_blocks(d.log_lines(logA)))
check("M2 (exp3 A): ... and the ambiguous wrap makes the record inconsistent (excluded)",
      r["consistent"] is False and "ambiguous" in r["consistent_why"], r["consistent_why"])
logB = b"(./main.tex\n! Undefined control sequence.\n)\nNo pages of output.\n"
r = syn(logB, {"main.tex": b"\\typeout{! Undefined control sequence.}\n"})
check("M2 (exp3 B): a `\\typeout`ed `!` with no fatal-error report is inconsistent",
      r["consistent"] is False and "no halt" in r["consistent_why"], r["consistent_why"])
logC = (b"(./main.tex (./sec.tex\nitem a)\n! LaTeX Error: \\begin{theorem} on input line 1 "
        b"ended by \\end{proof}.\n\nSee the LaTeX manual or LaTeX Companion for explanation.\n"
        b"Type  H <return>  for immediate help.\n ...                                     "
        b"         \n                                                  \nl.2 \\end{proof}\n"
        b"                \n" + FATAL)
r = syn(logC, {"main.tex": b"\\begin{proof}\n\\end{proof}\n\\input{sec}\n",
               "sec.tex": b"\\begin{theorem}\n\\end{proof}\n"})
check("M1 (exp3 C): a `)` in printed text that pops a file frame is a suspect pop",
      r["location"]["stack_stats"]["suspect_file_pops"] == 1, r["location"]["stack_stats"])
check("M1 (exp3 C): ... and the location is NOT certified",
      r["location"]["verified"] is False and "stack uncertain" in r["location"]["verify_why"],
      r["location"])
logT = (b"(./main.tex (./sec.tex)\n(./sec2.tex\n! Undefined control sequence.\nl.2 \\x\n"
        b"      \n" + FATAL)
r = syn(logT, {"main.tex": b"a\n\\x\n", "sec.tex": b"\n", "sec2.tex": b"b\n\\x\n"})
check("M1: a second opened tree file with the same context at l.N makes the location "
      "ambiguous (not certified)", r["location"]["verified"] is False
      and "ambiguous" in (r["location"]["verify_why"] or ""), r["location"])
r = syn(b"(./my file.tex\n! Undefined control sequence.\nl.1 \\foo\n        \n" + FATAL,
        {"my file.tex": b"\\foo\n"})
check("L3 (exp3 D): a file name with a space is parsed whole and certified",
      (r["location"]["file"], r["location"]["verified"]) == ("my file.tex", True), r["location"])
r = syn(b"(./my file.tex\n! Undefined control sequence.\nl.1 \\foo\n        \n" + FATAL, {})
check("L3: a spaced name the tree does not have stays unverified, counted by reason",
      r["location"]["verified"] is False
      and d.unverified_reason(r["location"]["verify_why"]) == "file not in the tree", r["location"])
logF = (b"(./main.tex\n! LaTeX Error: File `x.sty' not found.\n)\n! Emergency stop.\n"
        b"<*> main.tex\n          \n*** (job aborted, no legal \\end found)\n\n" + FATAL)
r = syn(logF, {"main.tex": b"\\typeout{! LaTeX Error: File `x.sty' not found.}\n"})
check("exp3 F: a forged missing-file line before an unrelated Emergency stop is inconsistent",
      r["consistent"] is False, r["consistent_why"])
SYN_PAREN = (b"(./main.tex\n"
             b"Missing character: There is no ( in font cmr10!\n"
             b"Overfull \\hbox (3.0pt too wide) in paragraph at lines 4--5\n"
             b"[]\\OT1/cmr/m/n/10 (unbalanced text in the box dump\n"
             b"\n"
             b"(./sec.tex) (./sec2.tex [1{/usr/x/pdftex.map}]\n"
             b"! Undefined control sequence.\n"
             b"l.2 \\foo\n"
             b"        \n" + FATAL)
r = d.diag_record(SYN_PAREN, in_tree=lambda n: d.canon_path(n) in {"main.tex", "sec.tex",
                                                                    "sec2.tex"})
check("stack: box dumps / missing-character lines are skipped; page markers are clean",
      r["location"]["file_stack"] == ["./main.tex", "./sec2.tex"]
      and r["location"]["stack_stats"]["suspect_file_pops"] == 0, r["location"])
r = d.diag_record(b"(./main.tex)) extra close\n! Undefined control sequence.\nl.1 \\x\n"
                  b"      \n" + FATAL)
check("stack: an underflow is counted, not hidden",
      r["location"]["stack_stats"]["underflow"] == 1 and r["location"]["frame"] == "none",
      r["location"])
check("record: no log -> no error", d.diag_record(None)["has_error"] is False)
check("record: a log with no `!` line -> no error",
      d.diag_record(b"(./main.tex)\nNo pages of output.\n")["has_error"] is False)
check("record: the final-report line alone is not an error block",
      d.diag_record(FATAL)["has_error"] is False)
check("record: the module reuses the oracle's line model (one implementation)",
      d._unwrap_log is _oracle._unwrap_log)
r = d.diag_record(b"(/lp/run/sec/a.tex\n! Undefined control sequence.\nl.1 \\x\n      \n" + FATAL,
                  read_source=lambda rel: b"\\x\n" if rel == "sec/a.tex" else None,
                  work_prefixes=(_oracle.RUN_DIR, "/tmp/w"))
check("L2/H7: a stack entry under the container's RUN_DIR is in the tree",
      (r["location"]["file"], r["location"]["verified"]) == ("sec/a.tex", True), r["location"])
check("p2_baseline.RUN_DIR is the oracle's", p2_baseline.RUN_DIR == _oracle.RUN_DIR)

# ── 2. canon_path: one normalisation, both sides (H7) ────────────────────────
CANON = [("main.tex", (), "main.tex"), ("./main.tex", (), "main.tex"),
         ("././/main.tex", (), "main.tex"), ("sec/../main.tex", (), "main.tex"),
         ("../main.tex", (), None), ("/main.tex", (), None), (".main.tex", (), ".main.tex"),
         ("./../x.tex", (), None), ("", (), None), (None, (), None), ("a\x00b", (), None),
         ("/tmp/w/sec/a.tex", ("/tmp/w",), "sec/a.tex"), ("/tmp/w", ("/tmp/w",), None),
         ("/tmp/wx/a.tex", ("/tmp/w",), None), ("/lp/run/a.tex", ("/lp/run",), "a.tex"),
         ("/tmp/w/../etc/passwd", ("/tmp/w",), None),
         ("/usr/local/texlive/2026/texmf-dist/tex/latex/base/article.cls", (), None)]
for p, roots, want in CANON:
    check(f"canon_path({p!r}, {roots})", d.canon_path(p, roots) == want, d.canon_path(p, roots))
G = {"file": "main.tex", "line": 3}
for f, want in (("../main.tex", False), ("/main.tex", False), (".main.tex", False),
                ("././/main.tex", True), ("main.tex", True)):
    check(f"H7 (exp1 lstrip): location_correct file {f!r} -> {want}",
          d.location_correct({"file": f, "line": 3}, G) is want)
check("H7: a None gold file never matches", not d.location_correct({"file": "a.tex", "line": 1},
                                                                    {"file": None, "line": 1}))
check("H7: a bool line is not a line", not d.location_correct({"file": "main.tex", "line": True},
                                                              {"file": "main.tex", "line": 1}))

# ── 3. source-line verification ──────────────────────────────────────────────
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

# ── 4. the cause taxonomy ────────────────────────────────────────────────────
CLS = [
    ("! LaTeX Error: File `foo.sty' not found.", "missing-file", "foo"),
    ("! I can't find file `sec/intro'.", "missing-file", "intro"),
    ("! Package pdftex.def Error: File `fig-eps-converted-to.pdf' not found: using draft "
     "setting.", "missing-file", "fig-eps-converted-to"),
    ("! Undefined control sequence.", "undefined-cs", None),
    ("! LaTeX Error: Command \\iint already defined.", "command-already-defined", "\\iint"),
    ("! LaTeX Error: Environment proofx undefined.", "undefined-env", "proofx"),
    ("! LaTeX Error: \\begin{itemize} on input line 4 ended by \\end{enumerate}.",
     "env-mismatch", "itemize"),
    ("! LaTeX Error: Missing \\begin{document}.", "missing-begin-document", None),
    ("! LaTeX Error: Option clash for package xcolor.", "option-clash", "xcolor"),
    ("! Package inputenc Error: Invalid UTF-8 byte \"E9.", "encoding", None),
    ("! LaTeX Error: Unicode character Π (U+03A0)", "encoding", None),
    ("! Fatal Package fontspec Error: The fontspec package requires either XeTeX or\n"
     "(fontspec)                      LuaTeX.", "engine-incompatible", "fontspec"),
    ("! Critical Package xeCJK Error: The xeCJK package requires XeTeX to function.",
     "engine-incompatible", "xecjk"),
    ("! Package unicode-math Error: Cannot be run with pdftex!\n"
     "(unicode-math)                Use XeLaTeX or LuaLaTeX instead.",
     "engine-incompatible", "unicodemath"),
    ("! Package luatexja-core Error: This package requires Lua(HB)(La)TeX.",
     "engine-incompatible", "luatexjacore"),
    ("! Critical Package ctex Error: CTeX fontset `mac' is unavailable in current\n"
     "(ctex)                         mode.", "engine-incompatible", "ctex"),
    ("! Missing } inserted.", "brace-imbalance", None),
    ("! Paragraph ended before \\@tempa was complete.", "brace-imbalance", None),
    ("! Missing \\right. inserted.", "left-right-imbalance", None),
    ("! Double superscript.", "math-mode", None),
    ("! Misplaced alignment tab character &.", "alignment", None),
    ("! TeX capacity exceeded, sorry [grouping levels=255].", "tex-capacity", None),
    ("! Package cleveref Error: cleveref must be loaded after hyperref!.", "package-error",
     "cleveref"),
    ("! Critical Package foo Error: something else.", "package-error", "foo"),
    ("! Package pdftex.def Error: Something unrelated.", "package-error", "pdftex.def"),
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
# H6, the class: every FEATURE_PACKAGES feature's T3 prediction matches the
# gold of pdfTeX's real output for every package it names that has a fixture,
# and every feature has at least one.
FEATURE_FIXTURES = {"opentype_fonts": ["eng_fontspec"], "unicode_math": ["eng_unicode_math"],
                    "polyglossia": ["eng_polyglossia"],
                    "lua_scripting": ["eng_luacode", "eng_luatexbase"],
                    "japanese_cjk": ["eng_xecjk", "eng_luatexja", "eng_ctex"]}
check("H6: every FEATURE_PACKAGES feature has a recorded pdfTeX fixture",
      set(FEATURE_FIXTURES) == set(d.FEATURE_PACKAGES))
for feat, cases in FEATURE_FIXTURES.items():
    pred = d.cli_prediction(f"NOT-READY\tmain.tex\n  T3 profile incompatible: feature {feat} "
                            f"not supported by profile pdflatex\n")["predictions"][0]
    for case in cases:
        g = fixture(case)["cause"]
        check(f"H6: T3 {feat} is cause-correct against pdfTeX's real error in {case}",
              d.cause_correct(pred, g), (pred.get("object_set"), g))

# ── 5. the CLI-side prediction ───────────────────────────────────────────────
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
FOREIGN = ("  T0 LP-Foreign construct(s) in {f} (outside every supported tier; not a parse "
           "failure): \\catcode direct mutation detected; LP-Foreign (line 3)\n")
p = d.cli_prediction(MODEL_OK + "NOT-READY\tmain.tex\n" + FOREIGN.format(f="main.tex"))
x = p["predictions"][0]
check("cli: an LP-Foreign reason is a located claim with no cause class",
      (x["code"], x["class"], x["file"], x["line"]) == ("T0", None, "main.tex", 3), x)
W = "/private/tmp/lp-oracle-ab/w"
p = d.cli_prediction(MODEL_OK + f"NOT-READY\t{W}/main.tex\n" + FOREIGN.format(f=f"{W}/main.tex"),
                     "", (W,))
x = p["predictions"][0]
check("H7 (exp1): an absolute path under the CLI's run directory is canonicalised and "
      "matches gold", x["file"] == "main.tex" and d.location_correct(x, G), x)
p = d.cli_prediction(MODEL_OK + "NOT-READY\tx\n" + FOREIGN.format(f="/etc/main.tex"), "", (W,))
check("H7: a claimed path outside the run is None (never matches)",
      p["predictions"][0]["file"] is None and p["predictions"][0]["file_raw"] == "/etc/main.tex")
p = d.cli_prediction(MODEL_OK + "NOT-READY\t/p/main.tex\n"
                     "  T2 project not closed: missing file sec/fig.tex\n")
x = p["predictions"][0]
check("cli: T2 missing file -> missing-file, object by basename",
      (x["class"], x["object"], x["file"]) == ("missing-file", "fig", None), x)
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
check("L4: artefact-fatal names its file and NO class (the gold taxonomy has none)",
      (p["predictions"][0]["class"], p["predictions"][0]["file"], p["predictions"][0]["code"])
      == (None, "main.aux", "artefact"), p["predictions"][0])
# L4, the class: every class a prediction can name is a gold class, so no
# prediction is unscorable by construction.
pred_classes = set(d.T5_CLASS.values()) | {"missing-file", "engine-incompatible"}
for line in ("  T5 rule violations: [" + "; ".join(sorted(d.T5_CLASS)) + "]",
             "  structural-fatal (will not compile): [a: ! Double superscript; b: ! LaTeX "
             "Error: Missing \\begin{document}.; c: ! Undefined control sequence]",
             "  artefact-fatal (main.aux): bad", "  T2 project not closed: missing file x.tex",
             "  T3 profile incompatible: feature opentype_fonts not supported by profile p"):
    for x in d.cli_prediction("NOT-READY\tm.tex\n" + line + "\n")["predictions"]:
        if x["class"]:
            pred_classes.add(x["class"])
check("L4: every class a prediction can name is in the gold taxonomy",
      pred_classes <= set(d.CLASSES), pred_classes - set(d.CLASSES))
# L6: the printed order, and no prediction from a CERTIFIED model
REJ = ("MODEL-CONNECTED\tPREMISE-REJECTED\ttier=lp-core\ta compilability-bearing obligation "
       "failed\n  T3 body-required feature(s) [unicode_math] not admitted by engine pdflatex\n")
p = d.cli_prediction(REJ + "NOT-READY\t/p/main.tex\n  T5 rule violations: [DELIM-001]\n"
                     "  (model-connected checks also reject; see above)\n")
check("L6: predictions follow the CLI's printed order (MODEL-CONNECTED first), and top-1 is "
      "the first printed", [x["code"] for x in p["predictions"]] == ["T3", "DELIM-001"],
      p["predictions"])
p = d.cli_prediction(MODEL_OK + "  T3 body-required feature(s) [unicode_math] not admitted\n"
                     "NOT-READY\t/p/main.tex\n  T5 rule violations: [DELIM-001]\n")
check("L6: an indented line under a CERTIFIED model is not a prediction",
      [x["code"] for x in p["predictions"]] == ["DELIM-001"], p["predictions"])
p = d.cli_prediction(REJ + "READY\t/p/main.tex\n")
check("L6: a READY answer predicts nothing", p["predictions"] == [], p)
check("cli: T5 classes only name compile-blocking rules",
      set(d.T5_CLASS) <= set(f"DELIM-{i:03d}" for i in range(1, 12))
      | set(f"ENC-{i:03d}" for i in range(1, 25)))

# ── 6. matching ──────────────────────────────────────────────────────────────
GM = {"class": "missing-file", "object": "fig"}
check("match: class and object", d.cause_correct({"class": "missing-file", "object": "fig"}, GM))
check("match: object differs", not d.cause_correct({"class": "missing-file", "object": "x"}, GM))
check("match: class differs", not d.cause_correct({"class": "encoding", "object": None}, GM))
check("match: no class never matches", not d.cause_correct({"class": None}, GM))
check("match (L): a graphic named with and without its extension is one object",
      d.norm_object("missing-file", "fig.pdf") == d.norm_object("missing-file", "fig"))
GL = {"file": "sec/a.tex", "line": 7}
check("loc: exact", d.location_correct({"file": "./sec/a.tex", "line": 7}, GL))
check("loc: off by one is wrong", not d.location_correct({"file": "sec/a.tex", "line": 8}, GL))
check("loc: other file", not d.location_correct({"file": "a.tex", "line": 7}, GL))
check("loc: file level", d.location_correct({"file": "sec/a.tex", "line": None}, GL, "file"))
check("loc: no line is not line-correct",
      not d.location_correct({"file": "sec/a.tex", "line": None}, GL))

# ── 7. bounds and metrics ────────────────────────────────────────────────────
lo, hi = d.clopper_pearson(0, 28)
check("cp: 0/28 upper = 1 - 0.05^(1/28)", abs(hi - (1 - 0.05 ** (1 / 28))) < 1e-6, hi)
lo, hi = d.clopper_pearson(28, 28)
check("cp: 28/28 lower = 0.05^(1/28)", abs(lo - 0.05 ** (1 / 28)) < 1e-6, lo)
lo, hi = d.clopper_pearson(5, 10)
check("cp: 5/10 is symmetric", abs(lo - (1 - hi)) < 1e-6 and abs(lo - 0.2224) < 1e-3, (lo, hi))
check("cp: n = 0 has no bound", d.clopper_pearson(0, 0) == (None, None))
for n_big in (1030, 5000):
    try:
        lo0, hi0 = d.clopper_pearson(0, n_big)
        lo1, hi1 = d.clopper_pearson(n_big, n_big)
        lom, him = d.clopper_pearson(n_big // 2, n_big)
        ok = (abs(hi0 - (1 - 0.05 ** (1 / n_big))) < 1e-9 and abs(lo1 - 0.05 ** (1 / n_big)) < 1e-9
              and abs(lom - (1 - him)) < 1e-9 and lom < 0.5 < him)
    except (OverflowError, ValueError) as e:
        ok = repr(e)
    check(f"L5: clopper_pearson is stable at n = {n_big}", ok is True, ok)


def gold(cls, obj, file, line, verified=True, consistent=True):
    return {"has_error": True, "consistent": consistent, "cause": {"class": cls, "object": obj},
            "location": {"file": file, "line": line, "verified": verified}}


def pred(verdict, *ps):
    return {"verdict": verdict, "predictions": list(ps)}


NOGOLD = {"has_error": False}
ROWS = [
    {"graded": True, "agrees_with_record": True, "compiles": False,
     "gold": gold("missing-file", "fig", "main.tex", 4),
     "pred": pred("NOT-READY", {"class": "missing-file", "object": "fig", "file": "main.tex",
                                "line": 4})},
    {"graded": True, "agrees_with_record": True, "compiles": False,
     "gold": gold("brace-imbalance", None, "main.tex", 9),
     "pred": pred("NOT-READY", {"class": "encoding"}, {"class": "brace-imbalance"})},
    {"graded": True, "agrees_with_record": True, "compiles": False,
     "gold": gold("undefined-cs", "\\x", "main.tex", 2), "pred": pred("READY")},
    {"graded": True, "agrees_with_record": True, "compiles": False,
     "gold": gold("undefined-cs", "\\y", "main.tex", 3, verified=False),
     "pred": pred("NOT-READY", {"class": None, "file": "main.tex", "line": 3})},
    {"graded": True, "agrees_with_record": True, "compiles": False,
     "gold": gold("other", None, "main.tex", 1, consistent=False),
     "pred": pred("NOT-READY", {"class": None})},
    {"graded": True, "agrees_with_record": True, "compiles": True, "gold": NOGOLD,
     "pred": pred("NOT-READY", {"class": "encoding", "file": "main.tex", "line": 1})},
    {"graded": True, "agrees_with_record": False, "compiles": False, "gold": NOGOLD,
     "pred": pred("READY")},
    {"graded": False, "gold": NOGOLD, "pred": pred("TIMEOUT")},
]
S = d.score_rows(ROWS)
check("score: inputs", S["inputs"] == {"rows": 8, "fails": 5, "compiles": 1, "cause_scored": 4,
                                       "location_scored": 3, "cause_line_labelled": 0},
      S["inputs"])
check("score: exclusions are counted",
      (S["excluded"]["ungraded"], S["excluded"]["disagrees_with_record"],
       S["excluded"]["cause_inconsistent"], S["excluded"]["location_unverified"]) == (1, 1, 1, 1),
      S["excluded"])
check("score: cause recall top-1 1/4", (S["cause_recall_top1"]["k"], S["cause_recall_top1"]["n"])
      == (1, 4), S["cause_recall_top1"])
check("score: cause precision counts a cause named on a compiling document as wrong",
      (S["cause_precision_top1_heuristic"]["k"], S["cause_precision_top1_heuristic"]["n"])
      == (1, 3), S["cause_precision_top1_heuristic"])
check("score: location precision 1/2", (S["location_precision_line_heuristic"]["k"],
                                        S["location_precision_line_heuristic"]["n"]) == (1, 2))
check("R4: with no certified claim the certified channel is empty (n = 0, no defect)",
      S["cause_precision_top1_certified"]["n"] == 0 and S["location_precision_line_certified"]["n"]
      == 0 and S["soundness"]["certified_claims"] == 0, S["soundness"])
check("score: location recall 1/3", (S["location_recall_line"]["k"],
                                     S["location_recall_line"]["n"]) == (1, 3))
check("M3(d): the gameable any-of recall is not a metric", "cause_recall_any" not in S)
check("L3: unverified locations are counted by reason",
      S.get("location_unverified_by_reason") == {"unknown": 1},
      S.get("location_unverified_by_reason"))
shot = [{"graded": True, "agrees_with_record": True, "compiles": False,
         "gold": gold("missing-file", "fig", "main.tex", 4),
         "pred": pred("NOT-READY", {"class": None}, *[{"class": c} for c in d.CLASSES])}] * 30
SS = d.score_rows(shot)
check("M3(d) (exp2 shotgun): listing every class after a classless first scores 0 recall",
      SS["cause_recall_top1"]["k"] == 0 and SS["cause_precision_top1_heuristic"]["n"] == 0, SS)

# ── 8. the pre-registration (committed document) ─────────────────────────────
PRE = REPO / p2_baseline.PREREG
block = p2_baseline.read_lines_block(PRE)
check("prereg: the lines block names this code's definitions version",
      block.get("definitions") == d.DEFINITIONS_VERSION, block.get("definitions"))
check("prereg: the committed lines are PROPOSED, not FIXED (nothing is scored yet)",
      block.get("status") == "PROPOSED", block.get("status"))
check("prereg: every line names a known metric and stat",
      all((ln["metric"] in S or ln["metric"].split(".", 1)[0] in ("inputs", "excluded"))
          and ln["stat"] in ("k", "n", "point", "lower95", "upper95") for ln in block["lines"]),
      [ln.get("id") for ln in block["lines"]])
check("prereg (R4): every success line has the floor min_n >= 29",
      all((ln.get("min_n") or 0) >= 29 for ln in block["lines"] if ln["kind"] == "success")
      and sum(1 for ln in block["lines"] if ln["kind"] == "success") >= 7,
      [(ln["id"], ln.get("min_n")) for ln in block["lines"] if ln["kind"] == "success"])
check("prereg (R4): certified precision lines demand exactly 1.0; heuristic >= 0.95; "
      "heuristic kills < 0.90; no certified kill line",
      all(ln["op"] == "==" and ln["value"] == 1.0 for ln in block["lines"]
          if ln["kind"] == "success" and ln["metric"].endswith("_certified"))
      and all(ln["op"] == ">=" and ln["value"] == 0.95 for ln in block["lines"]
              if ln["kind"] == "success" and "precision" in ln["metric"]
              and ln["metric"].endswith("_heuristic"))
      and all(ln["op"] == "<" and ln["value"] == 0.90 and ln["metric"].endswith("_heuristic")
              for ln in block["lines"] if ln["kind"] == "kill")
      and {ln["metric"] for ln in block["lines"] if ln["kind"] == "kill"}
      == {"location_precision_line_heuristic", "cause_precision_top1_heuristic",
          "location_precision_cause_heuristic"})
check("prereg (R4): recall targets kept (location >= 0.50, cause >= 0.80) and the baseline "
      "predicted at zero", {(ln["metric"], ln["op"], ln["value"]) for ln in block["lines"]
                             if ln["id"] in ("S2", "S4", "P1")}
      == {("location_recall_line", ">=", 0.5), ("cause_recall_top1", ">=", 0.8),
          ("location_recall_line", "<=", 0.1)})
check("prereg: the lines block is still PROPOSED and names p2-defs/4",
      block["status"] == "PROPOSED" and block["definitions"] == "p2-defs/4")
check("prereg (provenance): both owner messages are quoted verbatim",
      all(q in PRE.read_text() for q in (
          '"What are the answers leading to the best product for the orginal vision? Ultrathink"',
          '"Yes to run docker builder prune and listing the images. And I asked best '
          'recommendations for perfect project concerning your other two questions"')))
check("prereg (H5/M3b): V0 floors record-time exclusions; V6/V7 floor the cause and "
      "location sets", {"V0", "V6", "V7"} <= {ln["id"] for ln in block["lines"]})
check("prereg: the document states the definitions version in prose",
      d.DEFINITIONS_VERSION in PRE.read_text())

# ── 9. the seal and the producer, on SYNTHETIC repositories ──────────────────


def git(repo, *a):
    r = subprocess.run(["git", *a], cwd=repo, capture_output=True)
    assert r.returncode == 0, (a, r.stderr)
    return r.stdout.decode().strip()


SEALED_FAKE = [f"9999.{i:05d}v1" for i in range(200)]
S1_FAKE = [f"0001.{i:05d}v1" for i in range(200)]
S2_FAKE = [f"0002.{i:05d}v2" for i in range(200)]
SID = SEALED_FAKE[17]
HELDOUT_FAKE = [f"9998.{i:05d}v1" for i in range(1080)]
HID = HELDOUT_FAKE[500]


def commit_all(repo):
    git(repo, "-c", "user.email=t@t", "-c", "user.name=t", "add", "-A")
    git(repo, "-c", "user.email=t@t", "-c", "user.name=t", "-c", "commit.gpgsign=false", "commit", "-qm", "c")


def make_repo(td: Path, *, prereg_status="PROPOSED", s1=None) -> Path:
    """A SYNTHETIC git repo: a sealed manifest of invented ids, two grades of
    record of invented ids, the pre-registration (status as given)."""
    repo = td / "repo"
    (repo / "corpora/real_roots").mkdir(parents=True)
    (repo / "docs/v27/product").mkdir(parents=True)
    (repo / seal.SEALED_MANIFEST).write_text(json.dumps(
        {"frame": {"offset": 720, "n": 200}, "docs": [{"arxiv_id": x} for x in SEALED_FAKE]}))
    (repo / seal.HELDOUT_MANIFEST).write_text(json.dumps(
        {"frame": {"offset": 920, "n": 1080}, "docs": [{"arxiv_id": x} for x in HELDOUT_FAKE]}))
    for rel, ids in ((seal.ALLOWED[1][2], s1 or S1_FAKE), (seal.ALLOWED[2][2], S2_FAKE)):
        (repo / rel).write_text(json.dumps({"docs": [
            {"arxiv_id": x, "toplevel": "main.tex", "sha256_tree": "0" * 64, "pdflatex_rc": 1,
             "pdflatex_pdf": False, "cli_rc": 1} for x in ids]}))
    blk = dict(block, status=prereg_status)
    (repo / p2_baseline.PREREG).write_text(
        f"x\n{p2_baseline.LINES_BEGIN}\n```json\n{json.dumps(blk)}\n```\n{p2_baseline.LINES_END}\n")
    git(repo, "init", "-q")
    commit_all(repo)
    return repo


def run_main(argv, repo):
    out, err = io.StringIO(), io.StringIO()
    saved_repo = p2_baseline.REPO
    p2_baseline.REPO = repo
    try:
        with redirect_stdout(out), redirect_stderr(err):
            rc = p2_baseline.main(argv)
    except SystemExit as e:
        rc = ("SystemExit", e.code)
    finally:
        p2_baseline.REPO = saved_repo
    return rc, err.getvalue() + out.getvalue()


# 9a. ids: strict allow-list, never normalised (H1b; exp1's variants)
SEALED_KEYS = frozenset(seal.paper_key(x) for x in SEALED_FAKE)
for v in (SID, SID + "/.", SID + "/./", SID + "\u200b", SID + ".", "\uff19999.00017v1",
          SID + "\t/.", SID + "v1", SID.replace(".", "\u2024"), SID + "/x/..", SID[:-2] + "V1",
          SID[:-2] + "v9", SID[:-2], " " + SID, "../papers/" + SID, None, 9999.00017, ""):
    check(f"H1b: id {v!r} refused against the sealed set",
          refused(seal.refuse_ids, ["0001.00001v1", v], SEALED_KEYS))
check("H1b: a valid unsealed id passes", not refused(seal.refuse_ids, ["0001.00001v1"],
                                                     SEALED_KEYS))
for k in (3, "3", " 3", "03", 3.0, True, False, 0, 4, None, "1 ", "sample3", [1], "\uff11",
          "\uff12", " 2", "2\n", 1.0):
    check(f"seal: sample number {k!r} refused", refused(seal.sample_spec, k))
for k in (1, 2, "1", "2"):
    check(f"seal: sample number {k!r} allowed", not refused(seal.sample_spec, k))
for off, n in ((720, 200), (719, 2), (919, 1), (900, 1000), (0, 721), (700, 21),
               (720, 0), (-1, 5), (1000, -300), (720.0, 200), ("720", 200), (True, 200)):
    check(f"seal: window ({off!r}, {n!r}) refused", refused(seal.refuse_window, off, n))
for off, n in ((0, 200), (200, 200), (0, 720), (2000, 10), (400, 320)):
    check(f"seal: window ({off}, {n}) allowed", not refused(seal.refuse_window, off, n))
for nm in ("results_sample3.json", "results_sample 3.json", "results-sample\uff13.json",
           "results_s3.json", "Results_Sample_03.json", "x_SAMPLE3.json"):
    check(f"seal: name belt refuses {nm!r}", refused(seal.refuse_name, nm))
for nm in ("diag_sample1.json", "diag_sample2.json", "score.json", "results_sample2.json"):
    check(f"seal: name belt allows {nm!r}", not refused(seal.refuse_name, nm))

with tempfile.TemporaryDirectory() as td:
    repo = make_repo(Path(td))
    S3 = seal.sealed_ids(repo)
    check("seal(syn): the committed seals load 200 + 1,080 keys", len(S3) == 1280)
    docs, rel, blob = seal.sample_docs(repo, 1, S3)
    check("seal(syn): sample 1's docs come from HEAD with their blob",
          len(docs) == 200 and rel == seal.ALLOWED[1][2] and len(blob) == 40)
    m = repo / seal.SEALED_MANIFEST
    orig = m.read_text()
    m.write_text(orig.replace(SID, "0003.00001v1"))
    check("H1a: an edited (uncommitted) seal manifest refuses everything",
          refused(seal.sealed_ids, repo))
    m.write_text(orig)
    g1 = repo / seal.ALLOWED[1][2]
    orig1 = g1.read_text()
    g1.write_text(orig1.replace(S1_FAKE[5], SID))
    check("H1a: a working-tree grade of record that differs from HEAD is refused",
          refused(seal.sample_docs, repo, 1, S3))
    g1.write_text(orig1)
    check("seal(syn): restored inputs load again", not refused(seal.sample_docs, repo, 1, S3))

for label, ids in (("an exact sealed id", S1_FAKE[:199] + [SID]),
                   ("another version of a sealed paper", S1_FAKE[:199] + [SID[:-2] + "v7"]),
                   ("`SID/.`", S1_FAKE[:199] + [SID + "/."]),
                   ("a zero-width-suffixed sealed id", S1_FAKE[:199] + [SID + "\u200b"]),
                   ("a duplicated paper", S1_FAKE[:199] + [S1_FAKE[0][:-2] + "v3"]),
                   ("199 rows", S1_FAKE[:199])):
    with tempfile.TemporaryDirectory() as td:
        repo = make_repo(Path(td), s1=ids)
        check(f"H1: a COMMITTED grade of record with {label} is refused",
              refused(seal.sample_docs, repo, 1, seal.sealed_ids(repo)))

for label, key, val in (("199 sealed ids", "docs", None), ("a wrong offset", "frame", None),
                        ("an invalid sealed id", "id", None)):
    with tempfile.TemporaryDirectory() as td:
        repo = make_repo(Path(td))
        m = repo / seal.SEALED_MANIFEST
        dd = json.loads(m.read_text())
        if key == "docs":
            dd["docs"] = dd["docs"][:199]
        elif key == "frame":
            dd["frame"] = {"offset": 0}
        else:
            dd["docs"][0]["arxiv_id"] = "x"
        m.write_text(json.dumps(dd))
        commit_all(repo)
        check(f"seal(syn): a committed seal with {label} refuses everything",
              refused(seal.sealed_ids, repo))
with tempfile.TemporaryDirectory() as td:
    repo = make_repo(Path(td))
    git(repo, "rm", "-q", "--cached", seal.SEALED_MANIFEST)
    git(repo, "-c", "user.email=t@t", "-c", "user.name=t", "-c", "commit.gpgsign=false",
        "commit", "-qm", "untrack")
    check("seal(syn): an untracked seal manifest refuses everything",
          refused(seal.sealed_ids, repo))

# 9a'. rulings R2 and R3: sample 3 by ruling, and the P2 held-out set
check("R2: the sample refusal cites ruling R2 (no longer a pending default)",
      refused(seal.sample_spec, 3) and "ruling R2" in str(
          next((e for e in [None] if False), None) or _msg(seal.sample_spec, 3)))
for off, n in ((920, 1), (1999, 1), (1500, 10), (900, 30), (0, 2719), (1990, 100)):
    check(f"R3: window ({off}, {n}) meets the held-out set and is refused",
          refused(seal.refuse_window, off, n))
for off, n in ((2000, 10), (2000, 719)):
    check(f"R3: window ({off}, {n}) after the held-out set is allowed",
          not refused(seal.refuse_window, off, n))
with tempfile.TemporaryDirectory() as td:
    repo = make_repo(Path(td))
    keys = seal.sealed_ids(repo)
    check("R3(syn): the sealed set is sample 3 plus the held-out set (1,280 keys)",
          len(keys) == 1280 and seal.paper_key(HID) in keys and seal.paper_key(SID) in keys)
    for v in (HID, HID[:-2] + "v3"):
        check(f"R3(syn): held-out id {v!r} refused", refused(seal.refuse_ids, [v], keys))
    m = repo / seal.HELDOUT_MANIFEST
    orig = m.read_text()
    m.write_text(orig.replace(HID, "0003.00002v1"))
    check("R3(syn): an edited (uncommitted) held-out manifest refuses everything",
          refused(seal.sealed_ids, repo))
    m.write_text(orig)
for label, mut in (("1,079 ids", lambda dd: dd.update(docs=dd["docs"][:1079])),
                   ("offset 900", lambda dd: dd.update(frame={"offset": 900, "n": 1080})),
                   ("n recorded as 1000", lambda dd: dd.update(frame={"offset": 920, "n": 1000})),
                   ("an id shared with sample 3", lambda dd: dd["docs"][0].update(arxiv_id=SID))):
    with tempfile.TemporaryDirectory() as td:
        repo = make_repo(Path(td))
        m = repo / seal.HELDOUT_MANIFEST
        dd = json.loads(m.read_text())
        mut(dd)
        m.write_text(json.dumps(dd))
        commit_all(repo)
        check(f"R3(syn): a committed held-out manifest with {label} refuses everything",
              refused(seal.sealed_ids, repo))
with tempfile.TemporaryDirectory() as td:
    repo = make_repo(Path(td), s1=S1_FAKE[:199] + [HID])
    check("R3(syn): a grade of record holding a held-out id is refused",
          refused(seal.sample_docs, repo, 1, seal.sealed_ids(repo)))
with tempfile.TemporaryDirectory() as td:
    repo = make_repo(Path(td))
    (repo / seal.HELDOUT_MANIFEST).unlink()
    commit_all(repo)
    check("R3(syn): a missing held-out manifest refuses everything", refused(seal.sealed_ids, repo))
for nm in ("manifest_p2_heldout.json", "x-held-out.json", "HELD_OUT_run.json"):
    check(f"R3: name belt refuses {nm!r}", refused(seal.refuse_name, nm))

# 9b. record, with a FAKE oracle (exp4): what reaches the engine
seen: list = []


class FakeOracle:
    def tempdir(self):
        return tempfile.TemporaryDirectory()

    def tex_env(self, td):
        return {}

    def provenance(self):
        return {}


class FakeStamp:
    def __init__(self, *a):
        self.head = "0" * 40

    def require(self):
        pass

    def oracle_block(self, o):
        return {}


def fake_run(work, top, env, timeout):
    pth = Path(work) / top
    seen.append(("ORACLE", str(pth), pth.read_text() if pth.is_file() else None))
    return types.SimpleNamespace(rc=1, passes=1, pdf=False)


def fake_cli(argv, cwd, timeout, env):
    pth = Path(cwd) / argv[-1]
    seen.append(("CLI", str(pth), pth.read_text() if pth.is_file() else None))
    return types.SimpleNamespace(returncode=1, stdout=b"NOT-READY\tmain.tex\n", stderr=b"")


saved = (_oracle.get_oracle, _oracle.RunStamp, diff_real_roots.run_to_fixpoint_full,
         p2_baseline.run_cli, p2_baseline.cli_provenance)
_oracle.get_oracle = lambda *a, **k: FakeOracle()
_oracle.RunStamp = FakeStamp
diff_real_roots.run_to_fixpoint_full = fake_run
p2_baseline.run_cli = fake_cli
p2_baseline.cli_provenance = lambda cli: {"path": "fake", "sha256": "0"}
try:
    with tempfile.TemporaryDirectory() as td:
        td = Path(td)
        corpus = td / "corpus"
        (corpus / SID).mkdir(parents=True)
        (corpus / SID / "main.tex").write_text("SYNTHETIC SEALED DOC\n")
        outside = td / "outside"
        outside.mkdir()
        (outside / "x.tex").write_text("OUTSIDE\n")
        tops = {S1_FAKE[0]: str(corpus / SID / "main.tex"), S1_FAKE[1]: f"../{SID}/main.tex",
                S1_FAKE[2]: "main.tex", S1_FAKE[3]: "main.tex", S1_FAKE[4]: "main.tex"}
        for x in S1_FAKE[:5]:
            (corpus / x).mkdir()
            (corpus / x / "main.tex").write_text("innocent\n")
        os.symlink(outside, corpus / S1_FAKE[2] / "s3")          # a symlinked directory
        os.symlink(corpus / SID, corpus / S1_FAKE[3] / "inner")   # a link to a sealed tree
        repo_t = make_repo(td)
        g1 = repo_t / seal.ALLOWED[1][2]
        dd = json.loads(g1.read_text())
        for row in dd["docs"]:
            row["toplevel"] = tops.get(row["arxiv_id"], "main.tex")
            row["sha256_tree"] = (diff_real_roots.sha256_tree(corpus / row["arxiv_id"])
                                  if (corpus / row["arxiv_id"]).is_dir() else "0" * 64)
        g1.write_text(json.dumps(dd))
        commit_all(repo_t)
        seen.clear()
        rc, out = run_main(["record", "--sample", "1", "--corpus-root", str(corpus),
                            "--out", str(td / "rec.json"), "--cli", "fake"], repo_t)
        check("record (fake oracle) runs", rc == 0, (rc, out))
        check("H1c/M6 (exp4): no sealed or outside byte reaches the CLI or the engine",
              not any(s[2] and ("SEALED" in s[2] or "OUTSIDE" in s[2]) for s in seen), seen)
        check("record: the clean package is graded (CLI and engine both ran on it)",
              sum(1 for s in seen if s[2] == "innocent\n") == 2, seen)
        art = json.loads((td / "rec.json").read_text()) if rc == 0 else {"rows": []}
        why = {r["arxiv_id"]: r["excluded"] for r in art["rows"]}
        check("H1c: an absolute toplevel is excluded",
              why.get(S1_FAKE[0]) == "toplevel is absolute", why.get(S1_FAKE[0]))
        check("H1c: a `..` toplevel is excluded",
              why.get(S1_FAKE[1]) == "toplevel has a `..` component", why.get(S1_FAKE[1]))
        check("M6: a package with a symlinked directory is excluded (not hashed blind)",
              why.get(S1_FAKE[2]) == "symlink in the package tree", why.get(S1_FAKE[2]))
        check("M6: a link to a sealed tree inside a package is excluded",
              why.get(S1_FAKE[3]) == "symlink in the package tree", why.get(S1_FAKE[3]))
        check("record: rows missing from the corpus are excluded and counted",
              sum(1 for r in art["rows"] if r["excluded"] == "missing from the corpus") == 195,
              art.get("counts"))
        check("H1a: the record stamps the grade-of-record and seal blobs",
              art.get("grade_of_record", {}).get("blob") and art.get("seal_blob"))
        dd["docs"][10]["arxiv_id"] = SID + "/."
        g1.write_text(json.dumps(dd))
        seen.clear()
        rc, out = run_main(["record", "--sample", "1", "--corpus-root", str(corpus),
                            "--out", str(td / "rec2.json"), "--cli", "fake"], repo_t)
        check("H1a: record refuses a working-tree grade of record (exit 3), before any engine",
              rc == 3 and not seen, (rc, out))
        commit_all(repo_t)
        rc, out = run_main(["record", "--sample", "1", "--corpus-root", str(corpus),
                            "--out", str(td / "rec3.json"), "--cli", "fake"], repo_t)
        check("H1b: record refuses a committed `SID/.` id (exit 3), before any engine",
              rc == 3 and not seen, (rc, out))
        for argv in (["record", "--sample", "3"], ["record", "--sample", "03"],
                     ["record", "--sample", "1", "--out", str(td / "p2_sample3.json")]):
            full = argv + ["--corpus-root", str(corpus), "--cli", "fake"] + (
                [] if "--out" in argv else ["--out", str(td / "o.json")])
            rc, out = run_main(full, repo_t)
            check(f"seal: {' '.join(argv[1:3])} refused (exit 3) before any engine",
                  rc == 3 and not seen, (rc, out))
finally:
    (_oracle.get_oracle, _oracle.RunStamp, diff_real_roots.run_to_fixpoint_full,
     p2_baseline.run_cli, p2_baseline.cli_provenance) = saved

# 9c. score: committed inputs, exact samples, VOID, provenance (H2-H5, M3)


def rec_rows(ids, kind="hit"):
    rows = []
    for x in ids:
        p_ = ({"class": "missing-file", "object": "fig", "file": "main.tex", "line": 4}
              if kind == "hit" else {"class": None})
        rows.append({"arxiv_id": x, "graded": True, "agrees_with_record": True,
                     "compiles": False, "excluded": None,
                     "gold": gold("missing-file", "fig", "main.tex", 4),
                     "pred": pred("NOT-READY", p_)})
    return rows


def record_art(repo, k, rows=None):
    o_, n, rel = seal.sample_spec(k)
    return {"schema": d.SCHEMA, "definitions": d.DEFINITIONS_VERSION, "sample": k,
            "frame_window": {"offset": o_, "n": n},
            "grade_of_record": {"path": rel, "blob": seal.committed(repo, rel)[1]},
            "seal_blob": seal.seal_blob(repo),
            "rows": rows if rows is not None else rec_rows(S1_FAKE if k == 1 else S2_FAKE)}


def score_case(label, *, status="FIXED", arts=None, records=None, edit=None, expect_rc,
               expect_in=""):
    with tempfile.TemporaryDirectory() as td:
        repo = make_repo(Path(td), prereg_status=status)
        a1, a2 = record_art(repo, 1), record_art(repo, 2)
        arts_ = arts(a1, a2) if arts else {"rec1.json": a1, "rec2.json": a2}
        (repo / "corpora/p2_baseline").mkdir(exist_ok=True)
        for name, a in arts_.items():
            (repo / "corpora/p2_baseline" / name).write_text(json.dumps(a))
        commit_all(repo)
        if edit:
            edit(repo)
        recs = [str(repo / "corpora/p2_baseline" / x) for x in
                (records or ["rec1.json", "rec2.json"])]
        rc, out = run_main(["score", "--records", *recs, "--out", str(Path(td) / "s.json")], repo)
        sp = Path(td) / "s.json"
        res = json.loads(sp.read_text()) if sp.is_file() else None
        check(label, rc == expect_rc and expect_in in out, (rc, out[-300:]))
        return rc, res


rc, res = score_case("score: happy path on committed records and FIXED lines (rc 0)",
                     expect_rc=0)
if res:
    prov = res.get("provenance", {})
    check("H3: the output records HEAD, the prereg blob, the seal blob and each record's "
          "blob and sha256", prov.get("head") and prov.get("prereg", {}).get("blob")
          and prov.get("seal_blob") and len(prov.get("records", [])) == 2
          and all(r.get("blob") and r.get("sha256") for r in prov["records"]), prov)
    check("H4: n counts each document once", res["inputs"]["fails"] == 400, res["inputs"])
score_case("H3: PROPOSED lines at HEAD are refused", status="PROPOSED", expect_rc=2,
           expect_in="not 'FIXED'")


def edit_prereg_fixed(repo):
    p_ = repo / p2_baseline.PREREG
    p_.write_text(p_.read_text().replace('"PROPOSED"', '"FIXED"'))


score_case("H3: FIXED written into the working tree over PROPOSED at HEAD is refused",
           status="PROPOSED", edit=edit_prereg_fixed, expect_rc=3, expect_in="differs from HEAD")
with tempfile.TemporaryDirectory() as td:
    rc, out = run_main(["score", "--records", "a.json", "b.json", "--prereg", "x.md",
                        "--out", str(Path(td) / "s.json")], REPO)
    check("H3: there is no --prereg option (argparse refuses it)",
          isinstance(rc, tuple) and rc[0] == "SystemExit", rc)
    rc, out = run_main(["score", "--rec", "a.json", "--out", str(Path(td) / "s.json")], REPO)
    check("H3: option abbreviations are refused", isinstance(rc, tuple), rc)
ap = p2_baseline.build_parser()
sub = next(a for a in ap._actions if a.__class__.__name__ == "_SubParsersAction")
opts = {name: sorted(o for a in sp._actions for o in a.option_strings if o not in ("-h", "--help"))
        for name, sp in sub.choices.items()}
check("H3: the producer's whole option surface is exactly this (no bypass option exists)",
      opts == {"record": ["--cli", "--corpus-root", "--out", "--sample", "--timeout"],
               "score": ["--out", "--records"]}, opts)
score_case("H4 (exp2): the same record twice is refused", records=["rec1.json", "rec1.json"],
           expect_rc=2, expect_in="sample 1 and sample 2")
score_case("H4: one record alone is refused", records=["rec1.json"], expect_rc=2,
           expect_in="exactly two")
score_case("H4: a record whose rows are another sample's is refused",
           arts=lambda a1, a2: {"rec1.json": dict(a1, rows=rec_rows(S2_FAKE)), "rec2.json": a2},
           expect_rc=2, expect_in="not exactly")
score_case("H4: a record with a duplicated row is refused",
           arts=lambda a1, a2: {"rec1.json": dict(a1, rows=rec_rows(S1_FAKE[:199] + [S1_FAKE[0]])),
                                "rec2.json": a2}, expect_rc=2, expect_in="not exactly")
score_case("H2a (exp1): a record whose frame_window is offset 720 is refused (exit 3)",
           arts=lambda a1, a2: {"rec1.json": dict(a1, frame_window={"offset": 720, "n": 200}),
                                "rec2.json": a2}, expect_rc=3)
score_case("H2b: a row with no arxiv_id is refused (exit 3)",
           arts=lambda a1, a2: {"rec1.json": dict(a1, rows=rec_rows(S1_FAKE[:199]) + [
               {"graded": True}]), "rec2.json": a2}, expect_rc=3)
score_case("H2b: a row with a `SID/.` id is refused (exit 3)",
           arts=lambda a1, a2: {"rec1.json": dict(a1, rows=rec_rows(S1_FAKE[:199] + [SID + "/."])),
                                "rec2.json": a2}, expect_rc=3)
score_case("H2c: a self-declared sample label is not trusted (sample 2's rows labelled 1)",
           arts=lambda a1, a2: {"rec1.json": dict(a2, sample=1, frame_window=a1["frame_window"],
                                                  grade_of_record=a1["grade_of_record"]),
                                "rec2.json": a2}, expect_rc=2, expect_in="not exactly")
score_case("H2c: a string sample label is refused",
           arts=lambda a1, a2: {"rec1.json": dict(a1, sample="1"), "rec2.json": a2}, expect_rc=3)
score_case("L1: a copy (new inode) of an id-less artefact given as a record is refused",
           arts=lambda a1, a2: {"rec1.json": {"summary": {}}, "rec2.json": a2}, expect_rc=2,
           expect_in="is not a")


def dangling(repo):
    (repo / "corpora/real_roots/x_sample3_dangling.json").symlink_to("/nonexistent")
    (repo / "corpora/p2_baseline/dangling.json").symlink_to("/nonexistent")


score_case("L1: a dangling *sample3* symlink beside the inputs does not crash scoring",
           edit=dangling, expect_rc=0)
score_case("L1: a dangling symlink given as a record is refused cleanly (no traceback)",
           edit=dangling, records=["dangling.json", "rec2.json"], expect_rc=2,
           expect_in="not inside the repository")
score_case("H3: a record edited after its commit is refused",
           edit=lambda repo: (repo / "corpora/p2_baseline/rec1.json").write_text("{}"),
           expect_rc=3, expect_in="differs from HEAD")


def with_exclusions(a1, a2):
    rows = rec_rows(S1_FAKE)
    for r_ in rows[:175]:
        r_.update(excluded="tree differs from the grade of record", graded=False)
    return {"rec1.json": dict(a1, rows=rows), "rec2.json": a2}


rc, res = score_case("H5 (exp2): record-time exclusions VOID the run (exit 4)",
                     arts=with_exclusions, expect_rc=p2_baseline.EXIT_VOID)
if res:
    check("H5: the exclusions are counted by reason in the output",
          res.get("excluded_at_record_by_reason") == {"tree differs from the grade of record": 175}
          and res["excluded"]["at_record"] == 175, res.get("excluded_at_record_by_reason"))
    check("M3(a): a VOID output presents no metric",
          res.get("void") is True and not any(k in res for k in (
              "cause_recall_top1", "cause_precision_top1_heuristic",
              "location_precision_line_heuristic",
              "location_recall_line", "location_recall_file", "lines")), sorted(res))


def few_fails(a1, a2):
    rows1, rows2 = rec_rows(S1_FAKE), rec_rows(S2_FAKE)
    for r_ in rows1 + rows2[:-10]:
        r_.update(compiles=True, gold={"has_error": False}, pred=pred("READY"))
    return {"rec1.json": dict(a1, rows=rows1), "rec2.json": dict(a2, rows=rows2)}


score_case("M3(a) (exp2): V1 failing (10 fails < 20) VOIDs the run (exit 4)",
           arts=few_fails, expect_rc=p2_baseline.EXIT_VOID, expect_in="V1")


def abstainer(a1, a2):
    return {"rec1.json": dict(a1, rows=rec_rows(S1_FAKE, "abstain")),
            "rec2.json": dict(a2, rows=rec_rows(S2_FAKE, "abstain"))}


rc, res = score_case("M3(c): an abstaining predictor is scored (rc 0)", arts=abstainer,
                     expect_rc=0)
if res:
    st = {ln["id"]: ln["status"] for ln in res["lines"]}
    check("M3(c) (exp2 abstainer): S1/S3 not evaluable (so not met), K1/K2 not evaluable "
          "(they do not 'hold')", all(st[i] == "not-evaluable" for i in (
              "SC1", "SC3", "SH1", "SH3", "SH5", "KH1", "KH3", "KH5"))
          and all(ln["holds"] is None for ln in res["lines"] if ln["kind"] == "kill"), st)
lines_small = [{"id": "S3", "kind": "success", "metric": "cause_precision_top1_heuristic",
                "stat": "point",
                "op": "==", "value": 1.0, "min_n": 10}]
ev = p2_baseline.evaluate_lines({"lines": lines_small}, d.score_rows(rec_rows(S1_FAKE[:1])))
check("M3(b) (exp2): S3 at n = 1 is not evaluable", ev[0]["status"] == "not-evaluable", ev)

# 9c'. ruling R4: the claim tier, soundness, floors, cause-line gold
PROVEN_LINE = ("TIER\tproven\tPROVEN-NOT-READY\tPROVEN NOT-READY main.tex:4:1 ! LaTeX Error: "
               "File `fig.sty' not found. [E-12, rule X, probe p, contract abcdef12]\n")
p = d.cli_prediction(MODEL_OK + "NOT-READY\tmain.tex\n  T5 rule violations: [DELIM-001]\n"
                     + PROVEN_LINE)
tiers = [(x["tier"], x["code"]) for x in p["predictions"]]
check("R4: a PROVEN-NOT-READY TIER line is the one certified claim; reasons stay heuristic",
      tiers == [("heuristic", "DELIM-001"), ("certified", "PROVEN")], tiers)
c = p["predictions"][-1]
check("R4: the certified claim carries the proof's file:line and its classified message",
      (c["file"], c["line"], c["class"], c["object"]) == ("main.tex", 4, "missing-file", "fig"), c)
p = d.cli_prediction(MODEL_OK + "NOT-READY\tmain.tex\n  T5 rule violations: [DELIM-001]\n"
                     "TIER\theuristic\tLIKELY-FAIL\tLIKELY FAIL\n")
check("R4: a heuristic TIER line makes no certified claim",
      all(x["tier"] == "heuristic" for x in p["predictions"]) and p["verdict_tier"] == "heuristic")
p = d.cli_prediction(MODEL_OK + "NOT-READY\tmain.tex\n"
                     "TIER\tproven\tPROVEN-NOT-READY\tgarbled\n")
check("R4: an unparseable PROVEN line is a MALFORMED certified claim (fail closed)",
      p["predictions"][-1].get("malformed") is True and p["predictions"][-1]["tier"] == "certified")
p = d.cli_prediction(MODEL_OK + "READY\tmain.tex\nTIER\tproven\tPROVEN-NOT-READY\t"
                     "PROVEN NOT-READY main.tex:1:1 ! x [e]\n")
check("R4: no certified claim is read from a READY answer", p["predictions"] == [])


def cert_row(i, compiles=False, cls="missing-file", obj="fig", line=4, gold_line=4,
             malformed=False):
    cp = {"tier": "certified", "code": "PROVEN", "class": cls, "object": obj,
          "file": "main.tex", "line": line}
    if malformed:
        cp = {"tier": "certified", "code": "PROVEN", "class": None, "object": None,
              "file": None, "line": None, "malformed": True}
    return {"arxiv_id": f"0001.{i:05d}v1", "graded": True, "agrees_with_record": True,
            "compiles": compiles, "excluded": None,
            "gold": ({"has_error": False} if compiles else
                     gold("missing-file", "fig", "main.tex", gold_line)),
            "pred": pred("NOT-READY", {"tier": "heuristic", "class": "encoding"}, cp)}


S_ok = d.score_rows([cert_row(i) for i in range(30)])
check("R4: 30 exact certified claims: certified precision 30/30 and no defect",
      (S_ok["cause_precision_top1_certified"]["k"], S_ok["cause_precision_top1_certified"]["n"],
       S_ok["location_precision_line_certified"]["k"], S_ok["soundness"]["certified_wrong"])
      == (30, 30, 30, 0), S_ok["soundness"])
check("R4: the tiers are scored separately (the wrong heuristic first reason does not touch "
      "certified precision; heuristic precision is 0/30)",
      (S_ok["cause_precision_top1_heuristic"]["k"], S_ok["cause_precision_top1_heuristic"]["n"])
      == (0, 30))
check("R4: recall uses the certified claim first (certified ∪ heuristic)",
      S_ok["cause_recall_top1"]["k"] == 30)
for label, row in (("a wrong class", cert_row(99, cls="encoding")),
                   ("a wrong line (l.N is the certified gold)", cert_row(99, line=5)),
                   ("a claim on a compiling document", cert_row(99, compiles=True)),
                   ("a malformed claim", cert_row(99, malformed=True))):
    S_bad = d.score_rows([cert_row(i) for i in range(30)] + [row])
    check(f"R4: one wrong certified claim ({label}) is a soundness defect",
          S_bad["soundness"]["certified_wrong"] == 1
          and S_bad["soundness"]["wrong_rows"] == ["0001.00099v1"], S_bad["soundness"])
ev = p2_baseline.evaluate_lines({"lines": [
    {"id": "SH3", "kind": "success", "metric": "cause_precision_top1_certified", "stat": "point",
     "op": "==", "value": 1.0, "min_n": 29}]}, d.score_rows([cert_row(i) for i in range(28)]))
check("R4: a success line at n = 28 (< 29) is not evaluable", ev[0]["status"] == "not-evaluable",
      ev)
ev = p2_baseline.evaluate_lines({"lines": [
    {"id": "SH3", "kind": "success", "metric": "cause_precision_top1_certified", "stat": "point",
     "op": "==", "value": 1.0, "min_n": 29}]}, d.score_rows([cert_row(i) for i in range(29)]))
check("R4: ... and evaluable at n = 29", ev[0]["status"] == "holds", ev)


def cert_arts(wrong, void=False):
    def f(a1, a2):
        rows1 = [dict(cert_row(i), arxiv_id=x) for i, x in enumerate(S1_FAKE)]
        if wrong:
            rows1[0] = dict(cert_row(0, cls="encoding"), arxiv_id=S1_FAKE[0])
        if void:
            rows1[1].update(excluded="tree differs from the grade of record", graded=False)
        return {"rec1.json": dict(a1, rows=rows1), "rec2.json": a2}
    return f


rc, res = score_case("R4: exact certified claims score normally (rc 0)", arts=cert_arts(False),
                     expect_rc=0)
if res:
    check("R4: the outcome is SCORED with an empty defect list",
          res.get("outcome") == "SCORED" and res["soundness"]["certified_wrong"] == 0)
rc, res = score_case("R4: one wrong certified claim exits 5 (SOUNDNESS DEFECT, not a kill)",
                     arts=cert_arts(True), expect_rc=p2_baseline.EXIT_SOUNDNESS,
                     expect_in="SOUNDNESS DEFECT")
if res:
    check("R4: the outcome names the defect and its row",
          res.get("outcome") == "SOUNDNESS-DEFECT"
          and res["soundness"]["wrong_rows"] == [S1_FAKE[0]], res.get("soundness"))
rc, res = score_case("R4: the defect takes precedence over VOID (exit 5)",
                     arts=cert_arts(True, void=True), expect_rc=p2_baseline.EXIT_SOUNDNESS)
if res:
    check("R4: a void run still reports its soundness block",
          res.get("void") is True and res["soundness"]["certified_wrong"] == 1)

# the two-labeller cause-line gold (§5.5)
LAB = {"schema": d.LABEL_SCHEMA, "labeller_a": "A", "labeller_b": "B", "adjudicator": "C",
       "docs": {
           "0001.00000v1": {"A": {"file": "main.tex", "line": 3},
                            "B": {"file": "./main.tex", "line": 3}},
           "0001.00001v1": {"A": {"file": "main.tex", "line": 3}, "B": {"file": "main.tex", "line": 5},
                            "adjudicated": {"file": "main.tex", "line": 5}},
           "0001.00002v1": {"A": {"file": "main.tex", "line": 3}, "B": {"file": "main.tex", "line": 5},
                            "adjudicated": {"file": "main.tex", "line": 9}},
           "0001.00003v1": {"A": {"file": "main.tex", "line": 3}, "B": {"file": "main.tex", "line": 5},
                            "adjudicated": "unresolvable"},
           "0001.00004v1": {"A": {"none": "no single line"}, "B": {"none": "macro"}}}}
gold_cl, st = d.cause_line_gold(LAB)
check("§5.5: agreement (after canon_path) is gold; adjudication must pick one of the two; "
      "unresolvable and both-none have no gold",
      gold_cl == {"0001.00000v1": {"file": "main.tex", "line": 3},
                  "0001.00001v1": {"file": "main.tex", "line": 5}}
      and st == {"entries": 5, "agreed": 1, "adjudicated": 1, "unresolved": 2,
                 "no_cause_line": 1}, (gold_cl, st))
for label, bad in (("labellers not distinct", dict(LAB, labeller_b="A")),
                   ("adjudicator = a labeller", dict(LAB, adjudicator="B")),
                   ("wrong schema", dict(LAB, schema="x"))):
    try:
        d.cause_line_gold(bad)
        ok = False
    except ValueError:
        ok = True
    check(f"§5.5: a label file with {label} is refused", ok)


def cl_rows(a1, a2):
    rows1 = rec_rows(S1_FAKE)
    for r_ in rows1[:2]:
        r_["pred"] = pred("NOT-READY", {"tier": "heuristic", "class": None, "file": "main.tex",
                                        "line": 3})
    return {"rec1.json": dict(a1, rows=rows1), "rec2.json": a2}


def add_labels(repo, commit=True):
    (repo / p2_baseline.CAUSE_LABELS).write_text(json.dumps(LAB))
    if commit:
        commit_all(repo)


rc, res = score_case("§5.5: committed cause-line labels are scored (rc 0)", arts=cl_rows,
                     edit=add_labels, expect_rc=0)
if res:
    m_ = res.get("location_precision_cause_heuristic", {})
    check("§5.5: heuristic claims are scored against the cause-line gold (1 of 2 right)",
          (m_.get("k"), m_.get("n")) == (1, 2)
          and res["provenance"]["cause_labels"]["stats"]["agreed"] == 1, (m_,
                                                                          res.get("provenance")))
score_case("§5.5: an uncommitted label file is refused", arts=cl_rows,
           edit=lambda repo: add_labels(repo, commit=False), expect_rc=3,
           expect_in="not committed")

# 9d. CLI provenance (M4)
real_cli_provenance = saved[4]
with tempfile.TemporaryDirectory() as td:
    cr = Path(td) / "ck"
    (cr / "latex-parse/src").mkdir(parents=True)
    (cr / "latex-parse/src/a.ml").write_text("let x = 1\n")
    (cr / "_build").mkdir()
    exe = cr / "_build/cli.exe"
    exe.write_text("binary")
    (cr / ".gitignore").write_text("_build/\n")
    git(cr, "init", "-q")
    commit_all(cr)
    prov = real_cli_provenance(exe)
    check("M4: the CLI's provenance names its binary hash, HEAD and src tree",
          prov.get("sha256") and len(prov.get("head", "")) == 40 and prov.get("src_tree"), prov)
    (cr / "latex-parse/src/a.ml").write_text("let x = 2\n")
    check("M4: a CLI built from a dirty latex-parse/src is refused",
          refused(real_cli_provenance, exe, exc=p2_baseline.InputError))
    (cr / "latex-parse/src/a.ml").write_text("let x = 1\n")
    (cr / "latex-parse/src/new.ml").write_text("let y = 1\n")
    check("M4: an untracked latex-parse/src file is refused",
          refused(real_cli_provenance, exe, exc=p2_baseline.InputError))

# 9e. the real seals: counts only, never an id
real = seal.sealed_ids(REPO)
check("seal: the real committed sealed sets hold exactly 200 + 1,080 paper keys",
      len(real) == 1280, len(real))
hm = json.loads(seal.committed(REPO, seal.HELDOUT_MANIFEST)[0])
check("R3: the real held-out manifest records the frame rule and its verification",
      hm["frame"] == {"corpus": "LP_v24_FULL_BACKUP_20250716_165548/corpus/papers",
                      "frame_size": 2719, "selection": "sha256(arxiv_id) ascending",
                      "offset": 920, "n": 1080}
      and hm["built"]["verification"] == {
          "frame_size": 2719, "sample1_equals_ranks_0_200": True,
          "sample2_equals_ranks_200_400": True, "sample3_equals_ranks_720_920": True,
          "window_920_2000_size": 1080, "window_ids_valid": True,
          "window_disjoint_from_samples_1_3": True}
      and set(hm) == {"purpose", "frame", "built", "docs"}
      and all(set(r_) == {"arxiv_id"} for r_ in hm["docs"]), sorted(hm))
for k in (1, 2):
    docs, rel, blob = seal.sample_docs(REPO, k, real)
    check(f"seal: real sample {k} loads from HEAD (200 valid ids, none sealed)", len(docs) == 200)

# ── 9f. the P2 records are registered with the oracle-pin gate (L7) ─────────
import check_oracle_pin  # noqa: E402
for k in (1, 2):
    rel = f"corpora/p2_baseline/diag_sample{k}.json"
    check(f"L7: {rel} is a GRADED artefact of check_oracle_pin, its graders this producer's",
          (rel, ("oracle",)) in check_oracle_pin.GRADED
          and tuple(check_oracle_pin.GRADERS.get(rel, ())) == p2_baseline.GRADERS,
          check_oracle_pin.GRADERS.get(rel))
check("L7: the pre-registered procedure names the registered paths",
      all(f"corpora/p2_baseline/diag_sample{k}.json" in PRE.read_text() for k in (1, 2)))

# ── 10. the recorded grades still name current grading code ──────────────────
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
