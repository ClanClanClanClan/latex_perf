#!/usr/bin/env python3
"""The lexical contract of the strict fragment L_S0 (ADR-012, M2 phase 2).

WHAT IT WRITES. corpora/contracts/strict/article-s0-lexical.json: the reading
regime of the `article` configuration at body start, which the Coq lexer
(proofs/Strict/Lexer.v, record `lexcon`) takes as a PARAMETER and the driver
(latex-parse/strict/strict_decide.ml, trusted loader T5) builds from this
file:

  * `catcodes`: \\catcode of every byte 0..255, dumped INSIDE the body of the
    configuration's own document by the pinned image (gen_contract.py's
    `catcode_line`, the same dump the configuration contract diffs against
    format state; its `catcodes` field records only differences, and the
    format table is not stored, so the full table is recorded here);
  * `endlinechar`: \\endlinechar at body start;
  * `structural`: the names the front matter and the body's structure are
    made of. They are READ, not written: from the phase-1 renderer
    proofs/Strict/Syntax.v (`render_tok (TPar true)` gives \\par, `render_tok
    TEnd` gives \\end and the document environment, `header` gives
    \\documentclass, the class and \\begin, `render_tok TMOpenInline` ..
    `TMCloseDisplay` the four delimiter symbols), so the lexer reads exactly
    the names phase 1's attested documents were printed with; the class is
    cross-checked against the configuration contract;
  * `meanings`: \\meaning of each structural name at body start (evidence);
  * `source` (the kernel/contract files, by sha256), `oracle` provenance,
    and the sha256 of the dump document.

The rules that USE these values (a blank line is \\par, \\end{document} ends
the reading, ...) are attested by the lexer probe families
(strict_differential.py --bytes-rules), not by this file.

Needs the oracle (the pinned image via _oracle.py). Usage:
    python3 scripts/tools/gen_strict_lexical.py [--check]
--check regenerates in memory and fails unless the committed file is
byte-identical to the regeneration (the file holds no timestamp).
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import _oracle  # noqa: E402
import _strict_s0 as S  # noqa: E402
import gen_contract as G  # noqa: E402

SCHEMA = "lp-strict-lexical/1"
GENERATOR_VERSION = "1"
OUT = S.REPO / "corpora/contracts/strict/article-s0-lexical.json"
SYNTAX = S.REPO / "proofs/Strict/Syntax.v"
END = "|lpe"


def structural_from_syntax(text: str) -> dict:
    """The structural names as the phase-1 renderer prints them."""
    def tok_line(ctor: str) -> str:
        m = re.search(r"^\s*\|\s*" + re.escape(ctor) + r"\s*=>\s*(.*)$", text, re.M)
        if not m:
            raise SystemExit(f"Syntax.v: no render_tok case for {ctor}")
        return m.group(1)

    def chars(s: str) -> list[str]:
        return re.findall(r'"(.)"', s)

    par = tok_line("TPar true")
    m = re.fullmatch(r"\[bs;((?:\s*\"[a-z]\";)+)\s*nl\]", par.strip())
    if not m:
        raise SystemExit(f"Syntax.v: unexpected render of TPar true: {par}")
    par_name = "".join(chars(m.group(1)))
    end = re.search(r'list_ascii_of_string "\\(\w+)\{(\w+)\}"', tok_line("TEnd"))
    if not end:
        raise SystemExit("Syntax.v: unexpected render of TEnd")
    hdr = re.search(r'Definition header : list ascii :=\s*list_ascii_of_string '
                    r'"\\(\w+)\{(\w+)\}" \+\+ \[nl\]\s*\+\+ list_ascii_of_string '
                    r'"\\(\w+)\{(\w+)\}" \+\+ \[nl\]\.', text)
    if not hdr:
        raise SystemExit("Syntax.v: unexpected header")
    delims = {}
    for key, ctor in (("open_inline", "TMOpenInline"), ("close_inline", "TMCloseInline"),
                      ("open_display", "TMOpenDisplay"), ("close_display", "TMCloseDisplay")):
        m = re.fullmatch(r'\[bs;\s*"(.)";\s*nl\]', tok_line(ctor).strip())
        if not m:
            raise SystemExit(f"Syntax.v: unexpected render of {ctor}")
        delims[key] = m.group(1)
    if hdr.group(4) != end.group(2):
        raise SystemExit("Syntax.v: header's environment differs from TEnd's")
    return {
        "par": par_name,
        "end": end.group(1),
        "begin": hdr.group(3),
        "documentclass": hdr.group(1),
        "class": hdr.group(2),
        "document_env": hdr.group(4),
        "math_delimiters": delims,
    }


def dump_tex(cfg: dict, st: dict) -> bytes:
    names = [st["par"], st["end"], st["begin"], st["documentclass"]] + \
        list(st["math_delimiters"].values())
    lines = [G.preamble_tex(G.normalize_config(cfg)), b"\\begin{document}\n",
             G.catcode_line(),
             b"\\immediate\\write-1{LPE:\\the\\endlinechar}%\n"]
    for n in names:
        lines.append(b"\\immediate\\write-1{LPL:" + n.encode() + b":\\meaning\\"
                     + n.encode() + END.encode() + b"}%\n")
    lines.append(b"x\n\\end{document}\n")
    return b"".join(lines)


def generate() -> dict:
    contract = json.loads(S.CONTRACT.read_text())
    st = structural_from_syntax(SYNTAX.read_text())
    if st["class"] != contract["configuration"]["class"]:
        raise SystemExit(f"Syntax.v renders class {st['class']!r} but the contract's "
                         f"configuration is {contract['configuration']['class']!r}")
    oracle = _oracle.get_oracle()
    tex = dump_tex(contract["configuration"], st)
    with oracle.tempdir("lp-strict-lexical-") as td:
        td = Path(td)
        (td / "main.tex").write_bytes(tex)
        rc, _, to = oracle.run_engine(
            td, _oracle.ENGINE_PDFLATEX,
            ["-interaction=nonstopmode", "-halt-on-error", "main.tex"],
            G.tex_vars("grading", td), 300)
        log = (td / "main.log").read_bytes()
    if to or rc != 0:
        raise SystemExit(f"gen_strict_lexical: the dump did not compile (rc {rc}, "
                         f"timeout {to})")
    d = G.parse_dump(log)
    cats = d["catcodes"]
    if cats is None or len(cats) != 256:
        raise SystemExit("gen_strict_lexical: no catcode table in the log")
    m = re.search(rb"^LPE:(-?\d+)$", log, re.M)
    if not m:
        raise SystemExit("gen_strict_lexical: no \\endlinechar in the log")
    meanings = {}
    for nm, meaning in re.findall(rb"^LPL:([^:]+):(.*?)\|lpe$", log, re.M | re.S):
        meanings[nm.decode()] = meaning.decode("utf-8", "replace")
    want = [st["par"], st["end"], st["begin"], st["documentclass"]] + \
        list(st["math_delimiters"].values())
    if sorted(meanings) != sorted(want):
        raise SystemExit(f"gen_strict_lexical: meanings missing: {sorted(set(want) - set(meanings))}")
    return {
        "schema": SCHEMA,
        "generator": "scripts/tools/gen_strict_lexical.py",
        "generator_version": GENERATOR_VERSION,
        "source": S.source_block(),
        "syntax_sha256": S.sha256_file(SYNTAX),
        "oracle": oracle.provenance(),
        "configuration": contract["configuration"],
        "catcodes": cats,
        "endlinechar": int(m.group(1)),
        "structural": st,
        "meanings": {k: meanings[k] for k in sorted(meanings)},
        "contract_catcode_diff": contract.get("catcodes", {}),
        "dump_tex_sha256": hashlib.sha256(tex).hexdigest(),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    out = generate()
    text = json.dumps(out, indent=1, sort_keys=True) + "\n"
    if args.check:
        cur = OUT.read_text() if OUT.is_file() else ""
        if cur != text:
            print("gen_strict_lexical: the committed lexical contract differs from "
                  "a regeneration")
            return 1
        print("gen_strict_lexical: OK (byte-identical)")
        return 0
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(text)
    by = {}
    for b, c in enumerate(out["catcodes"]):
        by.setdefault(c, []).append(b)
    print(f"wrote {OUT.relative_to(S.REPO)}: endlinechar {out['endlinechar']}, "
          f"catcode classes {{{', '.join(f'{c}: {len(v)}' for c, v in sorted(by.items()))}}}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
