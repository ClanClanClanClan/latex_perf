#!/usr/bin/env python3
"""Gate: the decision on BYTES of the strict fragment and its evidence (ADR-012 M2 phase 2).

Pure: no TeX, no docker, no build. It reads the Coq sources of the reader
and the bytes decider (proofs/Strict/Lexer.v, Front.v, DecideBytes.v,
BridgeBytes.v, Explain.v), the committed extraction, the lexical contract and
the committed, oracle-graded evidence, and fails when they no longer belong
together:

  1. PROBE-TAGGED READER. Every constructor of `FirstLine`, `Lines`, `LineLex`,
     `LinesLex` (Lexer.v) and `Prologue`, `Body` (Front.v) carries a
     `probe L0/<constructor>` comment directly above it, and the list of
     constructors is the harness's (strict_differential.LEX_RULES).
  2. EVERY CONSTRUCTOR ATTESTED (the branch-coverage discipline of
     check_strict_kernel.py, extended to the reader). In
     corpora/strict_s0/bytes_probes.json each constructor's family agrees
     with the oracle on every graded document and at least one AGREEING
     graded document used it -- except the constructors whose use puts a
     file outside the fragment (OUTSIDE_ONLY: a RBad token, and LL_end,
     below), which must be used by at least one document the extracted
     decider places outside, and LL_nullcs, which the lexical contract makes
     unreachable (UNREACHABLE; both derived from the data below).
  3. FRESH EVIDENCE. bytes_probes.json and bytes_differential.json record the
     sha256 of the extraction they ran (latex-parse/strict/
     strict_bytes_extracted.ml), of the phase-1 extraction, of the signature
     file, of the lexical contract, and the kernel/contract files; each must
     be the committed file's.
  4. NO DISAGREEMENT. Both files: 0 disagreements (verdict, message class,
     LINE), 0 infrastructure failures, 0 files generated inside that were
     built to be outside or the reverse, 0 mismatches between `explain` and
     the verdict; the rule probes' phase-1 renderings are decided the same
     by the tree decider and the bytes decider (verdict, reason, line); the
     differential graded at least MIN_BYTES_DIFFERENTIAL files, and its bound
     states that it is over the generator's distribution (C-85).
  5. NEAR-MISSES ARE OUTSIDE. Every L0-NEAR file of both files was decided
     NOT-IN-FRAGMENT (none graded), and there are at least MIN_NEAR of them.
  6. READER BRANCH MATRIX. Every cell <state>|<class> of the line reader
     (state N, M, S x every class the lexical contract's catcodes give a
     byte, the escape character refined by what follows it, ^ by ^^) is
     exercised: an in-fragment class by an AGREEING graded probe, a class
     outside the fragment by a probe decided outside; the front matter's
     filler cells and both shapes of \\end{document} likewise. And every cell
     of the KERNEL's branch matrix (check_strict_kernel.required_cells) that
     the phase-1 rule probes cover is covered at the byte level too.
  7. NO NAME IN COQ. The phase-2 files hold no string literal outside
     comments: every name reaches the reader through the lexical contract.
  8. BOUNDS. Lexer.v and DecideBytes.v pin max_line_bytes (10,000) and
     max_file_bytes (1,000,000) by Examples, equal to the harness's
     constants; in_strict_bytes requires them and the kernel's bounds and
     excludes a stream ending with $; the family L0-bounds agrees.
  9. FAITHFULBYTES' BODY IS PINNED, as Faithful's is (check 10 of
     check_strict_kernel.py, OPEN-121 review MEDIUM-1 and C-87): the
     definition's text is FAITHFUL_BYTES_BODY; it mentions Runs and Parse and
     none of the decider's executable functions (case-sensitive: `Parse` is
     the declarative relation, `parse` the executable parser); and every Coq
     SENTENCE of BridgeBytes.v is the pinned Require, FaithfulBytes or one of
     the two bridge corollaries. check_print_assumptions.py pins the
     elaborated body (coqc Print) and its convertibility against fully
     qualified names.
 10. THE LEXICAL CONTRACT IS THE GENERATOR'S. corpora/contracts/strict/
     article-s0-lexical.json has 256 catcodes and an \\endlinechar, its
     structural names are the ones the phase-1 renderer prints
     (gen_strict_lexical.structural_from_syntax over Syntax.v), its class is
     the configuration's, its record of the contract's catcode differences
     is the contract's, and it names the committed kernel/contract files.

Run: python3 scripts/tools/check_strict_bytes.py [--repo .]
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_strict_kernel import required_cells, strip_coq_comments  # noqa: E402

MIN_BYTES_DIFFERENTIAL = 3000
MIN_NEAR = 50
MAX_LINE_BYTES = 10_000
MAX_FILE_BYTES = 1_000_000
PROBES = "corpora/strict_s0/bytes_probes.json"
DIFFERENTIAL = "corpora/strict_s0/bytes_differential.json"
LEXICAL = "corpora/contracts/strict/article-s0-lexical.json"
BYTES_EXTRACT = "latex-parse/strict/strict_bytes_extracted.ml"
KERNEL_EXTRACT = "latex-parse/strict/strict_kernel_extracted.ml"
SIGNATURES = "corpora/contracts/strict/article-s0-signatures.json"
PHASE2_FILES = ["Lexer.v", "Front.v", "DecideBytes.v", "BridgeBytes.v", "Explain.v"]
READER_INDUCTIVES = [("Lexer.v", "Inductive FirstLine :"), ("Lexer.v", "Inductive Lines :"),
                     ("Lexer.v", "Inductive LineLex "), ("Lexer.v", "Inductive LinesLex "),
                     ("Front.v", "Inductive Prologue "), ("Front.v", "Inductive Body ")]
# A RBad token (Lexer.v) puts a file outside; LL_end is reachable only after a
# control symbol consumed the end-of-line character (checked on the data).
OUTSIDE_ONLY = {"LL_hathat", "LL_word_hathat", "LL_sym_hathat", "LL_bad", "LX_long",
                "LL_end", "FL_directive"}
UNREACHABLE = {"LL_nullcs"}
# TeX's category codes (Lexer.v `cat`, in TeX's order) -> reader classes.
CAT_NAMES = ["escape", "bgroup", "egroup", "math", "align", "eol", "param", "sup",
             "sub", "ignored", "spacer", "letter", "other", "active", "comment",
             "invalid"]
IN_CLASSES = {"bgroup", "egroup", "math", "eol", "sup", "sub", "spacer", "letter",
              "other", "comment", "esc.word", "esc.sym"}
OUT_CLASSES = {"align", "param", "ignored", "active", "invalid", "sup.hathat",
               "esc.word.hathat", "esc.sym.hathat"}
# (no space TOKEN can precede \documentclass: a file starts in state N, and
# only a character puts the reader in state M)
FRONT_CELLS_IN = {"P|pre|par_line", "P|mid|space", "P|mid|par_line",
                  "P|mid|par_word", "B_end|one_line", "B_end|split"}

FAITHFUL_BYTES_HEAD = ("Definition FaithfulBytes (oracle_ok : list Ascii.ascii -> Prop) "
                       "(C : bcontract) : Prop :=")
FAITHFUL_BYTES_BODY = ("forall b ks, in_strict_bytes C b -> Parse (bc_lex C) b ks -> "
                       "(oracle_ok b <-> Runs (bc_kernel C) init (toks_of ks) Compiles)")
FAITHFUL_BYTES_FORBIDDEN = ("decide", "decide_bytes", "run", "step", "rd", "lex", "parse",
                            "front", "body", "prologue", "lexl", "explain",
                            "in_strict_bytes_b", "strict_ks_b")
BRIDGE_REQUIRE = ("From LaTeXPerfectionist.Strict Require Import Syntax Contract Semantics "
                  "Decide Lexer Front DecideBytes")
BRIDGE_SENTENCES = [
    ("Definition", "FaithfulBytes"),
    ("Corollary", "strict_ready_iff_pdflatex_bytes"),
    ("Corollary", "strict_not_ready_pdflatex_bytes"),
]
_DEFINERS = r"Definition|Fixpoint|CoFixpoint|Let|Notation|Infix|Instance|" \
    r"Inductive|CoInductive|Record|Structure|Class|Axiom|Axioms|Parameter|" \
    r"Parameters|Hypothesis|Hypotheses|Variable|Variables|Conjecture|" \
    r"Coercion|Canonical|Ltac|Module|Section|Context|Program|Local|Global|" \
    r"Theorem|Lemma|Corollary|Remark|Fact|Proposition|Example|Import|Export|" \
    r"Require|From|Set|Unset|Arguments|Opaque|Transparent|Hint|Declare|Scheme"


def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def constructors(text: str, header: str) -> list[tuple[str, str]]:
    """(constructor, the comment directly above it) of an inductive."""
    i = text.index(header)
    j = text.index(".\n", text.index(":=", i))
    block = text[i:j]
    out = []
    for m in re.finditer(r"^\|\s*(\w+)\s*:", block, re.M):
        pre = block[:m.start()]
        k = pre.rfind("(*")
        out.append((m.group(1), pre[k:] if k >= 0 else ""))
    return out


def sentences(code: str) -> list[str]:
    """The Coq sentences of comment-free source (split at '.' + whitespace)."""
    parts = re.split(r"\.(?=\s|$)", code)
    return [" ".join(p.split()) for p in parts if p.strip()]


def bridge_findings(bridge: str) -> list[str]:
    out: list[str] = []
    code = strip_coq_comments(bridge)
    proofs = re.compile(r"^(Proof|Qed|intros|destruct|assert|rewrite|symmetry|apply|"
                        r"exact|split|exists|discriminate|contradiction|reflexivity)\b|"
                        r"^[-+*]")
    for s in sentences(code):
        m = re.match(rf"^({_DEFINERS})\b\s*(\S*)", s)
        if not m:
            if not proofs.match(s):
                out.append(f"BridgeBytes.v: unexpected sentence {s[:80]!r}")
            continue
        kind, name = m.group(1), m.group(2)
        if kind == "From":
            if s != BRIDGE_REQUIRE:
                out.append(f"BridgeBytes.v: the Require sentence is not the pinned one: "
                           f"{s[:160]!r} (a shadow module on this line was OPEN-121 "
                           f"re-review MEDIUM-1)")
            continue
        if (kind, name) not in BRIDGE_SENTENCES:
            out.append(f"BridgeBytes.v: defines more than FaithfulBytes and its corollaries: "
                       f"{(kind, name)} (a name defined here could shadow what "
                       f"FaithfulBytes reads)")
    head = " ".join(FAITHFUL_BYTES_HEAD.split())
    norm = " ".join(code.split())
    i = norm.find(head)
    if i < 0:
        return out + [f"BridgeBytes.v: no `{head}`"]
    j = norm.find(". ", i)
    body = norm[i + len(head):j if j >= 0 else len(norm)].strip()
    if body != " ".join(FAITHFUL_BYTES_BODY.split()):
        out.append(f"BridgeBytes.v: FaithfulBytes' body is not the pinned one\n"
                   f"      pinned: {FAITHFUL_BYTES_BODY}\n      found:  {body}")
    idents = set(re.findall(r"[A-Za-z_][A-Za-z_0-9']*", body))
    for need in ("Runs", "Parse"):
        if need not in idents:
            out.append(f"BridgeBytes.v: FaithfulBytes' body does not mention {need}")
    bad = sorted(idents & set(FAITHFUL_BYTES_FORBIDDEN))
    if bad:
        out.append(f"BridgeBytes.v: FaithfulBytes' body mentions {bad} -- the decider, "
                   f"the executable reader or parser must never be a premise's content")
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=".")
    args = ap.parse_args()
    repo = Path(args.repo).resolve()
    fails: list[str] = []
    strict = repo / "proofs/Strict"
    src = {f: (strict / f).read_text() for f in PHASE2_FILES}

    # 1. probe tags
    ctors: list[str] = []
    for f, header in READER_INDUCTIVES:
        for c, comment in constructors(src[f], header):
            ctors.append(c)
            if f"probe L0/{c}" not in comment:
                fails.append(f"{f}: constructor {c} has no `probe L0/{c}` comment "
                             f"directly above it")
    if len(ctors) < 40:
        fails.append(f"reader: found {len(ctors)} constructors; the parser of this gate "
                     f"is broken or the reader shrank")
    import strict_differential as D  # the harness's list (pure import)
    if sorted(ctors) != sorted(D.LEX_RULES):
        fails.append(f"reader constructors {sorted(set(ctors) ^ set(D.LEX_RULES))} differ "
                     f"from strict_differential.LEX_RULES")

    # 10. the lexical contract
    contract = json.loads((repo / "corpora/contracts/article.json").read_text())
    kernel_path = repo / contract["kernel"]["file"]
    kern = json.loads(kernel_path.read_text())
    lex = json.loads((repo / LEXICAL).read_text())
    cats = lex.get("catcodes", [])
    if len(cats) != 256 or not all(isinstance(c, int) and 0 <= c <= 15 for c in cats):
        fails.append("lexical contract: not 256 catcodes in 0..15")
        cats = [12] * 256
    el = lex.get("endlinechar")
    if not isinstance(el, int):
        fails.append("lexical contract: no endlinechar")
        el = -1
    import gen_strict_lexical as GL  # pure: reads Syntax.v
    want_st = GL.structural_from_syntax((strict / "Syntax.v").read_text())
    if lex.get("structural") != want_st:
        fails.append(f"lexical contract: structural names {lex.get('structural')} are not "
                     f"the ones Syntax.v renders {want_st}")
    if want_st["class"] != contract["configuration"]["class"]:
        fails.append("lexical contract: class differs from the configuration's")
    if lex.get("contract_catcode_diff") != contract.get("catcodes", {}):
        fails.append("lexical contract: its record of the contract's catcode differences "
                     "is not the contract's")
    cur_src = {"kernel_sha256": sha(kernel_path),
               "contract_sha256": sha(repo / "corpora/contracts/article.json"),
               "kernel_meanings_sha256": kern["meanings_sha256"],
               "contract_config_key": contract["config_key"]}
    for k, v in cur_src.items():
        if lex.get("source", {}).get(k) != v:
            fails.append(f"lexical contract: source {k} is not the committed file's")

    # the data behind OUTSIDE_ONLY's LL_end and UNREACHABLE's LL_nullcs
    delims = set((want_st.get("math_delimiters") or {}).values())
    if not (0 <= el <= 255) or cats[el] != 5:
        fails.append("lexical contract: \\endlinechar is not a category-5 byte; LL_end and "
                     "LL_nullcs are then reachable inside the fragment (re-derive "
                     "OUTSIDE_ONLY/UNREACHABLE)")
    elif chr(el) in delims:
        fails.append("lexical contract: \\endlinechar is a math-delimiter symbol; LL_end is "
                     "then reachable inside the fragment")

    # 3. fresh evidence
    cur = {"bytes_extract_sha256": sha(repo / BYTES_EXTRACT),
           "kernel_extract_sha256": sha(repo / KERNEL_EXTRACT),
           "signatures_sha256": sha(repo / SIGNATURES),
           "lexical_sha256": sha(repo / LEXICAL)}
    files = {}
    for label, rel in (("bytes_probes", PROBES), ("bytes_differential", DIFFERENTIAL)):
        d = json.loads((repo / rel).read_text())
        files[label] = d
        for k, v in cur.items():
            if d.get(k) != v:
                fails.append(f"{label}: ran another {k.replace('_sha256', '')} "
                             f"({str(d.get(k))[:12]} != committed {v[:12]}); re-run it")
        for k in ("kernel_sha256", "contract_sha256"):
            if d.get("source", {}).get(k) != cur_src[k]:
                fails.append(f"{label}: source {k} is not the committed file's")

        # 4. no disagreement
        s_ = d.get("summary", {})
        if s_.get("disagree") != 0 or d.get("disagreements"):
            fails.append(f"{label}: {s_.get('disagree')} disagreement(s) with the oracle")
        for k in ("oracle_infrastructure_failures", "not_strict_generated",
                  "explain_mismatches"):
            if s_.get(k) != 0:
                fails.append(f"{label}: {k} = {s_.get(k)}")
        if s_.get("agree") != s_.get("graded"):
            fails.append(f"{label}: agree {s_.get('agree')} != graded {s_.get('graded')}")
        # 5. near-misses
        near = d.get("by_family", {}).get("L0-NEAR", {})
        if near.get("n", 0) != 0 or near.get("outside", 0) < MIN_NEAR:
            fails.append(f"{label}: near-misses: {near.get('n')} decided, "
                         f"{near.get('outside')} outside (need 0 and >= {MIN_NEAR})")

    dfs = files["bytes_differential"]
    if dfs.get("summary", {}).get("graded", 0) < MIN_BYTES_DIFFERENTIAL:
        fails.append(f"bytes_differential: graded {dfs.get('summary', {}).get('graded')} "
                     f"files, the floor is {MIN_BYTES_DIFFERENTIAL}")
    ub = dfs.get("summary", {}).get("upper_bound_95", {})
    if "not over L_S0" not in str(ub.get("scope", "")):
        fails.append("bytes_differential: the upper bound does not state that it is over "
                     "the generator's distribution, not over L_S0 (C-85)")
    rp = files["bytes_probes"]
    tc = rp.get("summary", {}).get("tree_bytes_consistency", {})
    if not tc.get("checked") or tc.get("agree") != tc.get("checked") \
            or rp.get("tree_bytes_differences"):
        fails.append(f"bytes_probes: the tree decider and the bytes decider differ on "
                     f"{(tc.get('checked') or 0) - (tc.get('agree') or 0)} phase-1 "
                     f"rendering(s) (of {tc.get('checked')})")

    # 2. every constructor attested
    fam = rp.get("by_family", {})
    lr = rp.get("lex_rules", {})
    for c in ctors:
        if c in UNREACHABLE:
            continue
        use = lr.get(c, {})
        if c in OUTSIDE_ONLY:
            if use.get("outside", 0) < 1:
                fails.append(f"bytes_probes: constructor {c} (outside the fragment) is used "
                             f"by no document decided outside")
            continue
        f = fam.get(c, {})
        if f.get("n", 0) < 1:
            fails.append(f"bytes_probes: no graded probe family for constructor {c}")
        elif f.get("agree") != f.get("n"):
            fails.append(f"bytes_probes: family {c}: {f['n'] - f['agree']} of {f['n']} "
                         f"probes disagree with the oracle")
        if use.get("graded_agree", 0) < 1:
            fails.append(f"bytes_probes: no agreeing graded probe used constructor {c}")

    # 6. reader branch matrix
    present = {CAT_NAMES[c] for c in cats}
    if 0 <= el <= 255:
        present.add(CAT_NAMES[cats[el]])
    classes_in, classes_out = set(), set()
    for cls in present:
        if cls == "escape":
            classes_in |= {"esc.word", "esc.sym"}
            classes_out |= {"esc.word.hathat", "esc.sym.hathat"}
        elif cls == "sup":
            classes_in.add("sup")
            classes_out.add("sup.hathat")
        elif cls in IN_CLASSES:
            classes_in.add(cls)
        elif cls in OUT_CLASSES:
            classes_out.add(cls)
    covered_in = {b for r in rp.get("documents", []) if r.get("agree")
                  for b in r.get("lex_branches", [])}
    covered_out = {b for r in rp.get("outside", []) for b in r.get("lex_branches", [])}
    miss = []
    for st in "NMS":
        miss += [f"{st}|{c}" for c in sorted(classes_in) if f"{st}|{c}" not in covered_in]
        miss += [f"{st}|{c} (outside)" for c in sorted(classes_out)
                 if f"{st}|{c}" not in covered_out | covered_in]
    miss += [c for c in sorted(FRONT_CELLS_IN) if c not in covered_in]
    for m in miss[:25]:
        fails.append(f"reader branch matrix: cell {m} is not exercised")
    if len(miss) > 25:
        fails.append(f"reader branch matrix: {len(miss)} cells missing in all")
    # the kernel's matrix at the byte level
    sem = (strict / "Semantics.v").read_text()
    syn = (strict / "Syntax.v").read_text()
    sigs = json.loads((repo / SIGNATURES).read_text()).get("signatures", {})
    need_ok, _, finds = required_cells(syn, sem, sigs)
    fails += [f"kernel matrix: {m}" for m in finds]
    kcov = {b for r in rp.get("documents", []) if r.get("agree") for b in r.get("branches", [])}
    # A `$` at the END of the kernel stream is outside the fragment at the byte
    # level (DecideBytes.in_strict_bytes: ends_dollar, checked in 8 below), so
    # its follower-eof cells are phase 1's only.
    kmiss = sorted(c for c in need_ok - kcov if not re.fullmatch(r"\w+\|dollar\|eof\|-", c))
    for cell in kmiss[:25]:
        fails.append(f"kernel branch matrix at the byte level: cell {cell} is not exercised "
                     f"by an agreeing byte-level probe")

    # 7. no name in Coq
    for f in PHASE2_FILES:
        code = strip_coq_comments(src[f])
        for lit in re.findall(r'"((?:[^"]|"")*)"', code):
            fails.append(f"proofs/Strict/{f}: string literal {lit!r} outside a comment "
                         f"(names reach the reader only through the lexical contract)")

    # 8. bounds
    for f, pin in (("Lexer.v", "Example max_line_bytes_is_10000 : max_line_bytes = "
                                "Nat.mul 100 100."),
                   ("DecideBytes.v", "Example max_file_bytes_is_1000000 : max_file_bytes = "
                                     "Nat.mul max_line_bytes 100.")):
        if pin not in src[f]:
            fails.append(f"{f}: missing the pin `{pin}`")
    import _strict_bytes as SB
    if (SB.MAX_LINE_BYTES, SB.MAX_FILE_BYTES) != (MAX_LINE_BYTES, MAX_FILE_BYTES):
        fails.append("_strict_bytes: MAX_LINE_BYTES/MAX_FILE_BYTES differ from the Coq pins")
    isb = " ".join(strip_coq_comments(src["DecideBytes.v"]).split())
    m = re.search(r"Definition in_strict_bytes \(C : bcontract\) \(b : list ascii\) : Prop :=(.*?)\. ",
                  isb)
    body = m.group(1) if m else ""
    for need in ("length b <= max_file_bytes", "Parse (bc_lex C) b ks",
                 "in_strict_toks (bc_kernel C) (toks_of ks)",
                 "bounded (toks_of ks) = true", "ends_dollar (toks_of ks) = false"):
        if need not in body:
            fails.append(f"DecideBytes.v: in_strict_bytes no longer requires `{need}`")
    b = fam.get("L0-bounds", {})
    if b.get("n", 0) < 9 or b.get("agree") != b.get("n"):
        fails.append(f"bytes_probes: L0-bounds {b.get('agree')}/{b.get('n')} agree "
                     f"(at least 9, all agreeing)")

    # 9. FaithfulBytes pinned
    fails += bridge_findings(src["BridgeBytes.v"])

    if fails:
        for m in fails:
            print(f"FAIL {m}")
        print(f"[strict-bytes] FAIL — {len(fails)} finding(s)")
        return 1
    ps, ds = rp["summary"], dfs["summary"]
    print(f"[strict-bytes] OK — {len(ctors)} reader constructors, each probe-tagged and "
          f"attested; {ps['graded']} byte-level probes and {ds['graded']} differential "
          f"files agree with the oracle (verdict, message, line); "
          f"{ps['outside_by_design'] + ds['outside_by_design']} files outside by design; "
          f"reader matrix {len(classes_in) * 3} + {len(classes_out) * 3} cells and the "
          f"kernel matrix's {len(need_ok)} covered at the byte level")
    return 0


if __name__ == "__main__":
    sys.exit(main())
