#!/usr/bin/env python3
"""Gate: the strict kernel L_S0 and its evidence describe each other (ADR-012 M2).

Pure: no TeX, no docker, no build. It reads the Coq sources, the committed
extraction and the committed, oracle-graded artefacts, and fails when they no
longer belong together:

  1. PROBE-TAGGED SEMANTICS (design §C.3 review rule: "every Runs constructor
     cites its probe family ids"). Every constructor of the inductive `Runs`
     in proofs/Strict/Semantics.v carries a `probe S0/<constructor>` comment,
     and corpora/strict_s0/rule_probes.json has that family with at least one
     graded probe, every one of which agrees with the oracle, and at least one
     whose run actually used the constructor. A constructor without a family,
     or a family whose documents all bypass it, is a rule nobody has tested.
  2. FRESH EVIDENCE. The rule probes, the differential and the signature file
     each record the sha256 of the extraction they ran
     (latex-parse/strict/strict_kernel_extracted.ml) and of the kernel/contract
     files they read; each must equal the committed file's. A semantics change
     without re-running the evidence fails here, the extraction's own drift
     from the proofs is check_extract_identity.py's (proof CI).
  3. NO DISAGREEMENT. The rule probes and the differential report 0
     disagreements and 0 oracle infrastructure failures, and the differential
     graded at least MIN_DIFFERENTIAL documents (the M2 phase-1 floor; ADR-012
     decision 6: any disagreement blocks a release).
  4. SIGNATURES ARE THE GENERATOR'S. Every signature names a member of the
     article closed world (contract_wf), and the candidate set is exactly the
     documented selection rule's (sha256 order of the closed world's control
     words minus par/begin/end, first n): nothing was added or dropped by
     hand.
  5. NO NAME IN COQ. Semantics.v, Contract.v, Bridge.v hold no string literal
     outside comments, and Decide.v only one-character literals (the fixed
     catcode classes); a control-word name can reach the kernel only through
     the contract parameter.

Run: python3 scripts/tools/check_strict_kernel.py [--repo .]
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

MIN_DIFFERENTIAL = 1000
STRUCTURAL = {"par", "begin", "end"}


def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def strip_coq_comments(text: str) -> str:
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("(*", i):
            depth += 1
            i += 2
        elif text.startswith("*)", i) and depth:
            depth -= 1
            i += 2
        else:
            if depth == 0:
                out.append(text[i])
            i += 1
    return "".join(out)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=".")
    args = ap.parse_args()
    repo = Path(args.repo).resolve()
    fails: list[str] = []

    sem = (repo / "proofs/Strict/Semantics.v").read_text()
    body = sem[sem.index("Inductive Runs"):]
    ctors = re.findall(r"^\|\s*(R_\w+)\s*:", body, re.M)
    if len(ctors) < 40:
        fails.append(f"Semantics.v: found {len(ctors)} Runs constructors; the parser "
                     f"of this gate is broken or the relation shrank")
    for c in ctors:
        pre = body[:body.index(f"| {c} :")]
        last_comment = pre[pre.rfind("(*"):]
        if f"probe S0/{c}" not in last_comment:
            fails.append(f"Semantics.v: constructor {c} has no `probe S0/{c}` comment "
                         f"directly above it")

    extract = repo / "latex-parse/strict/strict_kernel_extracted.ml"
    sig_path = repo / "corpora/contracts/strict/article-s0-signatures.json"
    contract_path = repo / "corpora/contracts/article.json"
    contract = json.loads(contract_path.read_text())
    kernel_path = repo / contract["kernel"]["file"]
    cur = {"kernel_sha256": sha(kernel_path), "contract_sha256": sha(contract_path)}
    ext_sha = sha(extract)

    def fresh(label: str, d: dict, want_sig: bool) -> None:
        if d.get("kernel_extract_sha256") != ext_sha:
            fails.append(f"{label}: ran another extraction (kernel_extract_sha256 "
                         f"{str(d.get('kernel_extract_sha256'))[:12]} != committed "
                         f"{ext_sha[:12]}); re-run it")
        for k, v in cur.items():
            if d.get("source", {}).get(k) != v:
                fails.append(f"{label}: source {k} is not the committed file's")
        if want_sig and d.get("signatures_sha256") != sha(sig_path):
            fails.append(f"{label}: ran another signature file; re-run it")

    sig = json.loads(sig_path.read_text())
    fresh("signatures", sig, False)
    rp = json.loads((repo / "corpora/strict_s0/rule_probes.json").read_text())
    fresh("rule_probes", rp, True)
    df = json.loads((repo / "corpora/strict_s0/differential_v1.json").read_text())
    fresh("differential_v1", df, True)

    fam = rp.get("by_family", {})
    for c in ctors:
        f = fam.get(c)
        if not f or f.get("n", 0) < 1:
            fails.append(f"rule_probes: no probe family for constructor {c}")
        elif f.get("agree") != f.get("n"):
            fails.append(f"rule_probes: family {c}: {f['n'] - f['agree']} of {f['n']} "
                         f"probes disagree with the oracle")
        elif f.get("exercised", 0) < 1:
            fails.append(f"rule_probes: family {c}: no probe's run used {c}")
    for label, d in (("rule_probes", rp), ("differential_v1", df)):
        s = d.get("summary", {})
        if s.get("disagree") != 0 or d.get("disagreements"):
            fails.append(f"{label}: {s.get('disagree')} disagreement(s) with the oracle")
        if s.get("oracle_infrastructure_failures") != 0:
            fails.append(f"{label}: {s.get('oracle_infrastructure_failures')} ungraded "
                         f"document(s) (oracle infrastructure failures)")
        if s.get("agree") != s.get("graded"):
            fails.append(f"{label}: agree {s.get('agree')} != graded {s.get('graded')}")
    if df.get("summary", {}).get("graded", 0) < MIN_DIFFERENTIAL:
        fails.append(f"differential_v1: graded {df.get('summary', {}).get('graded')} "
                     f"documents, the floor is {MIN_DIFFERENTIAL}")

    # 4. signatures: contract_wf and the selection rule
    kern = json.loads(kernel_path.read_text())
    members = set(kern["names"])
    for n, v in contract["defined_names"].items():
        (members.discard if v.get("kind") == "Undefined" else members.add)(n)
    for n in sig.get("signatures", {}):
        if n not in members:
            fails.append(f"signatures: {n!r} is not defined in the closed world")
    words = sorted((m for m in members if re.fullmatch(r"[A-Za-z]+", m)
                    and m not in STRUCTURAL),
                   key=lambda m: hashlib.sha256(m.encode()).hexdigest())
    want = set(words[:sig.get("selection", {}).get("n", -1)])
    got = set(sig.get("signatures", {})) | set(sig.get("rejected", {}))
    if want != got:
        fails.append(f"signatures: candidate set differs from the selection rule "
                     f"({len(got - want)} extra, {len(want - got)} missing)")
    if set(sig.get("signatures", {})) & set(sig.get("rejected", {})):
        fails.append("signatures: a name is both admitted and rejected")

    # 5. no name in Coq
    for f in ("Semantics.v", "Contract.v", "Bridge.v", "Decide.v"):
        code = strip_coq_comments((repo / "proofs/Strict" / f).read_text())
        for lit in re.findall(r'"((?:[^"]|"")*)"', code):
            if f == "Decide.v" and len(lit) == 1:
                continue
            fails.append(f"proofs/Strict/{f}: string literal {lit!r} outside a comment "
                         f"(names reach the kernel only through the contract)")

    if fails:
        for m in fails:
            print(f"FAIL {m}")
        print(f"[strict-kernel] FAIL — {len(fails)} finding(s)")
        return 1
    print(f"[strict-kernel] OK — {len(ctors)} Runs constructors, each probe-tagged and "
          f"attested; {rp['summary']['graded']} rule probes and "
          f"{df['summary']['graded']} differential documents agree with the oracle; "
          f"{len(sig['signatures'])} signatures by the selection rule")
    return 0


if __name__ == "__main__":
    sys.exit(main())
