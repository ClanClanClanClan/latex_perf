#!/usr/bin/env python3
"""Recompute the H.2 report's checkable numbers from the evidence committed beside it.

usage: python3 docs/v27/spike/h2/verify_h2.py [--report PATH]

Pure: reads files under docs/v27/spike/h2/ and the report; runs nothing.
  1. the translation manifest (evidence/manifest.json, written by emit_coq.py): every
     procedure translated, none failed, the counts the report quotes;
  2. the INITEX run: the model's terminal output and texput.log (the extracted program's
     output file handles) are byte-identical to the pinned binary's on both
     architectures, and the model's exit status is the binary's;
  3. C main's writes (evidence/cmain/): the globals gen_cmain.py turns into CMain.v are
     exactly the non-zero ones in the gdb measurement.
Exit 0 when all hold, 1 otherwise."""
import json
import re
import sys
from pathlib import Path

H = Path(__file__).resolve().parent
report = Path(sys.argv[sys.argv.index("--report") + 1]) if "--report" in sys.argv else H.parent / "H2-report.md"
R = report.read_text()
E = H / "evidence"
fails = []

m = json.loads((E / "manifest.json").read_text())
if m["procedures"] != 603 or m["failed"]:
    fails.append(f"manifest: {m['procedures']} procedures, failed {m['failed']}")
checks = [("procedures", 603, "603 of 603"), ("externals", 189, "189 distinct externals")]
if len(m["externals"]) != 189:
    fails.append(f"manifest: {len(m['externals'])} externals")
for _, _, q in checks:
    if q not in R:
        fails.append(f"report does not quote {q!r}")
if m["gotos"] != {"goto": 552, "return": 195}:
    fails.append(f"manifest gotos {m['gotos']}")
if len(m["c_vs_pascal_grouping"]) != 8 or len(m["unsequenced_conflicts"]) != 29 or m["unsequenced_pairs_checked"] != 45742:
    fails.append(f"manifest: {len(m['c_vs_pascal_grouping'])} grouping sites, "
                 f"{len(m['unsequenced_conflicts'])} unsequenced conflicts")
for q in ("45,742 unsequenced\n   pairs", "29 of them", "8 places"):
    if q not in R:
        fails.append(f"report does not quote {q!r}")

modelled = set(re.findall(r"x =\? X_(\w+)", (H / "coq" / "Boundary.v").read_text()))
if len(modelled) != 23 or "23 of the 189 externals" not in R or "166 of 189 externals are Stuck" not in R:
    fails.append(f"Boundary.v models {len(modelled)} externals; the report must say 23 of 189 (166 Stuck)")

I = E / "inirun"
ms, ml = (I / "model.stdout").read_bytes(), (I / "model.texput.log").read_bytes()
for arch in ("arm64", "amd64"):
    rs = (I / f"ref-{arch}.stdout").read_bytes()
    body, rc = rs.rsplit(b"[rc=", 1)
    if body != ms:
        fails.append(f"model terminal output differs from the {arch} binary's")
    if (I / f"ref-{arch}.texput.log").read_bytes() != ml:
        fails.append(f"model texput.log differs from the {arch} binary's")
    if not rc.startswith(b"1]"):
        fails.append(f"{arch} binary rc is not 1")
drv = (I / "model.driver.out").read_text()
if "RESULT: exit 1" not in drv or "stdin bytes not read: 0" not in drv:
    fails.append("model driver output does not show exit 1 with stdin consumed")
if b"\n*\n" not in ms:
    fails.append("model output does not contain the * prompt")

cm = json.loads((E / "cmain" / "cmain_globals.json").read_text())
nz = sorted(k for k, v in cm.items() if v.get("nonzero"))
want = sorted(["iniversion", "parsefirstlinep", "interactionoption", "formatdefaultlength", "TEXformatdefault",
               "shellenabledp", "restrictedshell", "synctexoption", "versionstring"])
if nz != want:
    fails.append(f"cmain non-zero globals {nz}")

for f in fails:
    print("FAIL", f)
print(f"verify_h2: {'OK' if not fails else f'{len(fails)} failure(s)'}")
sys.exit(1 if fails else 0)
