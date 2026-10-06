#!/usr/bin/env python3
"""Check the H.2 report's numbers against the evidence committed beside it.

usage: python3 docs/v27/spike/h2/verify_h2.py [--report PATH]
       python3 docs/v27/spike/h2/verify_h2.py --reproduce translate [--src SRC]
       python3 docs/v27/spike/h2/verify_h2.py --reproduce model --ps PATH/ps.exe

PURE MODE (the default; what CI can run) CHECKS CONSISTENCY, NOT REPRODUCTION. It runs
nothing. It checks that the committed evidence agrees with itself, with the committed
sources and with the report:
  1. evidence/build/provenance.json names, by sha256, the committed sources the measured
     build was made from (every file of translate/ and coq/, driver.ml, pipeline.sh,
     provenance.py); each must still hash as recorded. An edit to the translator,
     Interp.v, Boundary.v or driver.ml after the measurement makes the evidence STALE:
     FAIL. The same for the C-main measurement (the build's input) and the manifest
     (one of the build's outputs).
  2. every committed model output names the measured ps.exe (its sha256), and the
     outputs hash as their run records say;
  3. the INITEX run: the model's terminal output, texput.log and exit status equal the
     binary's, per architecture configuration; the binary's real-clock control run gives
     the same bytes as its clock-shim run;
  4. the differential (diff/results-*.tsv): every row was run by the measured ps.exe; no
     DIVERGENT row; the counts the report quotes;
  5. the translation manifest, the C-main globals, and the report's quoted numbers.
What pure mode cannot see: evidence forged CONSISTENTLY (outputs, their recorded hashes
and provenance.json all edited together). That needs reproduction:

--reproduce translate  re-runs emit_coq.py and gen_cmain.py on the pinned inputs (the H.1
    rebuild tree, --src, default ~/.cache/lp-spike-h1/b-arm64/repo, whose input hashes
    must match provenance.json) and compares the generated tree, file by file, with the
    hashes in provenance.json, and the manifest with evidence/manifest.json.
--reproduce model  re-runs ps.exe (--ps; its sha256 must be provenance.json's) on the
    INITEX run's spec in both char configurations and compares every output byte with
    the committed evidence.
The binary side is re-run by the recipe in diff/README.md (the repository's
check_oracle_pin.py allows a TeX engine to be started only inside _oracle.py, so the
recipe is not committed as an executable). Exit 0 when all hold, 1 otherwise."""
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

H = Path(__file__).resolve().parent
sys.path.insert(0, str(H))
import provenance  # noqa: E402

E = H / "evidence"
fails = []


def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def opt(name, default=None):
    return sys.argv[sys.argv.index(name) + 1] if name in sys.argv else default


PROV = json.loads((E / "build" / "provenance.json").read_text())
INI = E / "inirun"
RUN = json.loads((INI / "run.json").read_text())
CONFIGS = ("arm64", "amd64")


def pure():
    report = Path(opt("--report", H.parent / "H2-report.md"))
    R = report.read_text()
    R1 = re.sub(r"\s+", " ", R)

    def quote(q):
        if re.sub(r"\s+", " ", q) not in R1:
            fails.append(f"the report does not quote {q!r}")

    # 1. sources, inputs and outputs of the measured build
    now = provenance.committed_sources()
    for f, h in sorted(PROV["sources"].items()):
        if now.get(f) != h:
            fails.append(f"STALE: {f} changed since the measured build (provenance.json); re-run pipeline.sh, "
                         f"re-measure, `provenance.py record`")
    for f in sorted(set(now) - set(PROV["sources"])):
        fails.append(f"STALE: {f} is not in the measured build's provenance")
    for n in ("cmain_globals.json", "cmain_globals2.json", "cmain_globals3.json"):
        if sha(E / "cmain" / n) != PROV["inputs"][f"evidence/cmain/{n}"]:
            fails.append(f"evidence/cmain/{n} is not the C-main measurement the build used")
    if sha(E / "manifest.json") != PROV["generated"].get("manifest.json"):
        fails.append("evidence/manifest.json is not the measured build's manifest")
    ps = PROV["ps_exe"]

    # 2-3. the INITEX run
    if RUN["ps_sha256"] != ps:
        fails.append("inirun/run.json: not run by the measured ps.exe")
    for name, h in RUN["sha256"].items():
        if sha(INI / name) != h:
            fails.append(f"inirun/{name} does not hash as run.json records")
    for a in CONFIGS:
        m = (INI / f"model-{a}.driver.out").read_text()
        rc = int((INI / f"ref-{a}.rc").read_text())
        if f"RESULT: exit {rc}" not in m or "stdin bytes not read: 0" not in m:
            fails.append(f"{a}: the model did not exit {rc} with stdin consumed")
        for part in ("stdout", "stderr", "texput.log"):
            if (INI / f"model-{a}.{part}").read_bytes() != (INI / f"ref-{a}.{part}").read_bytes():
                fails.append(f"{a}: the model's {part} differs from the binary's")
        for part in ("stdout", "texput.log"):
            if (INI / f"ref-realclock-{a}.{part}").read_bytes() != (INI / f"ref-{a}.{part}").read_bytes():
                fails.append(f"{a}: the binary's real-clock control {part} differs from its clock-shim run")
        if b"\n*" not in (INI / f"model-{a}.stdout").read_bytes():
            fails.append(f"{a}: the model's output does not contain the * prompt")

    # 4. the differential
    tot = {}
    for a in CONFIGS:
        rows = [l.split("\t") for l in (H / "diff" / f"results-{a}.tsv").read_text().splitlines()[1:]]
        ins = sorted(p.stem for p in (H / "diff" / "inputs").glob("*.tex"))
        if sorted(r[0] for r in rows) != ins:
            fails.append(f"diff/results-{a}.tsv does not have one row per committed input")
        for r in rows:
            if r[8] != ps[:16]:
                fails.append(f"diff/results-{a}.tsv {r[0]}: not run by the measured ps.exe")
            if r[1] == "DIVERGENT":
                fails.append(f"diff/results-{a}.tsv {r[0]}: DIVERGENT ({r[7]})")
            tot[(a, r[1])] = tot.get((a, r[1]), 0) + 1
        n = len(rows)
        quote(f"{a}: {n} inputs, {tot.get((a, 'IDENTICAL'), 0)} identical, {tot.get((a, 'STUCK'), 0)} Stuck, "
              f"{tot.get((a, 'LIMIT'), 0)} without a result, {tot.get((a, 'DIVERGENT'), 0)} divergent")

    # 5. manifest, C main, the boundary, the report's numbers
    m = json.loads((E / "manifest.json").read_text())
    if m["procedures"] != 603 or m["failed"]:
        fails.append(f"manifest: {m['procedures']} procedures, failed {m['failed']}")
    # the measured build is H.3 checkpoint 2's (h3/model.patch merged): TEXMFENGINENAME is a
    # string literal there, not an external, so 188 externals (H.2's build had 189)
    if len(m["externals"]) != 188:
        fails.append(f"manifest: {len(m['externals'])} externals")
    for q in ("603 of 603", "188 distinct externals", f"{m['ir_nodes']:,} IR nodes"):
        quote(q)
    if m["gotos"] != {"goto": 552, "return": 195}:
        fails.append(f"manifest gotos {m['gotos']}")
    nun, npairs = len(m["unsequenced_conflicts"]), m["unsequenced_pairs_checked"]
    if len(m["c_vs_pascal_grouping"]) != 8:
        fails.append(f"manifest: {len(m['c_vs_pascal_grouping'])} grouping sites")
    for q in (f"{npairs:,} unsequenced pairs", f"{nun} of them", "8 places"):
        quote(q)
    # the boundary step (H-boundary-report.md, checkpoints 1-2): 15 externals more than H.3's 43
    modelled = set(re.findall(r"x =\? X_(\w+)", (H / "coq" / "Boundary.v").read_text()))
    if len(modelled) != 58:
        fails.append(f"Boundary.v models {len(modelled)} externals")
    quote("58 of the 188 externals")
    quote("130 of 188 externals are Stuck")
    cm = json.loads((E / "cmain" / "cmain_globals.json").read_text())
    nz = sorted(k for k, v in cm.items() if v.get("nonzero"))
    want = sorted(["iniversion", "parsefirstlinep", "interactionoption", "formatdefaultlength", "TEXformatdefault",
                   "shellenabledp", "restrictedshell", "synctexoption", "versionstring"])
    if nz != want:
        fails.append(f"cmain non-zero globals {nz}")
    # the build's measured cost, as the report quotes it (from evidence/build/measure.tsv)
    rows = [l.split("\t") for l in (E / "build" / "measure.tsv").read_text().splitlines()[1:]]
    for st in ("coqc", "extraction", "ocamlopt"):
        r = [x for x in rows if x[0] == st]
        quote(f"{st}: {len(r)} file(s), {sum(float(x[3]) for x in r):.0f} s wall, peak {max(int(x[5]) for x in r)} MB")


def reproduce_translate():
    src = Path(opt("--src", os.path.expanduser("~/.cache/lp-spike-h1/b-arm64/repo")))
    W = src / "texk" / "web2c"
    ins = {"pdftex.p": src / "Work/texk/web2c/pdftex.p", "pdftexcoerce.h": src / "Work/texk/web2c/pdftexcoerce.h",
           "pdftex.pool": src / "Work/texk/web2c/pdftex.pool", "common.defines": W / "web2c/common.defines",
           "texmf.defines": W / "web2c/texmf.defines", "synctex.defines": W / "synctexdir/synctex.defines",
           "pdftex.defines": W / "pdftexdir/pdftex.defines"}
    for k, p in ins.items():
        if sha(p) != PROV["inputs"][k]:
            fails.append(f"input {k} at {p} is not the measured build's")
    with tempfile.TemporaryDirectory(dir=os.path.expanduser("~/.cache/lp-spike-h1")) as td:
        g = Path(td) / "gen"
        subprocess.run([sys.executable, str(H / "translate/emit_coq.py"), str(ins["pdftex.p"]), str(ins["common.defines"]),
                        str(ins["texmf.defines"]), str(ins["synctex.defines"]), str(ins["pdftex.defines"]),
                        "--coerce", str(ins["pdftexcoerce.h"]), "--pool", str(ins["pdftex.pool"]), "--out", str(g)],
                       check=True, capture_output=True)
        cm = subprocess.run([sys.executable, str(H / "translate/gen_cmain.py"), str(g / "manifest.json")]
                            + [str(E / "cmain" / n) for n in ("cmain_globals.json", "cmain_globals2.json",
                                                             "cmain_globals3.json")],
                            check=True, capture_output=True).stdout
        (g / "CMain.v").write_bytes(cm)
        t = provenance.tree(g.glob("*"))
        for f in sorted(set(t) | set(PROV["generated"])):
            if t.get(f) != PROV["generated"].get(f):
                fails.append(f"reproduce translate: generated {f} differs from the measured build's")
        if (g / "manifest.json").read_bytes() != (E / "manifest.json").read_bytes():
            fails.append("reproduce translate: manifest.json differs from evidence/manifest.json")
    print(f"reproduce translate: {len(PROV['generated']) - 1} generated files compared")


def reproduce_model():
    ps = Path(opt("--ps"))
    if sha(ps) != PROV["ps_exe"]:
        fails.append(f"reproduce model: {ps} is not the measured ps.exe")
        return
    for a in CONFIGS:
        with tempfile.TemporaryDirectory(dir=os.path.expanduser("~/.cache/lp-spike-h1")) as td:
            p = subprocess.run([str(ps), "4000000000", str(INI / f"model-{a}.spec"), str(INI / "stdin")],
                               capture_output=True, env=dict(os.environ, PS_DUMPDIR=td), timeout=1800)
            got = {"stdout": Path(td, "handle-1"), "texput.log": Path(td, "handle-3"), "stderr": Path(td, "handle-2")}
            for part, f in got.items():
                b = f.read_bytes() if f.exists() else b""
                if b != (INI / f"model-{a}.{part}").read_bytes():
                    fails.append(f"reproduce model {a}: {part} differs from the committed output")
            if f"RESULT: exit {(INI / f'ref-{a}.rc').read_text().strip()}" not in p.stdout.decode("latin-1"):
                fails.append(f"reproduce model {a}: not the committed exit status")
    print("reproduce model: the INITEX run re-run in both char configurations")


def main():
    what = opt("--reproduce")
    if what is None:
        pure()
        mode = "pure (consistency of the committed evidence; nothing re-run)"
    elif what == "translate":
        reproduce_translate()
        mode = "reproduce translate"
    elif what == "model":
        reproduce_model()
        mode = "reproduce model"
    else:
        sys.exit(__doc__)
    for f in fails:
        print("FAIL", f)
    print(f"verify_h2 [{mode}]: {'OK' if not fails else f'{len(fails)} failure(s)'}")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
