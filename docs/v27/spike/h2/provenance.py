#!/usr/bin/env python3
"""Provenance of an H.2 build: what went in, what came out, by sha256 (review B, MEDIUM-1).

usage:
  provenance.py write   --src SRC --out OUT   after pipeline.sh: OUT/provenance.json
  provenance.py summary --out OUT             totals of OUT/measure.tsv, as the report quotes them
  provenance.py record  --out OUT             copy provenance.json and measure.tsv into
                                              evidence/build/ (the committed measurement)

provenance.json binds a build to
  - its inputs: the tangled pdftex.p, web2c's four .defines, pdftexcoerce.h, pdftex.pool
    (from the H.1 rebuild of r78081) and the committed C-main measurement;
  - the committed sources that made it: every file of translate/ and coq/ (driver.ml
    included), pipeline.sh and this file;
  - what it made: every generated Coq file (gen/), every extracted OCaml file, ps.exe;
  - the tools: coqc and ocamlopt versions.
verify_h2.py checks that the committed sources still hash as recorded here, and that every
committed model output names this ps.exe: an edit to the translator, Interp.v, Boundary.v
or the C-main values after the measurement makes the evidence STALE, and verify says so."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

H = Path(__file__).resolve().parent


def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def tree(files) -> dict:
    files = sorted(files, key=lambda p: p.name)
    d = {p.name: sha(p) for p in files}
    d["_tree"] = hashlib.sha256("".join(f"{k} {v}\n" for k, v in d.items()).encode()).hexdigest()
    return d


def committed_sources() -> dict:
    fs = sorted(list((H / "translate").glob("*.py")) + list((H / "coq").glob("*.v"))
                + [H / "coq" / "driver.ml", H / "pipeline.sh", H / "provenance.py"])
    return {str(p.relative_to(H)): sha(p) for p in fs}


def arg(name):
    return sys.argv[sys.argv.index(name) + 1]


def main():
    cmd = sys.argv[1]
    out = Path(arg("--out"))
    if cmd == "write":
        src = Path(arg("--src"))
        W = src / "texk" / "web2c"
        inputs = {
            "pdftex.p": src / "Work/texk/web2c/pdftex.p",
            "common.defines": W / "web2c/common.defines",
            "texmf.defines": W / "web2c/texmf.defines",
            "synctex.defines": W / "synctexdir/synctex.defines",
            "pdftex.defines": W / "pdftexdir/pdftex.defines",
            "pdftexcoerce.h": src / "Work/texk/web2c/pdftexcoerce.h",
            "pdftex.pool": src / "Work/texk/web2c/pdftex.pool",
        }
        for n in ("cmain_globals.json", "cmain_globals2.json", "cmain_globals3.json"):
            inputs[f"evidence/cmain/{n}"] = H / "evidence" / "cmain" / n
        ver = lambda c: subprocess.run(c, capture_output=True, text=True).stdout.strip().splitlines()[0]
        prov = {
            "inputs": {k: sha(p) for k, p in inputs.items()},
            "sources": committed_sources(),
            "generated": tree((out / "gen").glob("*")),
            "extracted": tree(p for p in (out / "build" / "new_ml").glob("*") if p.name != "driver.ml"),
            "ps_exe": sha(out / "build" / "ps.exe"),
            "tools": {"coqc": ver(["coqc", "--version"]), "ocamlopt": ver(["ocamlfind", "ocamlopt", "-version"])},
        }
        (out / "provenance.json").write_text(json.dumps(prov, indent=1, sort_keys=True) + "\n")
        print(f"provenance: ps.exe {prov['ps_exe'][:12]}, generated tree {prov['generated']['_tree'][:12]}")
    elif cmd == "summary":
        rows = [l.split("\t") for l in (out / "measure.tsv").read_text().splitlines()[1:]]
        for st in ("translate", "coqc", "extraction", "ocamlopt", "link"):
            r = [x for x in rows if x[0] == st]
            if not r:
                continue
            big = max(r, key=lambda x: float(x[3]))
            print(f"{st}: {len(r)} step(s), wall {sum(float(x[3]) for x in r):.1f} s, "
                  f"user {sum(float(x[4]) for x in r):.1f} s, peak RSS {max(int(x[5]) for x in r)} MB, "
                  f"longest {big[1]} {float(big[3]):.1f} s, load {min(x[6] for x in r)}-{max(x[6] for x in r)}")
    elif cmd == "record":
        dst = H / "evidence" / "build"
        dst.mkdir(exist_ok=True)
        for n in ("provenance.json", "measure.tsv"):
            (dst / n).write_bytes((out / n).read_bytes())
        print(f"recorded into {dst}")
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main()
