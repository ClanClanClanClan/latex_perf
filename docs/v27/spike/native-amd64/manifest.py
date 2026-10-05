#!/usr/bin/env python3
"""Hash every output of the H.1 architecture probes and the H.2 binary side into one manifest.

The same code reads both sides of the native-amd64 confirmation (owner decision E3,
../NATIVE-AMD64.md), so the two manifests have one layout:
  - the qemu side: the raw run directories the spike left in ~/.cache/lp-spike-h1/ (the runs
    whose summaries are committed in h1/archsem/probes/out/ and h2/diff/results-amd64.tsv);
  - the native side: the same directories, made by .github/workflows/spike-native-amd64.yml on
    a native x86_64 runner.
It only reads and hashes files; it starts no program.

usage: manifest.py --out FILE GROUP=KIND:DIR[:OUTFILE] ...
  KIND archsem  DIR holds the probe documents and one o-NAME/ directory per probe (the run.sh /
                run2.sh layout of h1/recipes.md); OUTFILE is the run's captured terminal output
       rot      DIR holds amd/ (the run's directory) and amd.rc (rot2's run.sh output)
       f7amd    DIR is f7amd.sh's /f7; OUTFILE is its captured output
       h2       DIR is the WORK of h2/diff/run_bin.zsh: NAME/bin/{out,err,rc,w/...} per input,
                and t0/realclock/{out,err,rc,w/...} (run_realclock.zsh)
"""
import hashlib
import json
import re
import sys
from pathlib import Path


def sha(p: Path) -> str:
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()


# The two declared masks (../NATIVE-AMD64.md says where each one may be applied):
#  coreline  drops the message coreutils' `timeout` prints when the child dumped core (with its
#            newline; it follows pdfTeX's unterminated last line, so it is not a line). Whether a
#            core is dumped is the HOST's setting (RLIMIT_CORE, kernel.core_pattern), not the
#            program's behaviour; the exit status (128 + signal) is compared unmasked.
#  date      replaces the INITEX banner's date and a `[YYYY/M/D/T]` message: only for the H.2
#            inputs whose run identity leaves pdfTeX on the REAL clock (time(), not the shim).
CORE_LINE = b"timeout: the monitored command dumped core"
DATE_RES = (re.compile(rb"\d{1,2} [A-Z]{3} \d{4} \d\d:\d\d"), re.compile(rb"\[\d{4}/\d{1,2}/\d{1,2}/\d+\]"))
MASK_MAX = 1 << 20


def masked(b: bytes) -> dict:
    core = b.replace(CORE_LINE + b"\n", b"")
    date = b
    for r in DATE_RES:
        date = r.sub(b"<MASKED>", date)
    return {"coreline": hashlib.sha256(core).hexdigest(), "date": hashlib.sha256(date).hexdigest()}


def entry(p: Path) -> dict:
    e = {"sha256": sha(p), "size": p.stat().st_size}
    if e["size"] <= MASK_MAX:
        e["masked"] = masked(p.read_bytes())
    if e["size"] <= 512:   # rc files, clock logs, short rc lines: compared by value
        e["text"] = p.read_bytes().decode("latin-1")
    return e


def files_under(d: Path) -> dict:
    return {str(p.relative_to(d)): entry(p)
            for p in sorted(d.rglob("*")) if p.is_file() and not p.is_symlink()}


def archsem(d: Path) -> dict:
    top = {p.name: sha(p) for p in d.iterdir() if p.is_file()}
    probes = {}
    for o in sorted(d.glob("o-*")):
        fs = files_under(o)
        for rel, v in fs.items():   # a copied input (cp $t *.jpg *.pdf o-$f/) is not an output
            v["input"] = top.get(rel) == v["sha256"]
        probes[o.name[2:]] = fs
    return {"inputs": top, "probes": probes}


def h2(d: Path) -> dict:
    out = {}
    for n in sorted(p.name for p in d.iterdir() if p.is_dir()):
        e = {}
        for sub in ("bin", "realclock"):
            if (d / n / sub).is_dir():
                e[sub] = files_under(d / n / sub)
        if e:
            out[n] = e
    return out


def main(argv):
    if "--out" not in argv:
        sys.exit(__doc__)
    i = argv.index("--out")
    out = Path(argv[i + 1])
    specs = argv[:i] + argv[i + 2:]
    m = {}
    for s in specs:
        g, _, rest = s.partition("=")
        kind, _, rest = rest.partition(":")
        d, _, of = rest.partition(":")
        d = Path(d).expanduser()
        if not d.is_dir():
            sys.exit(f"{g}: no directory {d}")
        if kind == "archsem":
            e = archsem(d)
        elif kind == "rot":
            e = {"files": files_under(d / "amd"), "rc_line": (d / "amd.rc").read_text()}
        elif kind == "f7amd":
            e = {"files": files_under(d)}
        elif kind == "h2":
            e = {"inputs": h2(d)}
        else:
            sys.exit(f"{g}: unknown kind {kind}")
        if of:
            p = Path(of).expanduser()
            e["outfile"] = {"sha256": sha(p), "text": p.read_text(errors="replace")}
        e["kind"] = kind
        m[g] = e
    out.write_text(json.dumps(m, indent=1, sort_keys=True) + "\n")
    print(f"wrote {out}: " + ", ".join(f"{g} ({m[g]['kind']})" for g in m))


if __name__ == "__main__":
    main(sys.argv[1:])
