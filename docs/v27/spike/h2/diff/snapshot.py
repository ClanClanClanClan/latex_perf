#!/usr/bin/env python3
"""The file-system snapshot of a differential run, measured in the pinned image.

The model's run identity includes what the run can see of the file system (Values.v fsent,
driver.ml's fs* lines): this tool measures it, in a container of the pinned image, with
stat(1)-like shell tests and GNU find, and never starts a TeX engine. Its output is a
`.snap` file of spec lines:

  fslist PATH=N1/N2/...   a directory and its complete listing (readdir's names without
                          . and ..; [ -d ] follows symbolic links, as stat(2) does)
  fsdir PATH              a directory, listing not measured
  fsfile PATH=@sha256:HEX a file test -e and not -d accept, whose bytes were copied out
                          (the container runs as root, so access(R_OK) succeeds: kpathsea's
                          READABLE); `diff.py prepare` materialises them, verifying HEX
  fsexists PATH           the same, bytes not copied
  fsabsent PATH           test -e fails (stat fails)

usage:
  snapshot.py measure --out FILE.snap --blobs DIR [--arch arm64|amd64] [--list P...] [--stat P...] [--content P...]
      --list: directories whose listing is recorded (a non-directory is recorded by type);
      --stat: type only; --content: a file whose bytes are recorded (into DIR/HEX).
      Paths must be canonical (absolute, no empty, '.' or '..' component).
  snapshot.py fetch --blobs DIR [--arch A] PATH=HEX...
      copies PATH out of the image again and checks its sha256 is HEX
"""
import hashlib
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

# a directory the container engine can mount (colima shares $HOME, not the system temp dir)
TMP = Path.home() / ".cache" / "lp-spike-snapshot-tmp"

IMAGE = "texlive/texlive@sha256:4984977ccf5afe883cb382d0163f267de0d029d140bb7a9e8f4c19f0b781d57b"


def mktmp():
    TMP.mkdir(parents=True, exist_ok=True)
    return TMP


def canonical(p):
    return p == "/" or (p.startswith("/") and "=" not in p and "\n" not in p
                        and all(c not in ("", ".", "..") for c in p.split("/")[1:]))


def q(s):
    return "'" + s.replace("'", "'\"'\"'") + "'"


def args_after(flag):
    a = sys.argv
    if flag not in a:
        return []
    i = a.index(flag) + 1
    out = []
    while i < len(a) and not a[i].startswith("--"):
        out.append(a[i])
        i += 1
    return out


def platform():
    a = sys.argv[sys.argv.index("--arch") + 1] if "--arch" in sys.argv else "arm64"
    if a not in ("arm64", "amd64"):
        sys.exit("--arch is arm64 or amd64")
    return "linux/" + a


def run_in_image(script, outdir):
    r = subprocess.run(["docker", "run", "--rm", "--platform", platform(), "--network", "none",
                        "-v", f"{outdir}:/o", IMAGE, "sh", "-c", script], capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(f"snapshot: the container failed: {r.stderr[-2000:]}")
    return r.stdout


def measure():
    out = Path(sys.argv[sys.argv.index("--out") + 1])
    blobs = Path(sys.argv[sys.argv.index("--blobs") + 1])
    lists, stats, contents = args_after("--list"), args_after("--stat"), args_after("--content")
    for p in lists + stats + contents:
        if not canonical(p):
            sys.exit(f"not a canonical path: {p!r}")
    lines = []
    with tempfile.TemporaryDirectory(dir=mktmp()) as td:
        sc = ["set -u"]
        for i, p in enumerate(lists):
            sc.append(f"if [ -d {q(p)} ]; then echo 'L {i}'; find {q(p)} -mindepth 1 -maxdepth 1 -printf '%f\\n' > /o/l{i}; "
                      f"elif [ -e {q(p)} ]; then echo 'F {i}'; else echo 'A {i}'; fi")
        for i, p in enumerate(stats):
            sc.append(f"if [ -d {q(p)} ]; then echo 'D {i}'; elif [ -e {q(p)} ]; then echo 'F {i}'; else echo 'A {i}'; fi")
        for i, p in enumerate(contents):
            sc.append(f"if [ -e {q(p)} ] && [ ! -d {q(p)} ]; then cp {q(p)} /o/c{i} && echo 'C {i}'; else echo 'N {i}'; fi")
        res = run_in_image("\n".join(sc), td).split("\n")
        ri = 0
        for i, p in enumerate(lists):
            k = res[ri].split()[0]; ri += 1
            if k == "L":
                names = (Path(td) / f"l{i}").read_text().split("\n")[:-1]
                if any(("/" in n) or n in ("", ".", "..") for n in names):
                    sys.exit(f"a name that cannot be recorded in {p}")
                lines.append(f"fslist {p}=" + "/".join(sorted(names)))
            else:
                lines.append(("fsexists " if k == "F" else "fsabsent ") + p)
        for i, p in enumerate(stats):
            k = res[ri].split()[0]; ri += 1
            lines.append({"D": "fsdir ", "F": "fsexists ", "A": "fsabsent "}[k] + p)
        blobs.mkdir(parents=True, exist_ok=True)
        for i, p in enumerate(contents):
            k = res[ri].split()[0]; ri += 1
            if k != "C":
                sys.exit(f"--content {p}: not a readable non-directory in the image")
            b = (Path(td) / f"c{i}").read_bytes()
            h = hashlib.sha256(b).hexdigest()
            (blobs / h).write_bytes(b)
            lines.append(f"fsfile {p}=@sha256:{h}")
    out.write_text(f"# measured by snapshot.py in {IMAGE}\n" + "".join(l + "\n" for l in lines))
    print(f"wrote {len(lines)} entries to {out}")


def fetch(blobs, pairs):
    """copy each PATH out of the image into blobs/HEX, checking the hash"""
    blobs.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=mktmp()) as td:
        sc = ["set -u"] + [f"cp {q(p)} /o/c{i}" for i, (p, _) in enumerate(pairs)]
        run_in_image("\n".join(sc), td)
        for i, (p, h) in enumerate(pairs):
            b = (Path(td) / f"c{i}").read_bytes()
            if hashlib.sha256(b).hexdigest() != h:
                sys.exit(f"{p}: the image's bytes do not have sha256 {h}")
            (blobs / h).write_bytes(b)


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    if sys.argv[1] == "measure":
        measure()
    elif sys.argv[1] == "fetch":
        fetch(Path(sys.argv[sys.argv.index("--blobs") + 1]),
              [tuple(a.split("=", 1)) for a in sys.argv[2:] if "=" in a and not a.startswith("--")])
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main()
