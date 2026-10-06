#!/usr/bin/env python3
"""Grow a run's file-system snapshot from the model's own questions (boundary step).

The model is Stuck on every question its snapshot does not decide, and says which path it asked
about ("the file-system snapshot does not decide P", "... does not hold the bytes of P", "... the
listing of P"). This tool runs the model, measures that one path in the pinned image with
snapshot.py (a directory: its listing; a file: its bytes; else: absent), adds the entry, and runs
again, until the model ends for another reason. It never starts a TeX engine; it only answers,
from the image, the questions the model asks, so the snapshot holds what the run reads and
nothing is assumed.

usage: snapgrow.py --ps PS.EXE --spec SPEC --stdin FILE --snap SNAP --blobs DIR [--arch A]
                   [--max N] [--timeout S] [--cap-mb M] [--out DIR]
  SPEC  the run's identity without its snapshot additions (fsfile lines may use @sha256:HEX)
  SNAP  the snapshot lines grown so far (created if absent; one spec line each)
  The model runs as `PS 4000000000 SPEC+SNAP FILE` with PS_DUMPDIR=DIR/run (default
  ~/.cache/lp-spike-h1/hb/grow), under h3/tools/capped.sh with --cap-mb (default 4000) and
  --timeout; its last result is printed.
"""
import hashlib
import os
import re
import subprocess
import sys
from pathlib import Path

H = Path(__file__).resolve().parent


def opt(name, default=None):
    return sys.argv[sys.argv.index(name) + 1] if name in sys.argv else default


def resolve(lines, blobs):
    out = []
    for l in lines:
        if l.startswith("fsfile ") and "=@sha256:" in l:
            p, h = l[len("fsfile "):].split("=@sha256:")
            b = blobs / h
            if hashlib.sha256(b.read_bytes()).hexdigest() != h:
                sys.exit(f"{b}: not the recorded bytes")
            l = f"fsfile {p}={b}"
        out.append(l)
    return out


def measure(kind, path, arch, blobs, tmp):
    snap = tmp / "one.snap"
    cmd = [sys.executable, str(H / "snapshot.py"), "measure", "--out", str(snap), "--blobs", str(blobs),
           "--arch", arch, kind, path]
    subprocess.run(cmd, check=True, capture_output=True)
    return [l for l in snap.read_text().splitlines() if l and not l.startswith("#")]


def main():
    ps, spec, stdin = opt("--ps"), Path(opt("--spec")), Path(opt("--stdin"))
    snapf, blobs, arch = Path(opt("--snap")), Path(opt("--blobs")), opt("--arch", "arm64")
    out = Path(opt("--out", os.path.expanduser("~/.cache/lp-spike-h1/hb/grow")))
    nmax, timeout = int(opt("--max", "200")), int(opt("--timeout", "1800"))
    out.mkdir(parents=True, exist_ok=True)
    snap = [l for l in snapf.read_text().splitlines() if l] if snapf.exists() else []
    for it in range(nmax):
        full = out / "spec"
        full.write_text("".join(l + "\n" for l in resolve(spec.read_text().splitlines(), blobs) + resolve(snap, blobs)))
        rd = out / "run"
        rd.mkdir(exist_ok=True)
        for f in rd.glob("handle-*"):
            f.unlink()
        # the model runs under h3/tools/capped.sh (CAP MB, default 4000), with standard input given
        cap = out / "cap"
        subprocess.run(["zsh", str(H.parent.parent / "h3/tools/capped.sh"), opt("--cap-mb", "4000"), str(timeout), str(cap),
                        "sh", "-c", 'exec "$0" 4000000000 "$1" "$2" < "$2"', ps, str(full), str(stdin)],
                       env=dict(os.environ, PS_DUMPDIR=str(rd)), check=True)
        stdout = (cap / "stdout").read_bytes()
        (rd / "driver.out").write_bytes(stdout)
        (rd / "verdict").write_text((cap / "verdict").read_text())
        res = [l for l in stdout.decode("latin-1").splitlines() if l.startswith("RESULT: ")]
        res = res[-1] if res else "RESULT: none"
        m = re.search(r"the file-system snapshot does not (decide|hold the bytes of|hold the listing of) (/\S*)", res)
        if not m:
            print(f"iteration {it}: {res}")
            snapf.write_text("".join(l + "\n" for l in snap))
            return
        what, path = m.group(1), m.group(2)
        key = lambda l: l.split(" ", 1)[1].split("=", 1)[0]
        if what == "decide":
            new = measure("--list", path, arch, blobs, out)
            if new and new[0].startswith("fsexists "):
                new = measure("--content", path, arch, blobs, out)
        elif what == "hold the bytes of":
            new = measure("--content", path, arch, blobs, out)
        else:
            new = measure("--list", path, arch, blobs, out)
        snap = [l for l in snap if key(l) != path] + new
        snapf.write_text("".join(l + "\n" for l in snap))
        print(f"iteration {it}: {what} {path} -> {new[0][:100]}", flush=True)
    print("stopped after --max iterations")


if __name__ == "__main__":
    main()
