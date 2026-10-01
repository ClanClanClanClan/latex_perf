#!/usr/bin/env python3
"""The H.2 differential: the extracted model against the pinned binary, input by input.

Review A of H.2 (2026-09-30) ran 153 INITEX inputs through both; this is that harness,
committed and re-runnable, and the seed of H.4's. Each input is a file of terminal bytes
(inputs/NAME.tex, given to `pdftex -ini` on standard input) with an optional
inputs/NAME.spec that changes the run's environment, kpathsea values or clock (below).

usage:
  diff.py prepare --arch {arm64,amd64} --work DIR
      for every input, DIR/NAME/model.spec (the model's run identity, driver.ml's SPEC)
      and DIR/NAME/docker.env (the same environment for the binary, one NAME=VALUE per
      line, plus LP_CLOCK for the clock shim); DIR/inputs.txt lists the names
  diff.py model --arch A --work DIR --ps PS.EXE [--jobs N] [--timeout S] [--only NAME...]
      runs the model on every prepared input: DIR/NAME/model/{driver.out,handle-*}
  (the binary side is the recipe in README.md: it starts the engine, which this
   repository's check_oracle_pin.py allows only inside _oracle.py)
  diff.py compare --arch A --work DIR [--write]
      classifies every input, prints the totals, and with --write records
      results-A.tsv beside this file (the committed per-input results)

The run's identity. base.spec holds what every input shares: the command line, the
environment variables the modelled externals read, the kpathsea values
setupboundvariable reads (evidence/inirun/kpsevars.txt, the pdftex column), and eight
clock readings. NAME.spec lines change it: `env N=V` sets, `unenv N` removes, `kpse N=V`
sets, and any `clock` line replaces all of base.spec's readings. An `env` line naming a
kpathsea variable must come with the `kpse` line for it (kpathsea reads the environment
first), or prepare refuses. `charsigned` is the architecture's: 0 for arm64, 1 for amd64.

Classes (compare):
  IDENTICAL  the model exited with the binary's status, and its terminal output, its
             standard error and every file it wrote are byte-identical to the binary's
  STUCK      the model is Stuck (outside the tier); its reason is recorded
  LIMIT      the model hit a resource limit or the time-out: no result
  DIVERGENT  the model exited, and something differs: a fidelity failure
"""
import hashlib
import json
import os
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

H = Path(__file__).resolve().parent
INPUTS = H / "inputs"
IMAGE = "texlive/texlive@sha256:4984977ccf5afe883cb382d0163f267de0d029d140bb7a9e8f4c19f0b781d57b"


def opt(name, default=None):
    return sys.argv[sys.argv.index(name) + 1] if name in sys.argv else default


def sha(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def parse_spec(text: str):
    items = []
    for line in text.splitlines():
        if not line or line.startswith("#"):
            continue
        k, _, rest = line.partition(" ")
        items.append((k, rest))
    return items


def names():
    return sorted(p.stem for p in INPUTS.glob("*.tex"))


def prepare(arch, work):
    base = parse_spec((H / "base.spec").read_text())
    kpse_names = {r.split("=", 1)[0] for k, r in base if k == "kpse"} | \
        {l.split("=", 1)[0] for l in (H.parent / "evidence/inirun/kpsevars.txt").read_text().splitlines()}
    work.mkdir(parents=True, exist_ok=True)
    for n in names():
        spec = list(base)
        extra = INPUTS / f"{n}.spec"
        if extra.exists():
            ex = parse_spec(extra.read_text())
            if any(k == "clock" for k, _ in ex):
                spec = [(k, r) for k, r in spec if k != "clock"]
            for k, r in ex:
                if k in ("env", "kpse"):
                    nm = r.split("=", 1)[0]
                    spec = [(k2, r2) for k2, r2 in spec if not (k2 == k and r2.split("=", 1)[0] == nm)]
                    if k == "env" and nm in kpse_names and not any(
                            k3 == "kpse" and r3.split("=", 1)[0] == nm for k3, r3 in ex):
                        sys.exit(f"{n}.spec: env {nm} is a kpathsea variable; give its kpse line too")
                    spec.append((k, r))
                elif k == "unenv":
                    spec = [(k2, r2) for k2, r2 in spec if not (k2 == "env" and r2.split("=", 1)[0] == r)]
                elif k == "clock":
                    spec.append((k, r))
                else:
                    sys.exit(f"{n}.spec: unknown key {k}")
        spec.append(("charsigned", "1" if arch == "amd64" else "0"))
        d = work / n
        d.mkdir(exist_ok=True)
        (d / "model.spec").write_text("".join(f"{k} {r}\n" for k, r in spec))
        clock = ",".join(r.replace(" ", ".", 1) for k, r in spec if k == "clock")
        for k, r in spec:   # the shim reads SEC.USEC: USEC must be the 6-digit fraction
            if k == "clock":
                s, u = r.split(" ")
                if not (u.isdigit() and len(u) == 6):
                    sys.exit(f"{n}: clock {r}: write tv_usec with exactly 6 digits")
        env = [r for k, r in spec if k == "env"] + ([f"LP_CLOCK={clock}"] if clock else [])
        (d / "docker.env").write_text("".join(e + "\n" for e in env))
        (d / "stdin").write_bytes((INPUTS / f"{n}.tex").read_bytes())
    (work / "inputs.txt").write_text("".join(n + "\n" for n in names()))
    (work / "prepared.json").write_text(json.dumps({"arch": arch, "image": IMAGE}) + "\n")
    print(f"prepared {len(names())} inputs for {arch} in {work}")


def run_model(arch, work, ps, jobs, timeout, only):
    todo = only or (work / "inputs.txt").read_text().split()
    ps_sha = sha(Path(ps).read_bytes())

    def one(n):
        d = work / n
        m = d / "model"
        m.mkdir(exist_ok=True)
        for f in m.glob("handle-*"):
            f.unlink()
        env = dict(os.environ, PS_DUMPDIR=str(m), PS_PROCNAMES=str(Path(ps).parent.parent / "procnames.txt"))
        t0 = time.time()
        try:
            p = subprocess.run([ps, "4000000000", str(d / "model.spec"), str(d / "stdin")],
                               capture_output=True, env=env, timeout=timeout)
            out, rc = p.stdout + p.stderr, p.returncode
        except subprocess.TimeoutExpired as e:
            out, rc = (e.stdout or b"") + b"\nRESULT: model resource limit: time-out\n", -1
        wall = time.time() - t0
        (m / "driver.out").write_bytes(out)
        (m / "run.json").write_text(json.dumps({"ps_sha256": ps_sha, "rc": rc, "wall_s": round(wall, 2),
                                                "load1": os.getloadavg()[0]}) + "\n")
        return n, wall

    with ThreadPoolExecutor(jobs) as ex:
        for n, w in ex.map(one, todo):
            print(f"{n} {w:.1f}s", flush=True)


def result_line(drv: str) -> str:
    rs = [l for l in drv.splitlines() if l.startswith("RESULT: ")]
    return rs[-1][len("RESULT: "):] if rs else "no result (driver failed)"


def compare(arch, work, write):
    rows = []
    for n in (work / "inputs.txt").read_text().split():
        d = work / n
        m, b = d / "model", d / "bin"
        drv = (m / "driver.out").read_bytes().decode("latin-1")
        res = result_line(drv)
        ps_sha = json.loads((m / "run.json").read_text())["ps_sha256"]
        brc = int((b / "rc").read_text().strip())
        bfiles = {p.name: p.read_bytes() for p in (b / "w").iterdir() if p.is_file() and p.name != "clock.log"}
        bclock = len((b / "w" / "clock.log").read_text().splitlines()) if (b / "w" / "clock.log").exists() else 0
        bout, berr = (b / "out").read_bytes(), (b / "err").read_bytes()
        # the model's handles: 1 stdout, 2 stderr, >= 3 files named in driver.out
        hnames = {}
        for l in drv.splitlines():
            if l.startswith("--- file handle "):
                h, _, nm = l[len("--- file handle "):].partition(" = ")
                hnames[h] = nm
        rd = lambda h: (m / f"handle-{h}").read_bytes() if (m / f"handle-{h}").exists() else b""
        mfiles = {nm: rd(h) for h, nm in hnames.items()}
        mclock = next((l.split()[4] for l in drv.splitlines() if l.startswith("--- clock readings used:")), "?")
        if res.startswith("exit "):
            same = (int(res.split()[1]) == brc and rd(1) == bout and rd(2) == berr and mfiles == bfiles)
            cls = "IDENTICAL" if same else "DIVERGENT"
            why = "" if same else ";".join(
                x for x, bad in (("rc", int(res.split()[1]) != brc), ("stdout", rd(1) != bout),
                                 ("stderr", rd(2) != berr), ("files", mfiles != bfiles)) if bad)
        elif res.startswith("stuck"):
            # the procedure chain, by name (the driver prints numbers when it has no names)
            names = json.loads((H.parent / "evidence" / "manifest.json").read_text())["proc_names"]
            parts = res[len("stuck: "):].split(" > ")
            why = " > ".join(names[int(x)] if x.isdigit() else x for x in parts)
            cls = "STUCK"
        else:
            cls, why = "LIMIT", res
        if cls == "IDENTICAL" and mclock != str(bclock):
            cls, why = "DIVERGENT", f"clock readings used: model {mclock}, binary {bclock}"
        rows.append([n, cls, str(brc), res.split(":")[0] if cls != "IDENTICAL" else res, sha(bout)[:16],
                     ",".join(f"{k}={sha(v)[:16]}" for k, v in sorted(bfiles.items())) or "-",
                     f"{bclock}", why.replace("\t", " "), ps_sha[:16]])
    tot = {}
    for r in rows:
        tot[r[1]] = tot.get(r[1], 0) + 1
    print(arch, len(rows), "inputs:", ", ".join(f"{k} {v}" for k, v in sorted(tot.items())))
    for r in rows:
        if r[1] in ("DIVERGENT", "LIMIT"):
            print("  ", r[1], r[0], r[7])
    if write:
        hdr = ["input", "class", "binary_rc", "model_result", "binary_stdout_sha256_16",
               "binary_files_sha256_16", "binary_clock_readings", "reason", "ps_exe_sha256_16"]
        (H / f"results-{arch}.tsv").write_text("\t".join(hdr) + "\n" + "".join("\t".join(r) + "\n" for r in rows))
        print("wrote", H / f"results-{arch}.tsv")


def main():
    cmd, arch, work = sys.argv[1], opt("--arch"), Path(opt("--work", ""))
    if arch not in ("arm64", "amd64") or not str(work):
        sys.exit(__doc__)
    if cmd == "prepare":
        prepare(arch, work)
    elif cmd == "model":
        only = sys.argv[sys.argv.index("--only") + 1:] if "--only" in sys.argv else None
        run_model(arch, work, opt("--ps"), int(opt("--jobs", "4")), int(opt("--timeout", "900")), only)
    elif cmd == "compare":
        compare(arch, work, "--write" in sys.argv)
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main()
