#!/usr/bin/env python3
"""Compare the model's meaning dump with the binary's, byte for byte, and both with the contract.

usage: meancompare.py --repo REPO --names NAMES.json --spec SPEC --model MODELDIR --bin BINDIR [--out SUMMARY.json]

MODELDIR is the model run's PS_DUMPDIR (handle-N files) holding driver.out (ps.exe's stdout);
BINDIR is the binary run's directory: out, err, rc, and w/ (the files it wrote: texput.log,
clock.log). Classes as in h2/diff/diff.py: IDENTICAL when the model exited with the binary's
status and its terminal output, standard error, every file it wrote and the number of clock
readings it used are byte-identical to the binary's (the model's file handles include the files it
only READ, the spec's `gzfile` paths: those are inputs, not outputs, and are left out); otherwise STUCK, LIMIT (no result) or
DIVERGENT. Each side's log is also reduced to the contract generator's meanings_sha256 (its own
parse_dump, as meandigest.py) and compared with the committed contract's. Exit 0 always: the
outcome is data (a CI job must not fail on a finding); exit 2 only on missing inputs."""
import hashlib
import json
import sys
from pathlib import Path


def opt(name):
    return sys.argv[sys.argv.index(name) + 1] if name in sys.argv else None


def sha(b):
    return hashlib.sha256(b).hexdigest()


def digest(repo, names_path, log_bytes, tmp):
    """The contract generator's meanings_sha256 of one log, computed by meandigest.py (which
    uses gen_contract's own parse_dump) in a separate process: this module only compares bytes
    and does not import the oracle's client code (check_oracle_infra_grading)."""
    import subprocess
    lp = Path(tmp)
    lp.write_bytes(log_bytes)
    r = subprocess.run([sys.executable, str(Path(__file__).resolve().parent / "meandigest.py"), str(repo),
                        str(names_path), str(lp)], capture_output=True, text=True, check=True)
    d = json.loads(r.stdout)
    return {"records": d["records"], "defined": d["defined"], "undefined": d["undefined"], "error": d["error"],
            "meanings_sha256": d["digest"]}


def main():
    import tempfile
    tmpd = tempfile.mkdtemp()
    repo, md, bd = Path(opt("--repo")), Path(opt("--model")), Path(opt("--bin"))
    contract = json.loads((repo / "corpora/contracts/kernel/aarch64-a476533c0d6e64f0.json").read_text())
    if not (bd / "rc").exists() or not (md / "driver.out").exists():
        print("missing inputs", file=sys.stderr)
        sys.exit(2)
    drv = (md / "driver.out").read_bytes().decode("latin-1")
    res = [l[len("RESULT: "):] for l in drv.splitlines() if l.startswith("RESULT: ")]
    res = res[-1] if res else "no result (the driver did not finish)"
    brc = int((bd / "rc").read_text().strip())
    bout, berr = (bd / "out").read_bytes(), (bd / "err").read_bytes()
    bfiles = {p.name: p.read_bytes() for p in (bd / "w").iterdir() if p.is_file() and p.name != "clock.log"}
    bclock = len((bd / "w" / "clock.log").read_text().splitlines()) if (bd / "w" / "clock.log").exists() else 0
    hnames = {}
    for l in drv.splitlines():
        if l.startswith("--- file handle "):
            h, _, nm = l[len("--- file handle "):].partition(" = ")
            hnames[h] = nm
    rd = lambda h: (md / f"handle-{h}").read_bytes() if (md / f"handle-{h}").exists() else b""
    inputs = {l.split(" ", 1)[1].split("=", 1)[0] for l in Path(opt("--spec")).read_text().splitlines()
              if l.startswith("gzfile ")}
    mfiles = {nm: rd(h) for h, nm in hnames.items() if not (nm in inputs and rd(h) == b"")}
    mclock = next((l.split()[4] for l in drv.splitlines() if l.startswith("--- clock readings used:")), None)
    out = {"model_result": res, "binary_rc": brc,
           "binary": {"stdout_sha256": sha(bout), "stderr_sha256": sha(berr), "clock_readings": bclock,
                      "files_sha256": {k: sha(v) for k, v in sorted(bfiles.items())}},
           "contract_meanings_sha256": contract["meanings_sha256"]}
    if "texput.log" in bfiles:
        out["binary"]["digest"] = digest(repo, opt("--names"), bfiles["texput.log"], Path(tmpd) / "binary.log")
        out["binary"]["digest_equals_contract"] = out["binary"]["digest"]["meanings_sha256"] == contract["meanings_sha256"]
    if res.startswith("exit "):
        mrc = int(res.split()[1])
        diffs = [x for x, bad in (("rc", mrc != brc), ("stdout", rd(1) != bout), ("stderr", rd(2) != berr),
                                  ("files", mfiles != bfiles), ("clock readings", mclock != str(bclock))) if bad]
        out["class"] = "IDENTICAL" if not diffs else "DIVERGENT"
        out["differs_in"] = diffs
        out["model"] = {"stdout_sha256": sha(rd(1)), "stderr_sha256": sha(rd(2)), "clock_readings": mclock,
                        "files_sha256": {k: sha(v) for k, v in sorted(mfiles.items())}}
        if "texput.log" in mfiles:
            out["model"]["digest"] = digest(repo, opt("--names"), mfiles["texput.log"], Path(tmpd) / "model.log")
            out["model"]["digest_equals_contract"] = out["model"]["digest"]["meanings_sha256"] == contract["meanings_sha256"]
    elif res.startswith("stuck"):
        out["class"] = "STUCK"
    else:
        out["class"] = "LIMIT"
    js = json.dumps(out, indent=1)
    if opt("--out"):
        Path(opt("--out")).write_text(js + "\n")
    print(js)


if __name__ == "__main__":
    main()
