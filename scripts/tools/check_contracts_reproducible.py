#!/usr/bin/env python3
"""Regenerate committed configuration contracts and diff them byte for byte.

The contract generator (scripts/tools/gen_contract.py, ADR-012 M1) is in the
trusted base (design section G.2, T4), and its validity rule is that a contract
is reproducible: regenerating it under the same pin must give the same bytes.
This gate regenerates each selected contract from the configuration recorded
inside it, rebuilding the kernel from INITEX (unless --cached-kernel), and
compares both the contract and the committed kernel-names file.

LOCAL / NIGHTLY ONLY. It needs docker and the pinned TeX Live image, and the
committed contracts record the image's architecture (arm64): CI's tex-oracle
job runs the same multi-arch digest on amd64, a separately built image whose
pdflatex.fmt has not been compared with the arm64 one. It is therefore not
wired into any workflow, and it refuses (exit 2) on an architecture other than
the contract's; wiring it needs that comparison first (an open item under
OPEN-116).

Exit codes: 0 every selected contract reproduced; 1 a difference (printed);
2 cannot check here (no docker, no image, or a different architecture) -
never read 2 as a pass.

Usage:
  check_contracts_reproducible.py [--repo .]                 article.json only
  check_contracts_reproducible.py --all                      every contract
  check_contracts_reproducible.py --contract corpora/contracts/amsart.json
"""
from __future__ import annotations

import argparse
import difflib
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import gen_contract as gc  # noqa: E402

DEFAULT = gc.CONTRACT_DIR / "article.json"


def _is_contract(p: Path) -> bool:
    try:
        return json.loads(p.read_text(encoding="utf-8")).get("schema") == gc.SCHEMA
    except (OSError, ValueError):
        return False


def _show_diff(a: Path, b: Path, limit: int = 40) -> None:
    la = a.read_text(encoding="utf-8").splitlines()
    lb = b.read_text(encoding="utf-8").splitlines()
    for n, line in enumerate(difflib.unified_diff(la, lb, str(a), "regenerated",
                                                  lineterm="", n=1)):
        if n >= limit:
            print("  ... (diff truncated)")
            break
        print("  " + line)


def adversarial(image: str, work: Path, cache: Path) -> int:
    """Kill-test of the two completeness guards: a preamble definer that hides
    a \\def from the trace must make the contract incomplete, through BOTH the
    tracing-toggle check and the closure self-check (given the hidden name as a
    use-name); the same use-names on the plain class must pass. Returns the
    number of failed expectations."""
    cfg_bad = {"class": "article", "preamble": [
        {"definer": "\\tracingassigns=0 \\def\\lphidden{x}\\tracingassigns=1"}]}
    cfg_ok = {"class": "article"}
    use = ["lphidden", "lpnotdefinedanywhere"]
    bad = 0
    with gc.Tex(image, work) as tex:
        pin = gc.get_pin(tex, image)
        kernel = gc.load_kernel(tex, pin, cache, False, {})
        c1 = gc.generate(cfg_bad, tex, pin, kernel, use, {})
        c2 = gc.generate(cfg_ok, tex, pin, kernel, use, {})
    r1 = " | ".join(c1["incomplete_reasons"])
    checks = [
        ("hidden \\def: contract incomplete", c1["complete"] is False),
        ("hidden \\def: tracing-toggle guard fires", "tracing was toggled" in r1),
        ("hidden \\def: self-check names it",
         [m["name"] for m in c1["self_check"]["mismatches"]] == ["lphidden"]),
        ("plain class with the same use-names: complete", c2["complete"] is True),
    ]
    for label, ok in checks:
        print("%s adversarial: %s" % ("OK  " if ok else "FAIL", label))
        bad += 0 if ok else 1
    return bad


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--repo", default=str(gc.REPO))
    ap.add_argument("--contract", action="append", default=[])
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--cached-kernel", action="store_true",
                    help="reuse the cached kernel instead of re-running INITEX")
    ap.add_argument("--work", default="~/.cache/lp-oracle/contracts/work")
    a = ap.parse_args(argv)
    repo = Path(a.repo).resolve()

    if shutil.which("docker") is None:
        print("check_contracts_reproducible: CANNOT CHECK - docker is not available "
              "(this is not a pass)")
        return 2
    image = gc.read_image(repo)
    if subprocess.run(["docker", "image", "inspect", image],
                      capture_output=True).returncode != 0:
        print("check_contracts_reproducible: CANNOT CHECK - the pinned image %s is "
              "not pulled (this is not a pass)" % image)
        return 2

    if a.all:
        paths = sorted(p for p in (repo / gc.CONTRACT_DIR).glob("*.json") if _is_contract(p))
    else:
        paths = [repo / p for p in (a.contract or [str(DEFAULT)])]
    if not paths:
        print("check_contracts_reproducible: no contracts selected")
        return 1

    work = Path(a.work).expanduser()
    work.mkdir(parents=True, exist_ok=True)
    tmp = Path(tempfile.mkdtemp(prefix="check-", dir=work))
    failures = 0
    cache = (tmp / "cache" if not a.cached_kernel
             else Path("~/.cache/lp-oracle/contracts/cache").expanduser())
    try:
        kernel_checked = set()
        for path in paths:
            committed = json.loads(path.read_text(encoding="utf-8"))
            with gc.Tex(image, work) as tex:
                pin = gc.get_pin(tex, image)
                if pin["arch"] != committed["pin"]["arch"]:
                    print("check_contracts_reproducible: CANNOT CHECK %s - it was generated "
                          "on %s and this image runs on %s (this is not a pass)"
                          % (path.name, committed["pin"]["arch"], pin["arch"]))
                    return 2
                report: dict = {}
                fresh = not a.cached_kernel and not kernel_checked
                kernel = gc.load_kernel(tex, pin, cache, fresh, report)
                use = committed.get("self_check", {}).get("use_names_list", [])
                contract = gc.generate(committed["configuration"], tex, pin, kernel, use,
                                       report)
                gc.attach_kernel_ref(contract, kernel, pin)
            out = tmp / path.name
            out.write_text(gc.canonical_json(contract), encoding="utf-8")
            if out.read_bytes() == path.read_bytes():
                print("OK   %s reproduced byte for byte (%d bytes)" % (
                    path.relative_to(repo), out.stat().st_size))
            else:
                failures += 1
                print("DIFF %s does not reproduce:" % path.relative_to(repo))
                _show_diff(path, out)
            kfile = repo / contract["kernel"]["file"]
            if kfile not in kernel_checked:
                kernel_checked.add(kfile)
                kout = tmp / ("kernel-" + kfile.name)
                kout.write_text(gc.canonical_json(gc.kernel_public(kernel, pin)),
                                encoding="utf-8")
                if kfile.exists() and kout.read_bytes() == kfile.read_bytes():
                    print("OK   %s reproduced byte for byte" % kfile.relative_to(repo))
                else:
                    failures += 1
                    print("DIFF %s does not reproduce%s" % (
                        kfile.relative_to(repo), "" if kfile.exists() else " (missing)"))
                    if kfile.exists():
                        _show_diff(kfile, kout)
        failures += adversarial(image, work, cache)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    if failures:
        print("check_contracts_reproducible: FAIL - %d file(s) did not reproduce" % failures)
        return 1
    print("check_contracts_reproducible: PASS - %d contract(s) reproduced" % len(paths))
    return 0


if __name__ == "__main__":
    sys.exit(main())
