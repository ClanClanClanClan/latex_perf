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

It also runs `adversarial`: kill-tests of every completeness guard (the
tracing-toggle and untraced-change checks, the closure self-check, and TeX's
own hash-table count, which must see one name dropped from the kernel's
candidates or from a contract's universe) and the repros of the 2026-09-27
adversarial reviews (null control sequence, a name holding `=`, set_in
through a group, a fatal only on the confirming pass, a date-dependent load,
the reviewers' 24 missing kernel names), and of the re-review's defect 1 (a
name created from the job's own .aux on pass 2, which only the later-pass
trace and TeX's count on the last pass can see).

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
    """Kill-tests of the completeness guards, and the reviewers' repros of
    2026-09-27, each asserting the KIND of outcome. Returns the number of
    failed expectations.

    - a definer that hides a \\def from the trace must make the contract
      incomplete through BOTH the tracing-toggle check and the self-check;
    - the hash-coverage check (TeX's own count) must see a name missing from
      the kernel's candidates: 1 for `topmark`, 24 for the reviewers' 24;
    - and a name missing from a contract's dumped universe;
    - the null control sequence, a name holding `=`, set_in through a group,
      a fatal that appears only on pass 2, and a load that depends on the
      date must each come out right;
    - a name created from the job's own .aux on pass 2 (lastpage's
      \\r@LastPage; a definer's \\AtEndDocument-written \\gdef of lpq7) must
      make the contract incomplete, named; and with the name dropped from the
      universe, TeX's count on the last pass must see it (1) where the
      pass-1 count sees nothing (the re-review's defect 1);
    - the reviewers' 24 names as use-names on plain article: complete, 0
      mismatches."""
    review = json.loads((gc.REPO / gc.CONTRACT_DIR / "parser_fixtures" /
                         "review_missing_names.json").read_text(encoding="utf-8"))["names"]
    art = {"class": "article"}
    bad = 0
    checks = []
    with gc.Tex(image, work) as tex:
        pin = gc.get_pin(tex, image)
        kernel = gc.load_kernel(tex, pin, cache, False, {})
        kuniv = [gc.name_bytes(n) for n in kernel["universe"]]

        # The name is a token of the definer, so it is in the dumped universe:
        # the untraced-change check names it.
        c = gc.generate({"class": "article", "preamble": [
            {"definer": "\\tracingassigns=0 \\def\\lphidden{x}\\tracingassigns=1"}]},
            tex, pin, kernel, ["lphidden", "lpnotdefinedanywhere"], {})
        r = " | ".join(c["incomplete_reasons"])
        checks += [
            ("hidden \\def: contract incomplete", c["complete"] is False),
            ("hidden \\def: tracing-toggle guard fires", "tracing was toggled" in r),
            ("hidden \\def: untraced-change guard names it",
             "without a traced assignment" in r and "lphidden" in r),
        ]
        # The name is built with \\romannumeral0, so it is in no file and no
        # trace: only the self-check and TeX's hash count can see it.
        c = gc.generate({"class": "article", "preamble": [
            {"definer": "\\tracingassigns=0 \\expandafter\\def\\csname lp\\romannumeral0 "
                        "hidden\\endcsname{x}\\tracingassigns=1"}]},
            tex, pin, kernel, ["lphidden", "lpnotdefinedanywhere"], {})
        r = " | ".join(c["incomplete_reasons"])
        checks += [
            ("constructed hidden name: self-check names it",
             [m["name"] for m in c["self_check"]["mismatches"]] == ["lphidden"]),
            ("constructed hidden name: TeX's hash count sees it",
             c["coverage"].get("uncovered") == 1 and "outside the dumped universe" in r),
        ]

        one = gc.hash_coverage(tex, "kill_cov1", b"", [n for n in kuniv if n != b"topmark"])
        all24 = gc.hash_coverage(tex, "kill_cov24", b"",
                                 [n for n in kuniv if gc.name_str(n) not in review])
        full = gc.hash_coverage(tex, "kill_cov0", b"", kuniv)
        checks += [
            ("coverage: the kernel universe is complete", full.get("uncovered") == 0),
            ("coverage: dropping topmark is seen (uncovered 1)", one.get("uncovered") == 1),
            ("coverage: dropping the reviewers' 24 is seen (uncovered 24)",
             all24.get("uncovered") == 24),
        ]

        eq = {"class": "article", "preamble": [
            {"definer": "\\expandafter\\def\\csname lpa=b\\endcsname{x}"}]}
        c = gc.generate(eq, tex, pin, kernel, [], {}, universe_filter=lambda n: n != b"lpa=b")
        checks.append(("coverage: a name missing from a contract's universe is seen",
                       c["complete"] is False and c["coverage"].get("uncovered") == 1 and
                       any("outside the dumped universe" in x
                           for x in c["incomplete_reasons"])))
        c = gc.generate(eq, tex, pin, kernel, [], {})
        checks.append(("= in a name: lpa=b defined, no bogus lpa, complete",
                       c["complete"] and "lpa=b" in c["defined_names"] and
                       "lpa" not in c["reverted_names"] and "lpa" not in c["defined_names"]))

        c = gc.generate({"class": "article", "preamble": [
            {"definer": "\\expandafter\\def\\csname\\endcsname{nullcs}"}]},
            tex, pin, kernel, [], {})
        checks.append(("null cs: defined as the empty name, nothing bogus, complete",
                       c["complete"] and "" in c["defined_names"] and
                       not {"csnameendcsname", "csname\\endcsname"} &
                       (set(c["reverted_names"]) | set(c["defined_names"]))))

        c = gc.generate({"class": "article", "preamble": [
            {"definer": "\\gdef\\lpset{a}"}, {"package": "amssymb"},
            {"definer": "\\AtBeginDocument{\\begingroup\\def\\lpset{c}\\endgroup}"}]},
            tex, pin, kernel, [], {})
        checks.append(("set_in: a group-local \\def undone at the group end does not win",
                       c["complete"] and c["defined_names"]["lpset"]["set_in"] == "definer:0"))

        c = gc.generate({"class": "article", "preamble": [{"definer":
            "\\makeatletter\\AtBeginDocument{\\@ifundefined{lpflag}{\\immediate\\write"
            "\\@auxout{\\gdef\\string\\lpflag{}}}{\\lpundefinedzz}}\\makeatother"}]},
            tex, pin, kernel, [], {})
        lo = c["load_outcome"]
        checks.append(("pass 2: a fatal on the confirming pass is a fatal load",
                       lo["status"] == "fatal" and lo["first_pass_rc"] == 0 and
                       lo["error_class"] == "undefined_cs" and lo["passes"] == 2))

        c = gc.generate({"class": "article", "preamble": [
            {"definer": "\\ifnum\\year>2000 \\lpundefinedyy\\fi"}]},
            tex, pin, kernel, [], {})
        checks.append(("date: attested under the real clock, flagged date-dependent",
                       c["load_outcome"]["status"] == "fatal" and
                       any(x.startswith("date_dependent_load")
                           for x in c["incomplete_reasons"])))

        # Re-review defect 1: a name the configuration's own .aux creates on
        # pass 2, in no source file. The completeness checks used to run on
        # pass 1 only, so both shapes came out complete=true without it.
        lastpage = {"class": "article", "preamble": [{"package": "lastpage"}]}
        lpq7 = {"class": "article", "preamble": [{"definer":
            "\\makeatletter\\AtEndDocument{\\immediate\\write\\@auxout{\\string"
            "\\expandafter\\string\\gdef\\string\\csname\\space lpq\\number7 "
            "\\string\\endcsname{}}}\\makeatother"}]}
        for label, cfg, nm in [("lastpage", lastpage, "r@LastPage"), ("lpq7", lpq7, "lpq7")]:
            # The later-pass trace puts the name in the universe, so the
            # pass-to-pass state comparison names it.
            c = gc.generate(cfg, tex, pin, kernel, [], {})
            r = " | ".join(c["incomplete_reasons"])
            checks.append(("%s: pass-2 name %s makes the contract incomplete, named" %
                           (label, nm), c["complete"] is False and
                           "pass_dependent_state" in r and nm in r and
                           c["coverage_last_pass"].get("uncovered") == 0))
            # Without it in the universe, only TeX's count on the LAST pass
            # (the .aux in place) sees it; the pass-1 count cannot.
            c = gc.generate(cfg, tex, pin, kernel, [], {},
                            universe_filter=lambda n, nm=nm: n != gc.name_bytes(nm))
            r = " | ".join(c["incomplete_reasons"])
            checks.append(("%s: last-pass hash count sees %s missing (uncovered 1), "
                           "the pass-1 count does not" % (label, nm),
                           c["complete"] is False and
                           c["coverage_last_pass"].get("uncovered") == 1 and
                           c["coverage"].get("uncovered") == 0 and
                           "on pass 2 holds 1 names outside" in r))

        c = gc.generate(art, tex, pin, kernel, review, {})
        checks.append(("the reviewers' 24 names on plain article: complete, 0 mismatches",
                       c["complete"] and c["self_check"]["mismatch_count"] == 0 and
                       c["self_check"]["use_names"] == 24))
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
