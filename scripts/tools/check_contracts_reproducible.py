#!/usr/bin/env python3
"""Regenerate committed configuration contracts and diff them byte for byte.

The contract generator (scripts/tools/gen_contract.py, ADR-012 M1) is in the
trusted base (design section G.2, T4), and its validity rule is that a contract
is reproducible: regenerating it under the same pin must give the same bytes.
This gate regenerates each selected contract from the configuration recorded
inside it, rebuilding the kernel from INITEX (unless --cached-kernel), and
compares both the contract and the committed kernel-names file.

LOCAL / NIGHTLY ONLY. It needs the oracle (_oracle.py: docker and the pinned
image), and the committed contracts record the image's architecture (arm64): CI's tex-oracle
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
trace and TeX's count on a later pass can see), and of re-review 2 (a
name defined only on pass 3, after a failing pass 1; a date or job-name
dependence that reaches the state on pass 2 through the .aux).

Exit codes: 0 every selected contract reproduced; 1 a difference (printed);
2 cannot check here (no docker, no image, or a different architecture) -
never read 2 as a pass.

Usage:
  check_contracts_reproducible.py [--repo .]                 article.json only
  check_contracts_reproducible.py --all                      every contract
  check_contracts_reproducible.py --contract corpora/contracts/amsart.json
  check_contracts_reproducible.py --signatures               + article's signature sidecar

M1 slice 2 adds kill-tests of the signature probes (contract_signatures.py):
shapes whose \\meaning misleads (a wrapper of a one-argument macro reads as
arity 0; an optional argument; a star flag; a delimited parameter; a brace
group taken only by a peek; a text-only body) must come out as they behave,
and probe_names must answer from its cache without TeX.
"""
from __future__ import annotations

import argparse
import difflib
import json
import shutil
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
      universe, TeX's count on pass 2 must see it (1) where the pass-1 count
      sees nothing (the re-review's defect 1);
    - re-review 2: a name defined from pass 3 on (thirdB: after F S, the
      protocol's graded pass 3) must make the contract incomplete, named on
      pass 3 and not on pass 2; a digit-built one dropped from the universe
      (thirdB2) must be seen by TeX's count on passes 3 and 4 only, labelled
      with those passes; a date (dateC) or job name (jobD) that reaches the
      state through the .aux on pass 2 must make it incomplete, named;
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
        def cov_at(c, hist, env="forced", jobname="job"):
            hit = [x for x in c.get("coverage_passes", []) if x["history"] == hist and
                   x["env"] == env and x["jobname"] == jobname]
            return hit[0].get("uncovered") if len(hit) == 1 else None

        def all_cov_zero(c):
            return bool(c.get("coverage_passes")) and all(
                x.get("uncovered") == 0 for x in c["coverage_passes"])

        for label, cfg, nm in [("lastpage", lastpage, "r@LastPage"), ("lpq7", lpq7, "lpq7")]:
            # The later-pass trace puts the name in the universe, so the
            # pass-to-pass state comparison names it.
            c = gc.generate(cfg, tex, pin, kernel, [], {})
            r = " | ".join(c["incomplete_reasons"])
            checks.append(("%s: pass-2 name %s makes the contract incomplete, named" %
                           (label, nm), c["complete"] is False and
                           "pass_dependent_state" in r and nm in r and all_cov_zero(c)))
            # Without it in the universe, only TeX's count on a later pass
            # (the .aux in place) sees it; the pass-1 count cannot.
            c = gc.generate(cfg, tex, pin, kernel, [], {},
                            universe_filter=lambda n, nm=nm: n != gc.name_bytes(nm))
            r = " | ".join(c["incomplete_reasons"])
            checks.append(("%s: the pass-2 hash count sees %s missing (uncovered 1), "
                           "the pass-1 count does not" % (label, nm),
                           c["complete"] is False and cov_at(c, "S") == 1 and
                           cov_at(c, "none") == 0 and c["coverage"].get("uncovered") == 0
                           and "on pass 2 after history S holds 1 names outside" in r))

        # Re-review 2 (2026-09-27): the checks covered passes 1 and 2 only,
        # but the protocol grades pass 3 after a failing pass 1 (F S S) and
        # pass 4 after two (F F S S). thirdB: a counter the .aux carries from
        # pass to pass defines lpthird from pass 3 on.
        cnt = ("\\makeatletter\\newcount\\lpc\\def\\lpcnt#1{\\global\\lpc=#1\\relax}"
               "\\AtBeginDocument{\\ifnum\\lpc>1 %s\\fi\\immediate\\write\\@auxout"
               "{\\string\\lpcnt{\\the\\numexpr\\lpc+1\\relax}}}\\makeatother")
        third_b = {"class": "article", "preamble": [{"definer": cnt % "\\gdef\\lpthird{}"}]}
        c = gc.generate(third_b, tex, pin, kernel, [], {})
        r = " | ".join(c["incomplete_reasons"])
        checks.append(("thirdB: a name defined from pass 3 on makes the contract "
                       "incomplete, named on pass 3 after F S, not on pass 2",
                       c["complete"] is False and "lpthird" not in c["defined_names"] and
                       "pass 3 after history FS differs from pass 1: ['lpthird']" in r and
                       "pass 2 after history S differs" not in r and all_cov_zero(c)))
        # thirdB2: the name is built from digits (lpt2 on pass 3, lpt3 on
        # pass 4) in a group with tracing off, and dropped from the universe:
        # only TeX's count on passes 3 and 4 sees it, and it is labelled with
        # the pass it describes (re-review 2 defect 2: the pass-3 count was
        # labelled pass 2).
        third_b2 = {"class": "article", "preamble": [{"definer": cnt % (
            "\\begingroup\\tracingassigns=0 \\expandafter\\xdef\\csname lpt\\number"
            "\\lpc\\endcsname{}\\endgroup")}]}
        c = gc.generate(third_b2, tex, pin, kernel, [], {},
                        universe_filter=lambda n: n not in (b"lpt2", b"lpt3"))
        r = " | ".join(c["incomplete_reasons"])
        checks.append(("thirdB2: TeX's count sees the digit-built name on passes 3 and 4 "
                       "only, labelled pass 3 / pass 4",
                       c["complete"] is False and
                       [cov_at(c, h) for h in ("none", "F", "S", "FF", "FS", "FFS")] ==
                       [0, 0, 0, 1, 1, 1] and
                       "on pass 3 after history FS holds 1 names outside" in r and
                       "on pass 4 after history FFS holds 1 names outside" in r and
                       "on pass 2 after history S holds" not in r))
        # dateC: the date reaches the state through the .aux, on pass 2: the
        # date check used to run on pass 1 only.
        date_c = {"class": "article", "preamble": [{"definer":
            "\\makeatletter\\def\\lpyr#1{\\ifnum#1>2000 \\gdef\\lpgrade{}\\fi}"
            "\\AtBeginDocument{\\immediate\\write\\@auxout{\\string\\lpyr{\\the\\year}}}"
            "\\makeatother"}]}
        c = gc.generate(date_c, tex, pin, kernel, [], {})
        r = " | ".join(c["incomplete_reasons"])
        checks.append(("dateC: a date dependence on pass 2 makes the contract incomplete, "
                       "named, and pass 1 shows none",
                       c["complete"] is False and
                       "date_dependent_state: the body-start state on pass 2 after history "
                       "S under the real clock differs from the forced date: ['lpgrade']"
                       in r and "pass 1 after history none under the real clock" not in r))
        # jobD: the job name reaches the state through the .aux, on pass 2.
        job_d = {"class": "article", "preamble": [{"definer":
            "\\makeatletter\\def\\lpjn#1{\\def\\lpa{#1}\\def\\lpb{job}\\ifx\\lpa\\lpb"
            "\\else\\gdef\\lpnotjob{}\\fi}\\AtBeginDocument{\\immediate\\write\\@auxout"
            "{\\string\\lpjn{\\jobname}}}\\makeatother"}]}
        c = gc.generate(job_d, tex, pin, kernel, [], {})
        r = " | ".join(c["incomplete_reasons"])
        checks.append(("jobD: a job-name dependence on pass 2 makes the contract "
                       "incomplete, named, and pass 1 shows none",
                       c["complete"] is False and
                       "jobname_dependent_state: the body-start name set on pass 2 after "
                       "history S under job name lpotherjob differs: ['lpnotjob']" in r and
                       "pass 1 after history none under job name" not in r))

        c = gc.generate(art, tex, pin, kernel, review, {})
        checks.append(("the reviewers' 24 names on plain article: complete, 0 mismatches",
                       c["complete"] and c["self_check"]["mismatch_count"] == 0 and
                       c["self_check"]["use_names"] == 24))

        # M1 slice 2: the signature probes on shapes whose \meaning misleads.
        checks += signature_kills(tex, pin, kernel, work)
    for label, ok in checks:
        print("%s adversarial: %s" % ("OK  " if ok else "FAIL", label))
        bad += 0 if ok else 1
    return bad


SIG_DEFINERS = (
    # The \meaning says arity 0; the behaviour takes one argument.
    "\\newcommand{\\lpsb}[1]{#1}\\newcommand{\\lpsa}{\\lpsb}",
    # An optional argument before a mandatory one.
    "\\newcommand{\\lpsc}[2][d]{#1#2}",
    # A star flag, each variant taking one argument.
    "\\makeatletter\\newcommand{\\lpsd}{\\@ifstar{\\textbf}{\\textit}}\\makeatother",
    # A delimited parameter: no brace count attests it.
    "\\def\\lpse#1.{#1}",
    # A brace group taken only if present (a peek, as \\input does).
    "\\makeatletter\\newcommand{\\lpsf}{\\@ifnextchar\\bgroup{\\textbf}{}}\\makeatother",
    # Text-only: fails in math before taking its argument.
    "\\newcommand{\\lpsg}[1]{\\ifmmode\\lpundefinedsg\\fi#1}",
)


def signature_kills(tex, pin, kernel, work) -> list:
    """Each shape the \\meaning hint gets wrong or cannot see must come out
    attested as it behaves (or unresolved where no brace count describes it)."""
    import contract_signatures as sg
    cfg = {"class": "article", "preamble": [{"definer": d} for d in SIG_DEFINERS]}
    c = gc.generate(cfg, tex, pin, kernel, [], {})
    gc.attach_kernel_ref(c, kernel, pin)
    tmpd = Path(tempfile.mkdtemp(prefix="sigkill-", dir=str(tex.base)))
    cp = tmpd / "sigkill.json"
    cp.write_text(gc.canonical_json(c), encoding="utf-8")
    res = sg.probe_names(cp, ["lpsa", "lpsc", "lpsd", "lpse", "lpsf", "lpsg", "lpnotaname"],
                         cache=tmpd / "cache", work=work)

    def shape(n, i=0):
        r = res[n]
        if r.get("status") != "attested" or len(r["variants"]) <= i:
            return None
        return [a["kind"] for a in r["variants"][i]["args"]]
    out = [
        ("sig: the probe contract is complete", c["complete"]),
        ("sig: \\lpsa (hint arity 0) is attested as one mandatory argument",
         shape("lpsa") == ["req"] and res["lpsa"]["hint"].get("arity") == 0),
        ("sig: \\lpsc is [opt, req]", shape("lpsc") == ["opt", "req"]),
        ("sig: \\lpsd has a star flag and two one-argument variants",
         res["lpsd"].get("star") is True and shape("lpsd") == ["req"] and
         shape("lpsd", 1) == ["star", "req"]),
        ("sig: \\lpse (delimited) is unresolved", res["lpse"].get("status") == "unresolved"),
        ("sig: \\lpsf's peeked group is an argument (gopt), not typeset text",
         shape("lpsf") == ["gopt"]),
        ("sig: \\lpsg compiles in text and is fatal in math",
         shape("lpsg") == ["req"] and
         res["lpsg"]["variants"][0]["cells"]["text"]["allowed"] == "ok" and
         res["lpsg"]["variants"][0]["cells"]["math"]["allowed"] == "fatal"),
        ("sig: a name outside the closed world is E1, with no probe",
         res["lpnotaname"] == {"status": "undefined"}),
    ]
    # The cache answers the second call without TeX.
    rep: dict = {}
    again = sg.probe_names(cp, ["lpsa"], cells=("text",), cache=tmpd / "cache", work=work,
                           report=rep)
    out.append(("sig: probe_names serves a cached (contract, name, cell) without TeX",
                rep.get("lpsa") == "cache" and list(again["lpsa"]["variants"][0]["cells"])
                == ["text"]))
    return out


def check_sidecars(repo: Path, paths: list, work, tmp: Path, sample: int = 0) -> int:
    """Regenerate each selected contract's signature sidecar (if committed) and
    diff it byte for byte. Long: the whole scope is probed again. With
    `sample` > 0, only a seeded sample of names is regenerated and each
    regenerated name's record (its canonical JSON line) is compared with the
    committed one: a partial check, valid because every name's probes are
    independent of every other name's."""
    import contract_signatures as sg
    import random
    failures = 0
    for path in paths:
        side = sg.sidecar_path(repo, path)
        if not side.exists():
            continue
        if sample:
            old = json.loads(side.read_text(encoding="utf-8"))
            names = sorted(random.Random(old["config_key"]).sample(
                sorted(old["signatures"]), min(sample, len(old["signatures"]))))
            with gc.Tex(gc.read_image(repo), work) as tex:
                new = sg.generate_signatures(tex, repo, path, workers=8, batch=False,
                                             names=names)
            bad = [n for n in names if json.dumps(new["signatures"][n], sort_keys=True) !=
                   json.dumps(old["signatures"][n], sort_keys=True)]
            if bad:
                failures += 1
                print("DIFF %s: %d of %d sampled names do not reproduce: %s"
                      % (side.relative_to(repo), len(bad), len(names), bad[:10]))
            else:
                print("OK   %s: %d sampled names reproduced record for record"
                      % (side.relative_to(repo), len(names)))
            continue
        with gc.Tex(gc.read_image(repo), work) as tex:
            new = sg.generate_signatures(tex, repo, path, workers=8, batch=True)
        out = tmp / ("sig-" + path.name)
        out.write_text(gc.canonical_json(new), encoding="utf-8")
        if out.read_bytes() == side.read_bytes():
            print("OK   %s reproduced byte for byte" % side.relative_to(repo))
        else:
            failures += 1
            print("DIFF %s does not reproduce:" % side.relative_to(repo))
            _show_diff(side, out)
    return failures


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--repo", default=str(gc.REPO))
    ap.add_argument("--contract", action="append", default=[])
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--signatures", action="store_true",
                    help="also regenerate each selected contract's signature sidecar "
                         "(corpora/contracts/signatures/) and diff it (long)")
    ap.add_argument("--signatures-sample", type=int, default=0,
                    help="with --signatures: regenerate only this many seeded names")
    ap.add_argument("--cached-kernel", action="store_true",
                    help="reuse the cached kernel instead of re-running INITEX")
    ap.add_argument("--work", default=None,
                    help="a directory under the oracle work root (default: the "
                         "oracle work root)")
    a = ap.parse_args(argv)
    repo = Path(a.repo).resolve()

    image = gc.read_image(repo)
    # The generator is a client of the one oracle (_oracle.py); if the oracle
    # is unavailable (no docker, image not pulled, a wrong tree) nothing here
    # can be checked.
    ok, why = gc._oracle.availability()
    if not ok:
        print("check_contracts_reproducible: CANNOT CHECK - the oracle is unavailable: "
              "%s (this is not a pass)" % why)
        return 2

    if a.all:
        paths = sorted(p for p in (repo / gc.CONTRACT_DIR).glob("*.json") if _is_contract(p))
    else:
        paths = [repo / p for p in (a.contract or [str(DEFAULT)])]
    if not paths:
        print("check_contracts_reproducible: no contracts selected")
        return 1

    work = Path(a.work).expanduser() if a.work else None
    if work is not None:
        work.mkdir(parents=True, exist_ok=True)
        tmp = Path(tempfile.mkdtemp(prefix="check-", dir=work))
    else:
        tmp = gc._oracle.get_oracle().mkdtemp(prefix="check-")
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
        if a.signatures:
            failures += check_sidecars(repo, paths, work, tmp, a.signatures_sample)
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
