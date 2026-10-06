#!/usr/bin/env python3
"""OPEN-128 (8): one launch definition, two platforms -- grade per document on both.

WHY (ADR-015 E15, owner 2026-10-06; re-audit premises 23 and 25). Since
OPEN-128 the oracle has ONE launch definition (_oracle.launch_argv): a laptop
and CI's arm64 runner start byte-identical `docker run` command lines, and
check_oracle_pin refuses any other. That makes the CONFIGURATION identical by
construction. It does not make the PLATFORM identical: the work root's file
system (APFS through colima's virtiofs on a Mac -- case- and Unicode-
normalisation-insensitive -- against the runner's case-sensitive ext4), the
kernel, the CPU's speed against the wall-clock timeout, memory and disk all
still differ. The 97/97 this replaces (check_oracle_equivalence) compared two
code paths inside ONE local container and never ran in CI; it said nothing
about the platforms.

WHAT THIS DOES.
  --grade --platform NAME --out FILE
        grades every document of the platform set through `get_oracle()`
        (run_to_fixpoint: the protocol), records per document the grade (rc,
        PDF, passes), the values the adversarial documents print
        ([LPP:key=value]), the first error line (a diagnostic) and the
        seconds it took, and the PLATFORM's facts (host, docker, kernel, CPUs,
        memory, the work root's file system and whether it folds case and
        Unicode normalisation, measured by probes); the oracle block names the
        grading code, stamped when the run STARTS.
  --combine LOCAL CI --out corpora/oracle_baseline/platform_residuals.json
        joins the two sides (they must be of the same oracle, clock and
        grading code: one commit) and lists every document whose grade or
        values differ: the platform residuals.
  --check FILE
        compares a fresh grade (one side) with the RECORDED grades of that
        platform in platform_residuals.json; any difference fails (CI's
        tex-oracle job runs it on every PR, so a platform residual that
        appears or disappears is seen).

THE PLATFORM SET: every document of the in-repo graded corpora (compile_check,
false_ready, strict_battery, apply_fixes: the documents the required CI job
grades) and ADVERSARIAL documents for the residuals the re-audit names
(ADVERSARIAL below): a file name that differs from the reference only in case
or only in Unicode normalisation (NFC vs NFD), a case variant written and
then looked for, a directory's size, a directory listing. Their auxiliary
files are written by this tool with exact bytes (git and macOS would
normalise names committed to the repository).

Run:
  python3 scripts/tools/check_oracle_platforms.py --grade --platform local --out /tmp/local.json
  python3 scripts/tools/check_oracle_platforms.py --combine /tmp/local.json ci.json \\
      --out corpora/oracle_baseline/platform_residuals.json
  python3 scripts/tools/check_oracle_platforms.py --check /tmp/ci.json
"""
from __future__ import annotations

import argparse
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import time
import unicodedata
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import _oracle  # noqa: E402

GRADER_FILES = ("scripts/tools/check_oracle_platforms.py",)
SCHEMA = "lp-oracle-platforms/1"
OUT = "corpora/oracle_baseline/platform_residuals.json"
SETS = ("corpora/compile_check", "corpora/false_ready", "corpora/strict_battery",
        "corpora/apply_fixes")
TIMEOUT = 300
LPP = re.compile(r"\[LPP:([A-Za-z0-9-]+)=(.*?)\]")

_NFC = unicodedata.normalize("NFC", "café")
_NFD = unicodedata.normalize("NFD", "café")
_Q = r"""\makeatletter
\def\lppq#1#2{\begingroup\everyeof{\noexpand}\endlinechar=`\,
  \catcode`\%=12 \catcode`\#=12 \catcode`\_=12 \catcode`\~=12
  \catcode`\$=12 \catcode`\&=12 \catcode`\^=12 \catcode`\\=12
  \edef\lppx{\@@input|"#2" }\immediate\write16{[LPP:#1=\detokenize\expandafter{\lppx}]}\endgroup}
\makeatother
"""
# (name, {file name (str, exact bytes as UTF-8): content}, toplevel)
ADVERSARIAL = [
    ("p-case-input", {
        "p-case-input.tex": "\\documentclass{article}\n\\begin{document}\n"
                            "\\input{Foo}\\typeout{[LPP:found=\\lppfound]}\nx\n\\end{document}\n",
        "foo.tex": "\\def\\lppfound{lower-case foo.tex}\n"}, "p-case-input.tex"),
    ("p-case-ifexists", {
        "p-case-ifexists.tex": "\\documentclass{article}\n\\begin{document}\n"
                               "\\IfFileExists{FOO.TEX}{\\typeout{[LPP:exists=yes]}}"
                               "{\\typeout{[LPP:exists=no]}}\nx\n\\end{document}\n",
        "foo.tex": "\\relax\n"}, "p-case-ifexists.tex"),
    ("p-case-written", {
        "p-case-written.tex": "\\documentclass{article}\n\\begin{document}\n"
                              "\\immediate\\openout9=Written.txt \\immediate\\write9{w}"
                              "\\immediate\\closeout9\n"
                              "\\IfFileExists{written.txt}{\\typeout{[LPP:seen=yes]}}"
                              "{\\typeout{[LPP:seen=no]}}\nx\n\\end{document}\n"},
     "p-case-written.tex"),
    ("p-nfd-input", {
        "p-nfd-input.tex": "\\documentclass{article}\n\\begin{document}\n"
                           "\\input{" + _NFD + "}\\typeout{[LPP:found=\\lppfound]}\nx\n"
                           "\\end{document}\n",
        _NFC + ".tex": "\\def\\lppfound{nfc file}\n"}, "p-nfd-input.tex"),
    ("p-nfc-input", {
        "p-nfc-input.tex": "\\documentclass{article}\n\\begin{document}\n"
                           "\\input{" + _NFC + "}\\typeout{[LPP:found=\\lppfound]}\nx\n"
                           "\\end{document}\n",
        _NFD + ".tex": "\\def\\lppfound{nfd file}\n"}, "p-nfc-input.tex"),
    ("p-dirsize", {
        "p-dirsize.tex": "\\documentclass{article}\n\\begin{document}\n"
                         "\\typeout{[LPP:size-sub=\\pdffilesize{sub}]}"
                         "\\typeout{[LPP:size-file=\\pdffilesize{sub/a.tex}]}"
                         "\\typeout{[LPP:mod-sub=\\pdffilemoddate{sub/a.tex}]}\nx\n"
                         "\\end{document}\n",
        "sub/a.tex": "\\relax\n"}, "p-dirsize.tex"),
    ("p-listing", {
        "p-listing.tex": "\\documentclass{article}\n" + _Q + "\\begin{document}\n"
                         "\\lppq{ls}{l3sys-query ls}\\lppq{ls-date}{l3sys-query ls --sort date}"
                         "\\lppq{pwd}{l3sys-query pwd}\nx\n\\end{document}\n",
        "zeta.txt": "z\n", "Alpha.txt": "a\n", "mid.txt": "m\n", "beta.txt": "b\n"},
     "p-listing.tex"),
    ("p-children", {
        "p-children.tex": "\\documentclass{article}\n" + _Q + "\\begin{document}\n"
                          "\\lppq{osversion}{texosquery-jre8 -r}\\lppq{now}{texosquery-jre8 -n}"
                          "\\lppq{tmpdir}{kpsewhich -var-value=TMPDIR}\nx\n\\end{document}\n"},
     "p-children.tex"),
]


def documents(repo: Path) -> list[dict]:
    """The platform set, in a fixed order: (id, source dir, toplevel)."""
    out = []
    for rel in SETS:
        d = repo / rel
        for t in sorted(d.glob("*.tex")):
            out.append({"id": f"{rel}/{t.name}", "dir": d, "top": t.name})
        for sub in sorted(p for p in d.iterdir() if p.is_dir()):
            m = sub / "main.tex"
            if m.is_file():
                out.append({"id": f"{rel}/{sub.name}/main.tex", "dir": sub, "top": "main.tex"})
    for name, files, top in ADVERSARIAL:
        out.append({"id": f"adversarial/{name}", "files": files, "top": top})
    return out


def stage(o, doc: dict) -> Path:
    td = o.mkdtemp(prefix="lp-platform-")
    w = td / "w"
    if "dir" in doc:
        shutil.copytree(doc["dir"], w, symlinks=True)
    else:
        w.mkdir()
        for name, text in doc["files"].items():
            p = w / name
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_bytes(text.encode("utf-8"))
    return w


def grade_one(o, doc: dict) -> dict:
    w = stage(o, doc)
    try:
        t0 = time.monotonic()
        try:
            r = o.run_to_fixpoint(w, doc["top"], o.tex_env(), TIMEOUT)
        except _oracle.OracleError as e:
            return {"ungraded": str(e)[:300], "secs": round(time.monotonic() - t0, 2)}
        secs = round(time.monotonic() - t0, 2)
        log = _oracle.job_output(w, doc["top"], ".log")
        text = log.read_text(errors="replace") if log.is_file() else ""
        flat = "".join(text.split("\n"))
        return {"rc": r.rc, "pdf": r.pdf, "passes": r.passes, "timed_out": r.timed_out,
                "values": dict(LPP.findall(flat)),
                "first_error": _oracle.first_error_block(log)[:160], "secs": secs}
    finally:
        shutil.rmtree(w.parent, ignore_errors=True)


def platform_facts(o) -> dict:
    """What differs between platforms, measured."""
    facts = {"host": {"system": platform.system(), "machine": platform.machine(),
                      "release": platform.release(),
                      "cpus": os.cpu_count()}}
    di = subprocess.run([o.docker, "info", "--format", "{{json .}}"],
                        capture_output=True, text=True, timeout=60)
    try:
        info = json.loads(di.stdout)
        facts["docker"] = {k: info.get(k) for k in (
            "ServerVersion", "KernelVersion", "OperatingSystem", "OSType",
            "Architecture", "NCPU", "MemTotal", "Driver", "CgroupVersion",
            "CgroupDriver")}
    except ValueError:
        facts["docker"] = {"error": di.stderr[:200]}
    # The work root's file system, as the CONTAINER sees it, and whether it
    # folds case and Unicode normalisation (probes: write one name, look up
    # the other, inside a container of the launch definition).
    probe = o.mkdtemp(prefix="lp-platform-probe-")
    try:
        (probe / "CaseProbe").write_text("x")
        (probe / _NFC).write_text("x")
        rc, out, _ = o.image_command(["stat", "-f", "-c", "%T", str(probe)], cwd=probe)
        facts["work_root_fs_in_container"] = out.decode().strip() if rc == 0 else None
        rc1, _, _ = o.image_command(["stat", str(probe / "caseprobe")], cwd=probe)
        rc2, _, _ = o.image_command(["stat", str(probe / _NFD)], cwd=probe)
        facts["work_root_case_insensitive"] = rc1 == 0
        facts["work_root_normalisation_insensitive"] = rc2 == 0
    finally:
        shutil.rmtree(probe, ignore_errors=True)
    return facts


def do_grade(repo: Path, name: str, out: Path, only=None) -> int:
    try:
        stamp = _oracle.RunStamp(GRADER_FILES, repo)
        o = _oracle.get_oracle()
    except _oracle.OracleError as e:
        print(f"[platforms] FATAL: {e}", file=sys.stderr)
        return 2
    docs = documents(repo)
    if only:
        docs = [d for d in docs if any(x in d["id"] for x in only)]
    rows = {}
    for i, d in enumerate(docs, 1):
        rows[d["id"]] = grade_one(o, d)
        g = rows[d["id"]]
        print(f"[platforms] {i}/{len(docs)} {d['id']}: rc {g.get('rc')} pdf "
              f"{g.get('pdf')} {g.get('values') or ''} {g.get('ungraded', '')[:80]}",
              flush=True)
    why = stamp.check()
    if why:
        print(f"[platforms] FATAL: nothing written: {why}", file=sys.stderr)
        return 2
    doc = {"schema": SCHEMA, "platform": name, "graded_at_sha": stamp.head,
           "oracle": stamp.oracle_block(o), "facts": platform_facts(o),
           "documents": rows}
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(doc, indent=1, ensure_ascii=False, sort_keys=True) + "\n")
    print(f"[platforms] wrote {out}: {len(rows)} documents, "
          f"{sum(1 for r in rows.values() if 'ungraded' in r)} ungraded")
    return 0


GRADE_KEYS = ("rc", "pdf", "passes", "timed_out", "values")


def diff_rows(a: dict, b: dict) -> list[dict]:
    out = []
    for k in sorted(set(a) | set(b)):
        x, y = a.get(k), b.get(k)
        if x is None or y is None:
            out.append({"document": k, "missing_on": "local" if x is None else "ci"})
            continue
        moved = [f for f in GRADE_KEYS if x.get(f) != y.get(f)]
        if "ungraded" in x or "ungraded" in y:
            moved.append("ungraded")
        if moved:
            out.append({"document": k, "fields": moved,
                        "local": {f: x.get(f) for f in GRADE_KEYS + ("first_error", "ungraded")
                                  if f in x},
                        "ci": {f: y.get(f) for f in GRADE_KEYS + ("first_error", "ungraded")
                               if f in y}})
    return out


def do_combine(repo: Path, local: Path, ci: Path, out: Path) -> int:
    a, b = json.loads(local.read_text()), json.loads(ci.read_text())
    if a["platform"] == b["platform"]:
        print("[platforms] FATAL: both sides are one platform", file=sys.stderr)
        return 2
    try:
        _oracle.require_same_oracle(a["oracle"], b["oracle"], "the two platforms")
        _oracle.require_same_grading_code(a["oracle"].get("grading_code"),
                                          b["oracle"]["grading_code"], "the two platforms")
    except _oracle.OracleError as e:
        print(f"[platforms] FATAL: {e}", file=sys.stderr)
        return 2
    if a["graded_at_sha"] != b["graded_at_sha"]:
        print(f"[platforms] NOTE: graded at {a['graded_at_sha'][:12]} and "
              f"{b['graded_at_sha'][:12]}: the same grading code (checked), "
              f"different commits", file=sys.stderr)
    dif = diff_rows(a["documents"], b["documents"])
    secs = [(a["documents"][k].get("secs"), b["documents"][k].get("secs"))
            for k in a["documents"] if k in b["documents"]]
    ratio = sorted(round(y / x, 3) for x, y in secs if x and y)
    doc = {
        "schema": SCHEMA,
        "what": ("OPEN-128 (8): every document of the platform set graded through the "
                 "ONE launch definition on the laptop (colima VM, virtiofs work root) and "
                 "on CI's arm64 runner, with the same grading code; the documents whose "
                 "grade or printed values differ are the PLATFORM RESIDUALS"),
        "oracle_local": a["oracle"], "oracle_ci": b["oracle"],
        "graded_at_sha": {"local": a["graded_at_sha"], "ci": b["graded_at_sha"]},
        "facts": {"local": a["facts"], "ci": b["facts"]},
        "summary": {"documents": len(set(a["documents"]) | set(b["documents"])),
                    "differ": len(dif),
                    "differ_ids": [d["document"] for d in dif],
                    "secs_ratio_ci_over_local": {
                        "n": len(ratio),
                        "median": ratio[len(ratio) // 2] if ratio else None,
                        "min": ratio[0] if ratio else None,
                        "max": ratio[-1] if ratio else None}},
        "residuals": dif,
        "grades": {"local": a["documents"], "ci": b["documents"]},
    }
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(doc, indent=1, ensure_ascii=False, sort_keys=True) + "\n")
    print(f"[platforms] wrote {out}: {doc['summary']['documents']} documents, "
          f"{len(dif)} differ between the platforms: {doc['summary']['differ_ids']}")
    return 0


def do_check(repo: Path, fresh: Path, recorded: Path) -> int:
    f = json.loads(fresh.read_text())
    if not recorded.is_file():
        print(f"[platforms] FATAL: no recorded {recorded}", file=sys.stderr)
        return 2
    r = json.loads(recorded.read_text())
    side = "ci" if f["platform"] == "ci" else "local"
    try:
        _oracle.require_same_oracle(r[f"oracle_{side}"], f["oracle"],
                                    f"{recorded} [{side}]")
    except _oracle.OracleError as e:
        print(f"[platforms] FAIL: {e}", file=sys.stderr)
        return 1
    dif = [d for d in diff_rows(r["grades"][side], f["documents"])]
    if dif:
        print(f"[platforms] FAIL: {len(dif)} document(s) graded differently on "
              f"{side} from the recorded {side} grades:", file=sys.stderr)
        for d in dif[:20]:
            print(f"  - {json.dumps(d, ensure_ascii=False)[:300]}", file=sys.stderr)
        return 1
    print(f"[platforms] OK: {len(f['documents'])} documents graded on {side} exactly "
          f"as recorded; {r['summary']['differ']} recorded platform residual(s): "
          f"{r['summary']['differ_ids']}")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", default=".")
    ap.add_argument("--grade", action="store_true")
    ap.add_argument("--platform", choices=("local", "ci"))
    ap.add_argument("--only", action="append")
    ap.add_argument("--combine", nargs=2, metavar=("LOCAL", "CI"))
    ap.add_argument("--check", metavar="FRESH")
    ap.add_argument("--out", default=None)
    ns = ap.parse_args()
    repo = Path(ns.repo).resolve()
    if ns.grade:
        if not ns.platform or not ns.out:
            ap.error("--grade needs --platform and --out")
        return do_grade(repo, ns.platform, Path(ns.out), ns.only)
    if ns.combine:
        return do_combine(repo, Path(ns.combine[0]), Path(ns.combine[1]),
                          Path(ns.out or repo / OUT))
    if ns.check:
        return do_check(repo, Path(ns.check), repo / OUT)
    ap.error("give --grade, --combine or --check")
    return 2


if __name__ == "__main__":
    sys.exit(main())
