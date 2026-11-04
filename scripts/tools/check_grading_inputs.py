#!/usr/bin/env python3
"""check_grading_inputs.py -- three defects of the grading tools' INPUTS,
each with a test that fails before its fix (`--repo` at 0400f74a) and passes
after it (ruling R5: folded into OPEN-128's one re-grade).

  OPEN-139  the sample-3 seal in the GRADING tools. diff_real_roots.py,
            gen_proven_coverage.py and measure_strict_boundary.py must REFUSE
            a request that touches sealed sample 3 (OPEN-119) unless it is a
            `--sealed-measurement`, whose output carries no arXiv id; a
            sample-2 request is not refused by the seal.
  C-181     _oracle.first_error / first_error_block: TeX's 79-byte wrap
            undone exactly, the full message kept, message / context / help
            separated -- on real pdfTeX logs of the pinned oracle
            (corpora/oracle_baseline/first_error_fixtures, expected.json).
  C-182     diff_real_roots.sha256_tree digests what shutil.copytree (the
            graded copy) holds: a symlinked directory's files included; a
            link out of the package refused; a package without links digests
            exactly as before.

PURE: no docker, no TeX, no corpus. Never prints a sealed id.
Run: python3 scripts/tools/check_grading_inputs.py [--repo DIR]
"""
from __future__ import annotations

import argparse
import hashlib
import re
import importlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

FIX = "corpora/oracle_baseline/first_error_fixtures"


class Checker:
    def __init__(self):
        self.n, self.failures = 0, []

    def expect(self, label: str, ok: bool, detail: str = "") -> None:
        self.n += 1
        if not ok:
            self.failures.append(label + (f" ({detail})" if detail else ""))


def run_tool(repo: Path, argv: list[str]) -> tuple[int, str]:
    p = subprocess.run([sys.executable, *argv], cwd=repo, capture_output=True,
                       text=True, timeout=120,
                       env=dict(os.environ, LP_REAL_CORPUS="/nonexistent-corpus"))
    return p.returncode, p.stdout + p.stderr


def check_seal(c: Checker, repo: Path) -> None:
    s3 = "corpora/real_roots/results_sample3.json"
    s2 = "corpora/real_roots/results_sample2.json"
    tools = (
        ("diff_real_roots", lambda r: ["scripts/tools/diff_real_roots.py", "--repass",
                                       "--results", Path(r).name, "--repo", "."]),
        ("gen_proven_coverage", lambda r: ["scripts/tools/gen_proven_coverage.py",
                                           "--results", r, "--out", os.devnull, "--rejoin"]),
        ("measure_strict_boundary", lambda r: ["scripts/tools/measure_strict_boundary.py",
                                               "--results", r, "--corpus", "/nonexistent",
                                               "--cli", "/nonexistent", "--out", os.devnull]),
    )
    for name, argv in tools:
        rc, out = run_tool(repo, argv(s3))
        c.expect(f"OPEN-139: {name} on sealed sample 3 was not REFUSED by the seal "
                 f"(rc {rc})", rc == 2 and "REFUSED (OPEN-139)" in out, out[-200:])
        rc, out = run_tool(repo, argv(s2))
        c.expect(f"OPEN-139: {name} on sample 2 was refused by the seal",
                 "OPEN-139" not in out, out[-200:])
    rc, out = run_tool(repo, ["scripts/tools/diff_real_roots.py", "--offset", "800",
                              "--n", "5", "--results", "results_x.json", "--repo", "."])
    c.expect("OPEN-139: diff_real_roots drawing a window inside sample 3 was not "
             "refused", rc == 2 and "REFUSED (OPEN-139)" in out, out[-200:])
    # The measurement-only mode: per-document lines are withheld.
    m = json.loads((repo / "corpora/real_roots/manifest_sample3.json").read_text())
    sid = m["docs"][0]["arxiv_id"]
    prog = ("import sys; sys.path.insert(0, 'scripts/tools'); import _grading_seal as g\n"
            f"g.gate('t', [{sid!r}], measurement=True)\n"
            f"print('  [1/1] ' + {sid!r} + ' FALSE-READY')\n"
            f"print('[real-roots] FALSE-READY ' + {sid!r} + ': ! Undefined')\n"
            "print('[real-roots]   FALSE-READY        7')\n"
            # C-197 (review of 82638518, H3): id-free per-document text
            "print('[real-roots] false-READY classes:')\n"
            "print('[real-roots]   x1  ! Package foo Error: SECRET-FIRST-ERROR-LINE-1')\n"
            "print('SECRET-CONTINUATION-LINE-2 (\\\\MessageBreak)')\n"
            "sys.stderr.write('Traceback: SECRET-TRACE\\n')\n"
            f"sys.stderr.write('FATAL: ' + {sid!r} + ' tree sha differs\\n')\n")
    p = subprocess.run([sys.executable, "-c", prog], cwd=repo, capture_output=True,
                       text=True, timeout=60)
    out = p.stdout + p.stderr
    c.expect("OPEN-139: --sealed-measurement printed a sealed id or withheld the "
             "aggregate line", p.returncode == 0 and sid not in out
             and "FALSE-READY        7" in out and "withheld" in out,
             f"rc {p.returncode}, id printed: {sid in out}")
    c.expect("C-197: --sealed-measurement printed per-document text that carries no "
             "id (a deny-list of id lines leaks; it must be an allow-list)",
             "SECRET" not in out, [ln for ln in out.splitlines() if "SECRET" in ln][:3])
    rc, out = run_tool(repo, ["scripts/tools/diff_real_roots.py", "--repass", "--results",
                              "results_sample3.json", "--repo", ".", "--sealed-measurement",
                              "--diff-out", os.devnull])
    c.expect("C-197: a sealed measurement accepted --diff-out (a per-row file)",
             rc == 2 and "C-197" in out, out[-200:])
    rc, out = run_tool(repo, ["scripts/tools/diff_real_roots.py", "--repass", "--results",
                              "results_sample3.json", "--repo", ".", "--sealed-measurement",
                              "--experiment-out", os.devnull])
    c.expect("C-197: a sealed measurement accepted --experiment-out (a per-row file)",
             rc == 2 and "C-197" in out, out[-200:])


# The tools that need not gate (C-197): tests and harnesses whose ids are their
# own fixtures, never a corpus window.
GATE_EXEMPT = {
    "check_oracle_infra_grading.py": "pure test; fake engine, synthetic ids",
    "check_gate_selftests.py": "mutation harness; quotes other tools' code",
    "check_grading_inputs.py": "this test",
}
_TAKES_DOCS = re.compile(r'add_argument\(\s*"--(offset|sample-offset|only-ids|ids|results|window)"'
                         r'|build_frame\(')
_RUNS = re.compile(r"\b(run_to_fixpoint|run_to_fixpoint_full|run_once|run_pass|"
                   r"run_pdflatex|--compile-check)\b")


def check_gate_coverage(c: Checker, repo: Path) -> dict:
    """C-197 (third review, M2): the seal holds by CONSTRUCTION for every
    engine run -- the oracle checks it at the one place every run passes
    (_exec, reference_pass, _image_command) -- and by a per-tool gate for every
    tool that takes documents without running the oracle (it runs the CLI on
    them). Returns the counts the PASS line prints."""
    import inspect
    om = importlib.import_module("_oracle")
    co = om.ContainerOracle
    choke = ("_exec", "reference_pass", "_image_command")
    for m in choke:
        src = inspect.getsource(getattr(co, m)) if hasattr(co, m) else ""
        c.expect(f"C-197: ContainerOracle.{m} starts a container without the "
                 f"sample-3 seal check (seal_check)", "seal_check(" in src)
    # every container the oracle starts is one of these, or carries no document
    nodoc = {"hostinfo", "session_probe", "remove", "_dk", "stop"}
    launches = set()
    for name, fn in inspect.getmembers(co, inspect.isfunction):
        if "self._launch(" in inspect.getsource(fn):
            launches.add(name)
    stray = sorted(launches - set(choke) - nodoc)
    c.expect(f"C-197: a container is started outside the sealed choke points: {stray}",
             not stray)
    # behaviour: an id in the path, a copy by digest, an authorised measurement
    gs = importlib.import_module("_grading_seal")
    m3 = json.loads((repo / "corpora/real_roots/manifest_sample3.json").read_text())
    sid = m3["docs"][0]["arxiv_id"]
    with tempfile.TemporaryDirectory(prefix="seal-run-") as td:
        d = Path(td) / sid
        d.mkdir()
        (d / "main.tex").write_text("x\n")
        c.expect("C-197: seal_run let a run inside a directory named after a sealed "
                 "paper through", bool(gs.seal_run(d, ["main.tex"])))
        other = Path(td) / "copy"
        other.mkdir()
        (other / "main.tex").write_text("a copy\n")
        gs.seal_run(other, ["main.tex"])          # fills the cache
        gs._CACHE["digests"] = gs._CACHE["digests"] | {
            hashlib.sha256(b"a copy\n").hexdigest()}
        c.expect("C-197: seal_run let a COPY of a sealed top-level file through",
                 bool(gs.seal_run(other, ["main.tex"])))
        gs.SEALED_AUTHORIZED = True
        c.expect("C-197: an authorised sealed measurement was refused by seal_run",
                 gs.seal_run(other, ["main.tex"]) is None)
        gs.SEALED_AUTHORIZED = False
        gs._CACHE.clear()
    # tools: those that run the oracle are gated by construction; those that
    # take documents without running it must call the gate themselves
    runs = re.compile(r"\b(run_pdflatex|run_to_fixpoint(_full)?|run_pass|run_once|"
                      r"run_engine|reference_pass|measure)\s*\(|_oracle\.py")
    n_run = n_doc = 0
    for f in sorted((repo / "scripts" / "tools").glob("*.py")):
        s = f.read_text(errors="replace")
        if "__main__" not in s or f.name in GATE_EXEMPT:
            continue
        if runs.search(s):
            n_run += 1
            continue
        if _TAKES_DOCS.search(s) or ("arxiv_id" in s and _RUNS.search(s)):
            n_doc += 1
            c.expect(f"C-197: {f.name} takes documents but never calls "
                     f"_grading_seal.gate (it could grade sealed sample 3)",
                     "_grading_seal.gate(" in s)
    c.expect(f"C-197: the scan found only {n_run} oracle-running tools (floor 20)",
             n_run >= 20, str(n_run))
    c.expect(f"C-197: the scan found only {n_doc} other document-taking tools "
             f"(floor 4)", n_doc >= 4, str(n_doc))
    return {"oracle_tools": n_run, "doc_tools": n_doc}


def check_first_error(c: Checker, repo: Path, om) -> None:
    d = repo / FIX
    exp = json.loads((d / "expected.json").read_text())["expected"]
    c.expect("C-181: the fixtures are missing", len(exp) >= 5, str(len(exp)))
    fe = getattr(om, "first_error", None)
    c.expect("C-181: _oracle has no first_error (message / context / help)",
             callable(fe))
    for name, want in exp.items():
        got = om.first_error_block(d / f"{name}.log")
        c.expect(f"C-181: first_error_block({name}) is not the full unwrapped "
                 f"message", got == want["message"], repr(got[:120]))
        if callable(fe):
            c.expect(f"C-181: first_error({name}) is not {{message, context, help}} "
                     f"as recorded", fe(d / f"{name}.log") == want,
                     repr(fe(d / f"{name}.log"))[:200])
    # The wrap is BYTES: the pkgerr message holds UTF-8 across the 79-byte cut.
    c.expect("C-181: a UTF-8 message wrapped at 79 bytes is not joined exactly",
             "ünïcödé characters that goes past" in exp.get("pkgerr", {}).get("message", "")
             and om.first_error_block(d / "pkgerr.log") == exp["pkgerr"]["message"])


def legacy_tree(d: Path) -> str:
    h = hashlib.sha256()
    for f in sorted(d.rglob("*")):
        if f.is_file():
            h.update(str(f.relative_to(d)).encode())
            h.update(hashlib.sha256(f.read_bytes()).digest())
    return h.hexdigest()


def check_tree(c: Checker, drr) -> None:
    with tempfile.TemporaryDirectory(prefix="grading-inputs-") as td:
        td = Path(td)
        plain = td / "plain"
        (plain / "sub").mkdir(parents=True)
        (plain / "main.tex").write_text("a\n")
        (plain / "sub" / "b.tex").write_text("b\n")
        (plain / "Z.bib").write_text("z\n")
        c.expect("C-182: a package without links no longer digests as before (every "
                 "recorded manifest would be invalidated)",
                 drr.sha256_tree(plain) == legacy_tree(plain))
        pkg = td / "pkg"
        shutil.copytree(plain, pkg)
        os.symlink("sub", pkg / "linkdir")
        os.symlink("main.tex", pkg / "alias.tex")
        copy = td / "copy"
        shutil.copytree(pkg, copy)        # what run_one grades
        try:
            got = drr.sha256_tree(pkg)
        except ValueError as e:
            got = f"refused: {e}"
        c.expect("C-182: sha256_tree does not digest what copytree copies through a "
                 "symlinked directory", got == drr.sha256_tree(copy),
                 f"{got[:20]} vs {drr.sha256_tree(copy)[:20]}")
        out = td / "outside"
        shutil.copytree(plain, out)
        (td / "secret").mkdir()
        (td / "secret" / "s.tex").write_text("outside\n")
        os.symlink(str(td / "secret"), out / "escape")
        try:
            drr.sha256_tree(out)
            refused = False
        except ValueError:
            refused = True
        c.expect("C-182: a link out of the package was digested (the grade would read "
                 "bytes outside it) instead of refused", refused)
        loop = td / "loop"
        shutil.copytree(plain, loop)
        os.symlink(".", loop / "sub" / "self")
        try:
            drr.sha256_tree(loop)
            refused = False
        except (ValueError, RecursionError, OSError):
            refused = True
        c.expect("C-182: a looping link was not refused", refused)
        fifo = td / "fifo"
        shutil.copytree(plain, fifo)
        os.mkfifo(fifo / "pipe")
        try:
            drr.sha256_tree(fifo)
            refused = False
        except ValueError:
            refused = True
        c.expect("C-182 (L4): a package FIFO was skipped instead of refused", refused)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", default=str(Path(__file__).resolve().parent.parent.parent))
    repo = Path(ap.parse_args().repo).resolve()
    sys.path.insert(0, str(repo / "scripts" / "tools"))
    om = importlib.import_module("_oracle")
    drr = importlib.import_module("diff_real_roots")
    print(f"[grading-inputs] modules: {om.__file__}, {drr.__file__}")
    c = Checker()
    check_seal(c, repo)
    scan = check_gate_coverage(c, repo)
    check_first_error(c, repo, om)
    check_tree(c, drr)
    if c.failures:
        print(f"[grading-inputs] FAIL: {len(c.failures)} of {c.n} checks:", file=sys.stderr)
        for f in c.failures:
            print(f"  - {f}", file=sys.stderr)
        return 1
    print(f"[grading-inputs] OK: {c.n} checks: the seal at every engine run (the "
          f"oracle's choke points) and in {scan['doc_tools']} document-taking tools "
          f"(floor 4), {scan['oracle_tools']} oracle-running tools gated by "
          f"construction (floor 20), the sealed output an allow-list; C-181 first "
          f"error on {len(json.loads((repo / FIX / 'expected.json').read_text())['expected'])} "
          f"real logs; C-182 copytree-consistent digest")
    return 0


if __name__ == "__main__":
    sys.exit(main())
