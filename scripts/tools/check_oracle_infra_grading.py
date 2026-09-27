#!/usr/bin/env python3
"""Gate: an oracle that did not run pdfTeX is NEVER graded as a pdflatex result.

WHY (OPEN-118, adversarial review round 2, 2026-09-27). The first fix for
"infrastructure failures are graded" recognised an oracle failure by its SHAPE:
rc 125-127, or a non-zero rc with "Error response from daemon" on stderr. That
is a blacklist, and it missed a realistic shape. MEASURED with a docker wrapper
that sends `docker exec` to a dead socket (colima restarting, the VM gone): the
docker CLI prints "failed to connect to the docker API ..." and exits 1, and
  - the `_oracle.py pdflatex` shim exited 1 (a pdflatex failure, not 125);
  - `run_to_fixpoint` returned OracleRun(rc=1, pdf=False): a graded FAILS in
    diff_real_roots, gen_apply_fixes_real_differential, gen_strict_battery and
    regrade_sample;
  - check_apply_fixes_roundtrip.pdflatex_ok returned False ("fails");
  - false_ready_oracle.sh, with only its -halt-on-error passes lost, exited 0
    with 66 `ok` rows although no halt-protocol pdflatex had run.

The rule is now a whitelist (see `_oracle.PDFTEX_BANNER`): a run's rc counts
only with POSITIVE PROOF that pdfTeX produced it -- pdfTeX's banner in that
run's own output, and (container) the rc reported by a shell INSIDE the
container on a per-run nonce line rather than the docker client's rc.

This gate is PURE (no docker, no TeX): it drives the real grading code with
FAKE docker/engine executables that reproduce each failure shape, including the
re-reviewer's dead-socket one, and asserts each is refused, while a genuine
pdfTeX failure (banner present, rc 1) is still graded. Its kill-tests in
check_gate_selftests.py revert each proof check and must make it fail.

Run: python3 scripts/tools/check_oracle_infra_grading.py --repo .
"""
from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import _oracle  # noqa: E402

DEAD_MSG = ("failed to connect to the docker API at unix:///nonexistent.sock; "
            "check if the path is correct and if the daemon is running: dial "
            "unix /nonexistent.sock: connect: no such file or directory")

# A fake `docker`. It answers `exec ... rm ...` with success and every run
# `exec ... sh -c SCRIPT sh NONCE TIMEOUT ARGS...` according to FAKE_MODE (one
# mode per call, consumed from a comma-separated FAKE_PLAN via FAKE_COUNT):
#   ok        banner on stdout, nonce line rc=0
#   fail      banner + a TeX error on stdout, nonce line rc=1 (a REAL failure)
#   dead      nothing on stdout, DEAD_MSG on stderr, exit 1 (the measured shape)
#   daemonerr "Error response from daemon: No such container", exit 1
#   cut       banner on stdout, then the stream is lost: no nonce line, exit 1
#   nobanner  nothing on stdout, nonce line rc=1 (something else exited 1)
#   timeout   nonce line rc=124
FAKE_DOCKER = r'''#!/usr/bin/env python3
import os, sys
a = sys.argv[1:]
if a[:1] == ["exec"] and "-c" not in a:
    sys.exit(0)                       # `exec NAME rm -f -- ...`
plan = os.environ["FAKE_PLAN"].split(",")
cf = os.environ["FAKE_COUNT"]
n = int(open(cf).read()) if os.path.exists(cf) else 0
open(cf, "w").write(str(n + 1))
mode = plan[min(n, len(plan) - 1)]
i = a.index("-c")
nonce = a[i + 3]
banner = "This is pdfTeX, Version 3.141592653-2.6-1.40.29 (TeX Live 2026)\n"
def rcline(rc):
    sys.stderr.write("\n%s=%d\n" % (nonce, rc))
if mode == "ok":
    sys.stdout.write(banner + "Output written on t.pdf (1 page).\n"); rcline(0)
elif mode == "fail":
    sys.stdout.write(banner + "! Undefined control sequence.\n"); rcline(1)
elif mode == "dead":
    sys.stderr.write("%s\n" % os.environ["DEAD_MSG"]); sys.exit(1)
elif mode == "daemonerr":
    sys.stderr.write("Error response from daemon: No such container\n"); sys.exit(1)
elif mode == "cut":
    sys.stdout.write(banner); sys.exit(1)
elif mode == "nobanner":
    rcline(1)
elif mode == "timeout":
    rcline(124)
'''

# A fake ENGINE for the shell grader's run_pdflatex: modes as above, stdout only.
FAKE_ENGINE = r'''#!/bin/bash
n=$(( $(cat "$FAKE_COUNT" 2>/dev/null || echo 0) + 1 )); echo $n > "$FAKE_COUNT"
IFS=, read -ra plan <<<"$FAKE_PLAN"
i=$(( n - 1 )); [ $i -ge ${#plan[@]} ] && i=$(( ${#plan[@]} - 1 ))
case "${plan[$i]}" in
  ok)   echo "This is pdfTeX, Version 3.141592653-2.6-1.40.29"; exit 0 ;;
  fail) echo "This is pdfTeX, Version 3.141592653-2.6-1.40.29"; echo "! Undefined"; exit 1 ;;
  dead) echo "$DEAD_MSG" >&2; exit 1 ;;
  *)    exit 1 ;;
esac
'''


class Checker:
    def __init__(self, repo: Path, td: Path):
        self.repo, self.td = repo, td
        self.failures: list[str] = []
        self.n = 0
        self.fake = td / "fake-docker"
        self.fake.write_text(FAKE_DOCKER)
        self.fake.chmod(0o755)
        self.count = td / "count"
        self.workroot = (td / "work").resolve()
        self.workroot.mkdir()
        os.environ["DEAD_MSG"] = DEAD_MSG
        os.environ["FAKE_COUNT"] = str(self.count)

    def expect(self, label: str, ok: bool, detail: str = "") -> None:
        self.n += 1
        if not ok:
            self.failures.append(f"{label}{': ' + detail if detail else ''}")

    def oracle(self, plan: str):
        """A ContainerOracle wired to the fake docker, without the docker
        handshake of __init__ (nothing here may need a daemon)."""
        self.count.unlink(missing_ok=True)
        os.environ["FAKE_PLAN"] = plan
        o = _oracle.ContainerOracle.__new__(_oracle.ContainerOracle)
        _oracle._Base.__init__(o)
        o.docker, o.workroot, o.name = str(self.fake), self.workroot, "lp-oracle-fake"
        _oracle._ORACLE = o
        return o

    def run_pdflatex(self, plan: str):
        o = self.oracle(plan)
        try:
            return o.run_pdflatex(self.workroot, ["-interaction=nonstopmode", "t.tex"],
                                  {}, 60), None
        except _oracle.OracleError as e:
            return None, e

    # ---------------------------------------------------------------- python
    def python_graders(self) -> None:
        for mode in ("dead", "daemonerr", "cut", "nobanner"):
            got, err = self.run_pdflatex(mode)
            self.expect(f"ContainerOracle.run_pdflatex grades a '{mode}' run "
                        f"(no proof pdfTeX ran) instead of raising OracleError",
                        err is not None, f"returned {got!r}")
        got, err = self.run_pdflatex("fail")
        self.expect("a GENUINE pdfTeX failure (banner, in-container rc 1) is no "
                    "longer graded rc 1", err is None and got is not None
                    and got[0] == 1 and got[2] is False, f"{got!r} {err!r}")
        got, err = self.run_pdflatex("ok")
        self.expect("a genuine pdfTeX success is not graded rc 0",
                    err is None and got is not None and got[0] == 0, f"{got!r} {err!r}")
        got, err = self.run_pdflatex("timeout")
        self.expect("an in-container timeout (rc 124) is not reported as timed out",
                    err is None and got is not None and got[2] is True, f"{got!r} {err!r}")

        # The multi-pass protocol: pass 1 a real failure, pass 2 the daemon lost.
        for plan in ("fail,dead", "ok,dead", "dead"):
            o = self.oracle(plan)
            try:
                r = o.run_to_fixpoint(self.workroot, "t.tex", {}, 60)
                self.expect(f"run_to_fixpoint graded plan '{plan}' (a pass with "
                            f"no proof pdfTeX ran) as {r!r}", False)
            except _oracle.OracleError:
                self.expect("-", True)

        # check_apply_fixes_roundtrip.pdflatex_ok: None (not graded), never False.
        import check_apply_fixes_roundtrip as rt
        for plan, want in (("dead", None), ("fail", False), ("cut", None)):
            self.oracle(plan)
            got = _silenced(rt.pdflatex_ok, self.workroot, "t.tex", None)
            self.expect(f"check_apply_fixes_roundtrip.pdflatex_ok under '{plan}' "
                        f"returned {got!r}, expected {want!r}", got is want)

        # The shim: every oracle failure AND every other exception -> INFRA_RC.
        cwd = os.getcwd()
        os.chdir(self.workroot)
        try:
            for plan in ("dead", "cut", "nobanner"):
                self.oracle(plan)
                rc = _silenced(_oracle.main, [_oracle.SHIM_COMMAND, "--timeout", "60",
                                              "-interaction=nonstopmode", "t.tex"])
                self.expect(f"the _oracle.py shim exits {rc} under '{plan}', not "
                            f"INFRA_RC={_oracle.INFRA_RC}", rc == _oracle.INFRA_RC)
            o = self.oracle("ok")

            def boom(*_a, **_k):
                raise ValueError("an unexpected bug in the oracle")
            o.run_pdflatex = boom
            rc = _silenced(_oracle.main, [_oracle.SHIM_COMMAND, "-interaction=nonstopmode", "t.tex"])
            self.expect(f"the shim exits {rc} on a non-OracleError exception, not "
                        f"INFRA_RC={_oracle.INFRA_RC} (1 would read as 'pdflatex "
                        f"failed')", rc == _oracle.INFRA_RC)
            self.oracle("fail")
            rc = _silenced(_oracle.main, [_oracle.SHIM_COMMAND, "-interaction=nonstopmode", "t.tex"])
            self.expect(f"the shim exits {rc} on a genuine pdfTeX failure, not 1", rc == 1)
        finally:
            os.chdir(cwd)
            _oracle._ORACLE = None

    # ----------------------------------------------------------------- shell
    def shell_grader(self) -> None:
        fro = (self.repo / "scripts/tools/false_ready_oracle.sh").read_text()
        funcs = {}
        for name in ("run_pdflatex", "drift_class"):
            m = re.search(rf"^{name}\(\) \{{.*?^\}}$", fro, re.M | re.S)
            if not m:
                self.expect(f"false_ready_oracle.sh no longer defines {name}()", False)
                return
            funcs[name] = m.group(0)
        eng = self.td / "fake-engine"
        eng.write_text(FAKE_ENGINE)
        eng.chmod(0o755)
        lib = self.td / "fro_funcs.sh"
        lib.write_text(funcs["run_pdflatex"] + "\n" + funcs["drift_class"] + "\n")
        wd = self.td / "wd"
        wd.mkdir(exist_ok=True)

        def run(plan: str) -> str:
            self.count.unlink(missing_ok=True)
            env = dict(os.environ, FAKE_PLAN=plan, TMPDIR=str(self.td))
            p = subprocess.run(
                ["bash", "-c", f'source "{lib}"; PDFLATEX=("{eng}"); TIMEOUT=; '
                 f'run_pdflatex "{wd}" t.tex 1'], capture_output=True, text=True,
                env=env)
            return p.stdout.strip()
        for plan in ("dead", "ok,dead", "fail,dead"):
            got = run(plan)
            # Every pass runs (success must be STABLE), so a lost SECOND pass
            # must void the result even after a genuine first one.
            self.expect(f"false_ready_oracle.sh run_pdflatex graded plan '{plan}' "
                        f"as '{got}' (a pass with no pdfTeX banner)",
                        got.startswith("NOPROOF"))
        got = run("fail")
        self.expect(f"run_pdflatex no longer grades a genuine failure rc 1 (got '{got}')",
                    got.split()[:1] == ["1"])
        # The halt run's proof must be checked BEFORE its artefacts are deleted.
        i_halt = fro.find('read -r hrc hpdf <<<"$(run_pdflatex "$rundir" "$base" 1)"')
        i_rm = fro.find('"${ORACLE_RM[@]}" "$rundir/${base%.tex}.pdf"')
        i_chk = fro.find("grep -q 'This is pdfTeX' \"$rundir/${base%.tex}.log\"")
        i_nop = fro.find("124|125|126|127|NOPROOF)")
        self.expect("false_ready_oracle.sh checks the halt run's pdfTeX log and "
                    "NOPROOF only AFTER deleting it (or not at all)",
                    -1 not in (i_halt, i_rm, i_chk, i_nop)
                    and i_halt < i_nop < i_rm and i_halt < i_chk < i_rm)
        for g, m, want in (("error-halt", "compiles", "hard-rejects"),
                           ("strong-fatal", "compiles", "hard-rejects"),
                           ("compiles", "error-halt", "hard-compiles"),
                           ("error-halt", "strong-fatal", "soft"),
                           ("compiles", "compiles", "ok")):
            p = subprocess.run(["bash", "-c", f'source "{lib}"; drift_class {g} {m}'],
                               capture_output=True, text=True)
            self.expect(f"drift_class {g} vs manifest {m} = '{p.stdout.strip()}', "
                        f"expected {want}", p.stdout.strip() == want)


def _silenced(fn, *a):
    import contextlib
    import io
    buf = io.StringIO()
    out = io.TextIOWrapper(io.BytesIO())  # the shim writes sys.stdout.buffer
    with contextlib.redirect_stderr(buf), contextlib.redirect_stdout(out):
        try:
            return fn(*a)
        except SystemExit as e:
            return e.code
        except ValueError as e:  # the injected bug below: escaping IS the finding
            return f"raised {type(e).__name__}"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", default=".")
    repo = Path(ap.parse_args().repo).resolve()
    saved = {k: os.environ.get(k) for k in ("FAKE_PLAN", "FAKE_COUNT", "DEAD_MSG")}
    with tempfile.TemporaryDirectory(prefix="oracle-infra-") as td:
        c = Checker(repo, Path(td))
        c.python_graders()
        c.shell_grader()
    for k, v in saved.items():
        if v is None:
            os.environ.pop(k, None)
        else:
            os.environ[k] = v
    if c.failures:
        print("[oracle-infra] FAIL: an oracle run without proof that pdfTeX ran "
              "would be graded:", file=sys.stderr)
        for f in c.failures:
            print(f"  - {f}", file=sys.stderr)
        return 1
    print(f"[oracle-infra] OK: {c.n} checks; every no-proof shape (dead daemon "
          f"socket, daemon error, cut stream, no banner) is refused by the Python "
          f"graders, the shim (INFRA_RC) and false_ready_oracle.sh, and a genuine "
          f"pdfTeX failure is still graded")
    return 0


if __name__ == "__main__":
    sys.exit(main())
