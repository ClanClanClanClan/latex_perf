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

Round 3 (2026-09-27): proof that pdfTeX RAN is not proof its rc is the
DOCUMENT's. MEASURED: with the work root full, pdfTeX prints its banner, fails
on its own output ("I can't write on file `t.log'", "fwrite() failed") and
exits 1, which every grader graded FAILS. So a run is also refused when the
work root is below a free-space floor (before and after the run) or pdfTeX
could not write its own output; a document's own \\openout refusal is still
graded. Known residuals are listed in OPEN-118 (OOM-as-timeout, clock, VM disk).

C-91 (2026-09-28): ONE grading environment. `grading_env` drives every entry
point (run_pdflatex, the shim on the container and native backends,
check_apply_fixes_roundtrip.pdflatex_ok) under a HOSTILE host environment and
reads back what reached the engine: exactly ORACLE_TEX_VARS, a private
TEXMFHOME/TEXMFVAR, no other TeX variable; `_oracle.sh` must route both
backends through the shim; image_command must start no engine by any route.

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
#   fwrite    banner, then pdfTeX failing to write its PDF, nonce line rc=1
#             (the MEASURED disk-full shape, OPEN-118 review round 3)
#   cantlog   banner, then "! I can't write on file `t.log'.", nonce rc=1
#   openout   banner, then the DOCUMENT's own \openout refused under
#             openout_any=p ("I can't write on file `../x.tex'"), nonce rc=1:
#             a real document failure, must still be graded
FAKE_DOCKER = r'''#!/usr/bin/env python3
import os, sys
a = sys.argv[1:]
if os.environ.get("FAKE_ARGV"):
    open(os.environ["FAKE_ARGV"], "w").write("\0".join(a))
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
elif mode == "fwrite":
    sys.stdout.write(banner + "!pdfTeX error: pdflatex (file t.pdf): fwrite() failed\n"); rcline(1)
elif mode == "cantlog":
    sys.stdout.write(banner + "! I can't write on file `t.log'.\n"); rcline(1)
elif mode == "openout":
    sys.stdout.write(banner + "! I can't write on file `../x.tex'.\n"); rcline(1)
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
  fwrite) echo "This is pdfTeX, Version 3.141592653-2.6-1.40.29"
          echo "!pdfTeX error: pdflatex (file t.pdf): fwrite() failed"; exit 1 ;;
  openout) echo "This is pdfTeX, Version 3.141592653-2.6-1.40.29"
          echo "! I can't write on file \`../x.tex'."; exit 1 ;;
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

    def tv(self) -> dict:
        """A graded run's private TEXMFHOME/TEXMFVAR (required since C-91)
        with the protocol's variables: what tex_env gives a grader."""
        return _oracle.oracle_tex_vars(self.workroot / "tx")

    def run_pdflatex(self, plan: str):
        o = self.oracle(plan)
        try:
            return o.run_pdflatex(self.workroot, ["-interaction=nonstopmode", "t.tex"],
                                  self.tv(), 60), None
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

        # OPEN-118 review round 3: proof pdfTeX ran is not proof its rc is the
        # document's. pdfTeX failing to write its OWN output (the measured
        # disk-full shape) is refused; the document's own \openout refusal is
        # still a grade.
        for mode in ("fwrite", "cantlog"):
            got, err = self.run_pdflatex(mode)
            self.expect(f"ContainerOracle.run_pdflatex grades a '{mode}' run "
                        f"(pdfTeX could not write its own output: disk full) "
                        f"instead of raising OracleError", err is not None,
                        f"returned {got!r}")
        got, err = self.run_pdflatex("openout")
        self.expect("a document's own \\openout refused under openout_any=p "
                    "(banner, rc 1) is no longer graded rc 1",
                    err is None and got is not None and got[0] == 1,
                    f"{got!r} {err!r}")
        # The free-space floor, BEFORE the run: nothing may even start.
        saved = os.environ.get("LP_ORACLE_MIN_FREE_MB")
        os.environ["LP_ORACLE_MIN_FREE_MB"] = str(10 ** 12)
        try:
            got, err = self.run_pdflatex("ok")
            self.expect("ContainerOracle.run_pdflatex runs (and grades) with "
                        "the work root below the free-space floor",
                        err is not None and not self.count.exists(),
                        f"returned {got!r}, engine started: {self.count.exists()}")
        finally:
            if saved is None:
                os.environ.pop("LP_ORACLE_MIN_FREE_MB", None)
            else:
                os.environ["LP_ORACLE_MIN_FREE_MB"] = saved
        # ... and AFTER it: space that runs out DURING a run.
        real_free = _oracle._free_bytes
        seq = iter([10 ** 15, 0])
        _oracle._free_bytes = lambda _d: next(seq, 0)
        try:
            got, err = self.run_pdflatex("ok")
            self.expect("ContainerOracle.run_pdflatex grades a run after which "
                        "the work root is below the free-space floor",
                        err is not None, f"returned {got!r}")
        finally:
            _oracle._free_bytes = real_free

        # The multi-pass protocol: pass 1 a real failure, pass 2 the daemon lost.
        for plan in ("fail,dead", "ok,dead", "dead"):
            o = self.oracle(plan)
            try:
                r = o.run_to_fixpoint(self.workroot, "t.tex", self.tv(), 60)
                self.expect(f"run_to_fixpoint graded plan '{plan}' (a pass with "
                            f"no proof pdfTeX ran) as {r!r}", False)
            except _oracle.OracleError:
                self.expect("-", True)

        # check_apply_fixes_roundtrip.pdflatex_ok: None (not graded), never False.
        import check_apply_fixes_roundtrip as rt
        for plan, want in (("dead", None), ("fail", False), ("cut", None),
                           ("fwrite", None), ("cantlog", None)):
            self.oracle(plan)
            got = _silenced(rt.pdflatex_ok, self.workroot, "t.tex", None)
            self.expect(f"check_apply_fixes_roundtrip.pdflatex_ok under '{plan}' "
                        f"returned {got!r}, expected {want!r}", got is want)

        # The shim: every oracle failure AND every other exception -> INFRA_RC.
        cwd = os.getcwd()
        os.chdir(self.workroot)
        try:
            for plan in ("dead", "cut", "nobanner", "fwrite"):
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

    # ------------------------------------------------ the contract generator
    def generator_client(self) -> None:
        """gen_contract.py is a CLIENT of the oracle (run_engine), not a runner
        of its own: its jobs get the same proof-of-run refusals, the engine it
        names reaches the container, exactly the TeX variables it passes cross
        (on the native backend too: no host TeX variable leaks in), and an
        oracle failure stops the generator instead of reading as a TeX
        outcome."""
        tv = _oracle.oracle_tex_vars(self.workroot / "tx")
        for mode in ("dead", "daemonerr", "cut", "nobanner", "fwrite"):
            o = self.oracle(mode)
            try:
                got = o.run_engine(self.workroot, _oracle.ENGINE_PDFTEX,
                                   ["-ini", "-jobname=t", "\\dump"], tv, 60)
                self.expect(f"run_engine returned {got!r} for a '{mode}' run "
                            f"instead of raising OracleError", False)
            except _oracle.OracleError:
                self.expect("-", True)
        argv_file = self.td / "argv"
        os.environ["FAKE_ARGV"] = str(argv_file)
        try:
            o = self.oracle("fail")
            got = o.run_engine(self.workroot, _oracle.ENGINE_PDFTEX, ["-ini", "t.tex"],
                               dict(tv, FORCE_SOURCE_DATE="1"), 60)
            a = argv_file.read_text().split("\0")
            i = a.index("-c")
            fwd = sorted(a[j + 1] for j in range(len(a) - 1)
                         if a[j] == "-e" and j < i)
            want = sorted(["HOME=/tmp"] + [f"{k}={v}" for k, v in
                                           dict(tv, FORCE_SOURCE_DATE="1").items()])
            self.expect("run_engine: a genuine failure is rc 1, the engine reaches "
                        "the container after the nonce and timeout, and exactly "
                        "the caller's TeX variables are forwarded",
                        got[0] == 1 and a[i + 5] == _oracle.ENGINE_PDFTEX
                        and a[i + 6:] == ["-ini", "t.tex"] and fwd == want,
                        f"{got!r} {a[i + 3:]} {fwd}")
            # Run the in-container script itself (a fake `timeout` that drops
            # its options, an engine path that proves it ran): the script must
            # start the engine it was GIVEN, not a name of its own.
            tb = self.td / "tbin"
            tb.mkdir(exist_ok=True)
            (tb / "timeout").write_text('#!/bin/sh\nshift 3\nexec "$@"\n')
            (tb / "timeout").chmod(0o755)
            probe = tb / "given-engine"
            probe.write_text("#!/bin/sh\necho GIVEN-ENGINE-RAN \"$@\"\n")
            probe.chmod(0o755)
            r = subprocess.run(["sh", "-c", a[i + 1], "sh", "N", "60", str(probe), "x.tex"],
                               capture_output=True, text=True,
                               env=dict(os.environ, PATH=f"{tb}:/usr/bin:/bin"))
            self.expect("the in-container script runs the engine run_engine names",
                        "GIVEN-ENGINE-RAN x.tex" in r.stdout and "N=0" in r.stderr,
                        f"{r.stdout!r} {r.stderr!r}")
        finally:
            os.environ.pop("FAKE_ARGV", None)
        # An engine the oracle does not run (named through _oracle's table,
        # not spelled here: check_oracle_pin scans this file).
        not_run = sorted(_oracle.TEX_ENGINE_BINARIES - set(_oracle.ENGINES))[0]
        for bad_engine, bad_vars in ((not_run, tv), (_oracle.ENGINE_PDFTEX,
                                                   dict(tv, PATH="/host/bin"))):
            o = self.oracle("ok")
            try:
                o.run_engine(self.workroot, bad_engine, ["t.tex"], bad_vars, 60)
                self.expect(f"run_engine accepted engine {bad_engine!r} with "
                            f"variables {sorted(bad_vars)}", False)
            except _oracle.OracleError:
                self.expect("-", True)
        try:
            self.oracle("ok").image_command([_oracle.ENGINE_PDFLATEX, "t.tex"])
            self.expect("image_command started a TeX engine", False)
        except _oracle.OracleError:
            self.expect("-", True)
        # Native backend: the host's TeX variables never cross into a
        # run_engine job; only the caller's do. A fake engine on PATH dumps
        # the environment it received.
        bindir = self.td / "bin"
        bindir.mkdir(exist_ok=True)
        fake = bindir / _oracle.ENGINE_PDFTEX
        envdump = self.td / "envdump"
        fake.write_text("#!/bin/sh\necho 'This is pdfTeX, Version 3.141592653'\n"
                        f"env > '{envdump}'\nexit 0\n")
        fake.chmod(0o755)
        saved = {k: os.environ.get(k) for k in ("PATH", "openin_any", "max_print_line")}
        os.environ.update(PATH=f"{bindir}:{os.environ.get('PATH', '')}",
                          openin_any="a", max_print_line="79")
        try:
            n = _oracle.NativeOracle.__new__(_oracle.NativeOracle)
            _oracle._Base.__init__(n)
            rc, _, _ = n.run_engine(self.workroot, _oracle.ENGINE_PDFTEX, ["t.tex"], tv, 60)
            got = dict(x.split("=", 1) for x in envdump.read_text().splitlines()
                       if "=" in x)
            self.expect("native run_engine: the caller's TeX variables and no host "
                        "TeX variable", rc == 0 and got.get("openin_any") == "p"
                        and "max_print_line" not in got
                        and all(got.get(k) == v for k, v in tv.items()),
                        str({k: got.get(k) for k in ("openin_any", "max_print_line")}))
        finally:
            for k, v in saved.items():
                if v is None:
                    os.environ.pop(k, None)
                else:
                    os.environ[k] = v
        # The generator itself: an oracle failure is never a TeX outcome.
        import gen_contract as gc
        o = self.oracle("dead")
        tex = gc.Tex(_oracle.IMAGE, oracle=o)
        try:
            tex.pdflatex(tex.job("x"), b"\\relax\n")
            self.expect("gen_contract.Tex.pdflatex returned a result for a "
                        "'dead' run", False)
        except SystemExit as e:
            self.expect("gen_contract.Tex.pdflatex: a 'dead' run is not reported "
                        "as INFRASTRUCTURE", "INFRASTRUCTURE" in str(e.code), str(e.code))
        finally:
            tex.close()
            _oracle._ORACLE = None

    # ------------------------------------------- the ONE grading environment
    def grading_env(self) -> None:
        """C-91 (OPEN-118 known limit (b)): every GRADED run gets exactly the
        protocol's TeX environment, whoever calls the oracle and whatever the
        host exports -- ORACLE_TEX_VARS imposed, a private TEXMFHOME/TEXMFVAR
        required, every other TeX-shaping variable dropped. Before, the shim
        forwarded the host's values (or none: no SOURCE_DATE_EPOCH, no
        openin_any/openout_any), the native shell path ran a bare pdflatex,
        and check_apply_fixes_roundtrip passed the host environment. Each
        entry point is driven here with a HOSTILE host environment and the
        variables that reach the engine are read back: from the fake docker's
        argv (container) and from a fake engine's environment (native)."""
        hostile = {"SOURCE_DATE_EPOCH": "1700000000", "openin_any": "a",
                   "openout_any": "a", "FORCE_SOURCE_DATE": "1",
                   "max_print_line": "1000", "TEXINPUTS": f"{self.workroot}/inp:"}
        want_fixed = dict(_oracle.ORACLE_TEX_VARS)
        argv_file = self.td / "argv-env"

        def forwarded() -> dict:
            a = argv_file.read_text().split("\0")
            i = a.index("-c")
            return dict(a[j + 1].split("=", 1) for j in range(len(a) - 1)
                        if a[j] == "-e" and j < i)

        def exactly_protocol(got: dict, texmf_host: str | None) -> str:
            """'' when `got` is the protocol's environment, else what is wrong."""
            bad = []
            for k, v in want_fixed.items():
                if got.get(k) != v:
                    bad.append(f"{k}={got.get(k)!r} (protocol {v!r})")
            for k in ("FORCE_SOURCE_DATE", "max_print_line", "TEXINPUTS"):
                if k in got:
                    bad.append(f"host {k}={got[k]!r} reached the engine")
            for k in ("TEXMFHOME", "TEXMFVAR"):
                if not got.get(k) or got.get(k) == texmf_host:
                    bad.append(f"{k}={got.get(k)!r} is not a private per-run one")
            return "; ".join(bad)

        saved = {k: os.environ.get(k) for k in list(hostile) + ["FAKE_ARGV",
                                                                  "TEXMFHOME"]}
        os.environ["FAKE_ARGV"] = str(argv_file)
        host_th = str(self.workroot / "host-th")
        try:
            # (1) the Python API: a caller dict carrying the hostile values.
            o = self.oracle("ok")
            o.run_pdflatex(self.workroot, ["-interaction=nonstopmode", "t.tex"],
                           dict(self.tv(), **hostile), 60)
            why = exactly_protocol(forwarded(), None)
            self.expect("ContainerOracle.run_pdflatex forwards a caller's TeX "
                        "variables instead of imposing the protocol's", not why, why)
            # (2) no private TEXMF: refused, not run in the shared TEXMFVAR.
            o = self.oracle("ok")
            try:
                o.run_pdflatex(self.workroot, ["t.tex"], dict(want_fixed), 60)
                self.expect("run_pdflatex graded a run with no private "
                            "TEXMFHOME/TEXMFVAR (the container's persistent "
                            "TEXMFVAR would carry state)", False)
            except _oracle.OracleError:
                self.expect("-", True)
            # (3) the shim, under a hostile HOST environment.
            os.environ.update(hostile, TEXMFHOME=host_th)
            cwd = os.getcwd()
            os.chdir(self.workroot)
            try:
                self.oracle("ok")
                rc = _silenced(_oracle.main, [_oracle.SHIM_COMMAND, "--timeout", "60",
                                              "-interaction=nonstopmode", "t.tex"])
            finally:
                os.chdir(cwd)
            why = exactly_protocol(forwarded(), host_th) if rc == 0 else f"rc {rc}"
            self.expect("the _oracle.py pdflatex shim (the shell graders' path) "
                        "does not give its run the protocol's environment", not why,
                        why)
            # (4) the shim on the NATIVE backend (CI's tex-oracle job): a fake
            # engine on PATH dumps the environment it was started with.
            bindir = self.td / "nbin"
            bindir.mkdir(exist_ok=True)
            dump = self.td / "native-env"
            eng = bindir / _oracle.ENGINE_PDFLATEX
            eng.write_text("#!/bin/sh\necho 'This is pdfTeX, Version 3.141592653'\n"
                           f"env > '{dump}'\nexit 0\n")
            eng.chmod(0o755)
            n = _oracle.NativeOracle.__new__(_oracle.NativeOracle)
            _oracle._Base.__init__(n)
            _oracle._ORACLE = n
            path = os.environ.get("PATH", "")
            os.environ["PATH"] = f"{bindir}:{path}"
            os.chdir(self.workroot)
            try:
                rc = _silenced(_oracle.main, [_oracle.SHIM_COMMAND, "--timeout", "60",
                                              "-interaction=nonstopmode", "t.tex"])
            finally:
                os.chdir(cwd)
                os.environ["PATH"] = path
            got = (dict(x.split("=", 1) for x in dump.read_text().splitlines()
                        if "=" in x) if dump.exists() else {})
            why = exactly_protocol(got, host_th) if rc == 0 else f"rc {rc}"
            self.expect("the shim on the native backend does not give its run the "
                        "protocol's environment", not why, why)
            for k in hostile:
                os.environ.pop(k, None)
            os.environ.pop("TEXMFHOME", None)
            # (5) check_apply_fixes_roundtrip.pdflatex_ok, a grader that
            # passed `dict(os.environ)` until C-91.
            import check_apply_fixes_roundtrip as rt
            self.oracle("ok")
            got = _silenced(rt.pdflatex_ok, self.workroot, "t.tex", None)
            why = exactly_protocol(forwarded(), None) if got is not None else "not graded"
            self.expect("check_apply_fixes_roundtrip.pdflatex_ok does not grade "
                        "in the protocol's environment", not why, why)
        finally:
            _oracle._ORACLE = None
            for k, v in saved.items():
                if v is None:
                    os.environ.pop(k, None)
                else:
                    os.environ[k] = v
        # (6) the shell side: on BOTH backends oracle_setup must route every
        # run through the shim (a bare engine ran on the native one).
        osh = self.repo / "scripts/tools/_oracle.sh"
        py = str(self.repo / "scripts/tools/_oracle.py")
        stub = ('python3() { case "$2" in assert-native) return 0 ;; '
                'version) echo "pdfTeX 3.141592653-2.6-1.40.29" ;; '
                f'workroot) echo "{self.td}/wr" ;; esac; }}; ')
        for backend, envset in (("native", {"LP_ORACLE_IN_IMAGE": "x"}),
                                ("container", {})):
            env = {k: v for k, v in os.environ.items() if k != "LP_ORACLE_IN_IMAGE"}
            env.update(envset, ROOT=str(self.repo), TEX_TIMEOUT="30")
            p = subprocess.run(
                ["bash", "-c", stub + f'source "{osh}"; oracle_setup t 1; '
                 'printf "%s\\n" "$ORACLE_BACKEND" "$ORACLE_TIMEOUT_INSIDE" '
                 '"${PDFLATEX[@]}"'], capture_output=True, text=True, env=env)
            got = p.stdout.split("\n")
            self.expect(f"_oracle.sh ({backend}) does not run every grader's "
                        f"pdflatex through the _oracle.py shim",
                        got[:6] == [backend, "1", "python3", py,
                                    _oracle.SHIM_COMMAND, "--timeout"],
                        repr(got[:6]) + p.stderr[-200:])
        # (7) image_command (gen_contract.py's non-TeX commands) starts no
        # engine by any route: an engine as an argument another program runs,
        # a format selector, a shell that could run anything.
        eng = sorted(_oracle.TEX_ENGINE_BINARIES)
        for argv in (["xargs", "-a", "list", _oracle.ENGINE_PDFTEX],
                     ["kpsewhich", "&" + eng[0]], ["sh", "-c", "true"],
                     ["/usr/bin/" + eng[-1], "x"]):
            try:
                self.oracle("ok").image_command(argv)
                self.expect(f"image_command ran {argv[:1]}... (a TeX engine, a "
                            f"format selector or a shell)", False)
            except _oracle.OracleError:
                self.expect("-", True)
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
        osh = (self.repo / "scripts/tools/_oracle.sh").read_text()
        m = re.search(r"^oracle_vet\(\) \{.*?^\}$", osh, re.M | re.S)
        if not m:
            self.expect("_oracle.sh no longer defines oracle_vet()", False)
            return
        lib = self.td / "fro_funcs.sh"
        lib.write_text(f'ROOT="{self.repo}"\n' + m.group(0) + "\n"
                       + funcs["run_pdflatex"] + "\n" + funcs["drift_class"] + "\n")
        wd = self.td / "wd"
        wd.mkdir(exist_ok=True)

        def run(plan: str, **extra) -> str:
            self.count.unlink(missing_ok=True)
            env = dict(os.environ, FAKE_PLAN=plan, TMPDIR=str(self.td), **extra)
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
        # OPEN-118 review round 3: banner present, then pdfTeX failing to write
        # its own output (disk full) -- refused; the document's own \openout
        # refusal -- still graded; a work root below the floor -- refused
        # before any pass runs.
        for plan in ("fwrite", "ok,fwrite"):
            got = run(plan)
            self.expect(f"false_ready_oracle.sh run_pdflatex graded plan '{plan}' "
                        f"as '{got}' (pdfTeX could not write its own output)",
                        got.startswith("ENVFAIL"))
        got = run("openout")
        self.expect(f"run_pdflatex no longer grades a document's own \\openout "
                    f"refusal rc 1 (got '{got}')", got.split()[:1] == ["1"])
        got = run("ok", LP_ORACLE_MIN_FREE_MB=str(10 ** 12))
        self.expect(f"run_pdflatex graded a run with the work root below the "
                    f"free-space floor as '{got}'", got.startswith("ENVFAIL")
                    and not self.count.exists())
        # diff_compile_check.sh: the run is inline, so pin the ORDER: a vet
        # before the engine, a vet of the run's stdout after it, and the
        # refusal before any grade is computed.
        dcc = (self.repo / "scripts/tools/diff_compile_check.sh").read_text()
        i_pre = dcc.find('oracle_vet "$d" 2>/dev/null || envok=no')
        i_run = dcc.find('"${PDFLATEX[@]}" -interaction=nonstopmode -halt-on-error "$base" >"$pout"')
        i_post = dcc.find('! oracle_vet "$d" "$pout" -interaction=nonstopmode')
        i_ref = dcc.find('"ENVFAIL" "not graded')
        i_grade = dcc.find('then pl=COMPILES; else pl=FAILS; fi')
        self.expect("diff_compile_check.sh no longer vets free space before the "
                    "run AND the run's own output after it, before grading",
                    -1 not in (i_pre, i_run, i_post, i_ref, i_grade)
                    and i_pre < i_run < i_post < i_ref < i_grade)
        # The halt run's proof must be checked BEFORE its artefacts are deleted.
        i_halt = fro.find('read -r hrc hpdf <<<"$(run_pdflatex "$rundir" "$base" 1)"')
        i_rm = fro.find('"${ORACLE_RM[@]}" "$rundir/${base%.tex}.pdf"')
        i_chk = fro.find("grep -q 'This is pdfTeX' \"$rundir/${base%.tex}.log\"")
        i_nop = fro.find("124|125|126|127|NOPROOF|ENVFAIL)")
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
        c.generator_client()
        c.grading_env()
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
          f"socket, daemon error, cut stream, no banner) and every "
          f"environment-failure shape (pdfTeX unable to write its own output, "
          f"work root below the free-space floor before or after a run) is "
          f"refused by the Python graders, the shim (INFRA_RC) and the shell "
          f"graders, and a genuine pdfTeX failure (incl. a document's own "
          f"\\openout refusal) is still graded")
    return 0


if __name__ == "__main__":
    sys.exit(main())
