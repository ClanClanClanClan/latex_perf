"""The sample-3 seal in the GRADING tools (OPEN-139; ruling R5, the
assistant's recommendations of 2026-11-03, adopted by the owner).

Sample 3 (frame offsets 720-919) is the virgin North-Star sample, sealed for
the verdict tier's measurement only (OPEN-119). Until this module only the P2
tools refused it (Track E's `_sample_seal.py`, copied here UNCHANGED from
feat/v27165-p2-baseline @ b186c73a, so both branches carry one design); the
grading tools ran on it and printed each document's id, cell and first
error: diff_real_roots.py (`--offset 720`, `--results results_sample3.json`),
gen_proven_coverage.py and measure_strict_boundary.py.

Every request of those tools now goes through `gate`:
  * it reads the seal from the COMMITTED manifest (`_sample_seal.sealed_ids`)
    and refuses everything when it cannot (fail closed);
  * a request whose frame window meets the sealed window, or whose documents
    include a sealed paper, is REFUSED unless the caller asked for
    `--sealed-measurement`;
  * in that MEASUREMENT-ONLY mode the tool still writes its results file
    (the re-grade the protocol needs: OPEN-119's sanctioned re-measurement,
    OPEN-128's re-grade), but its own output is AGGREGATES ONLY: every
    line of stdout or stderr that carries an arXiv id is withheld (so no
    per-row id, cell or first error is printed), and the number withheld is
    reported at exit.
Messages name counts only, never a sealed id.
"""
from __future__ import annotations

import atexit
import io
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import _sample_seal as S  # noqa: E402

# Any arXiv-id-shaped token: new style with or without a version, old style.
ANY_ID = re.compile(r"(?<![0-9])[0-9]{4}\.[0-9]{4,5}(?:v[0-9]+)?(?![0-9])"
                    r"|(?<![A-Za-z])[a-z][a-z\-]*(?:\.[A-Z]{2})?/[0-9]{7}(?:v[0-9]+)?")
FLAG = "--sealed-measurement"


class _Withhold(io.TextIOBase):
    """A line filter over a text stream: lines carrying an id are dropped."""

    def __init__(self, inner, counter: list):
        self.inner, self.buf, self.counter = inner, "", counter

    def writable(self) -> bool:
        return True

    def write(self, s: str) -> int:
        self.buf += s
        while "\n" in self.buf:
            line, self.buf = self.buf.split("\n", 1)
            self._emit(line + "\n")
        return len(s)

    def _emit(self, line: str) -> None:
        if ANY_ID.search(line):
            self.counter[0] += 1
        else:
            self.inner.write(line)

    def flush(self) -> None:
        if self.buf:
            self._emit(self.buf)
            self.buf = ""
        self.inner.flush()


def _install() -> None:
    counter = [0]
    real_err = sys.stderr
    sys.stdout = _Withhold(sys.stdout, counter)
    sys.stderr = _Withhold(sys.stderr, counter)

    def report():
        try:
            sys.stdout.flush()
            sys.stderr.flush()
        except (OSError, ValueError):
            pass   # a closed stream at interpreter exit: the report below still goes out
        real_err.write(f"[sealed] measurement-only (OPEN-139): {counter[0]} "
                       f"per-document line(s) withheld; aggregates only\n")
    atexit.register(report)


def gate(tool: str, ids=(), window=None, measurement: bool = False,
         repo: Path | None = None) -> bool:
    """Refuse (SystemExit 2) a request that touches a sealed set without
    `--sealed-measurement`, or any request when the seal cannot be read.
    Returns True (and withholds per-document output from here on) for an
    allowed sealed measurement, False for a request that touches no seal."""
    repo = Path(repo) if repo is not None else S.REPO
    try:
        sealed = S.sealed_ids(repo)
        touched = 0
        if window is not None:
            try:
                S.refuse_window(*window)
            except S.SealError:
                touched += 1
        ids = list(ids)
        touched += sum(1 for x in ids if S.paper_key(x) in sealed)
    except S.SealError as e:
        print(f"[{tool}] REFUSED (OPEN-139): {e}", file=sys.stderr)
        raise SystemExit(2) from None
    if not touched:
        return False
    if not measurement:
        print(f"[{tool}] REFUSED (OPEN-139): the request touches sealed sample 3 "
              f"({touched} sealed document(s) or window); sample 3 is graded only "
              f"as a measurement (OPEN-119): pass {FLAG}, which writes the results "
              f"file and prints aggregates only", file=sys.stderr)
        raise SystemExit(2)
    _install()
    return True
