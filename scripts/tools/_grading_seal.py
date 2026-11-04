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
    OPEN-128's re-grade), but its own output is AGGREGATES ONLY, by an
    ALLOW-LIST (C-197; the review of 82638518 showed a deny-list of
    id-bearing lines leaks: the "false-READY classes" line carries no id, a
    multi-line first error spills onto lines without one): a line of stdout
    or stderr is printed only when it matches one of AGGREGATE_LINES -- fixed
    templates of counts, rates, shas and fixed vocabulary -- and every other
    line is withheld; the number withheld is reported at exit;
  * a tool refuses, in that mode, every option that writes a per-row file
    besides its results file (`side_outputs`: diff_real_roots's --diff-out
    and --experiment-out).
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
_CELL = r"(true-READY|true-NOT-READY|FALSE-READY|false-NOT-READY|ungraded-infra|ungraded-timeout)"
# The ONLY lines a sealed measurement prints (full-line matches): aggregates.
AGGREGATE_LINES = [re.compile(x) for x in (
    r"",
    r"\[real-roots\] oracle : pdfTeX [0-9.\-]+ .*\(container:[\w./@:\-]+\)",
    r"\[real-roots\] frame  : [0-9]+ papers, sampled [0-9]+ by sha256\(arxiv_id\) ascending",
    r"\[real-roots\]   " + _CELL + r" +[0-9]+",
    r"\[real-roots\] over-rejection: [0-9]+/[0-9]+ graded = [0-9.]+%",
    r"\[real-roots\] correct verdicts: [0-9]+/[0-9]+ = [0-9.]+%",
    r"\[real-roots\] refreshed: [0-9]+ cell change\(s\)",
    r"\[real-roots\] measured_at_sha = [0-9a-f]{7,40}",
    r"\[real-roots\] [0-9]+ cell\(s\) changed:",
    r"\[real-roots\] counts now: \{('" + _CELL + r"': [0-9]+(, )?)*\}",
    r"\[real-roots\] recorded [0-9]+ rows to [\w./\-]+/",
    r"\[real-roots\] PASS",
    r"\[gen-proven-coverage\] [\w./\-]+: [0-9]+ rows, lp-core certified\+compiles = [0-9]+",
    r"[{}],?",
    r" *\"[a-z_]+\": ([0-9]+|\{),?",
    r" *\},?",
    r"\[sealed\] .*",
)]


def side_outputs(tool: str, **opts) -> None:
    """In a sealed measurement, refuse (SystemExit 2) every option that
    writes per-row output besides the results file."""
    given = sorted(k for k, v in opts.items() if v)
    if given:
        print(f"[{tool}] REFUSED (OPEN-139, C-197): {', '.join('--' + g.replace('_', '-') for g in given)} "
              f"writes per-row output; a sealed measurement writes its results file "
              f"only", file=sys.__stderr__)   # names options only, never a row
        raise SystemExit(2)


class _Withhold(io.TextIOBase):
    """A line filter over a text stream: a line is passed only when it is an
    aggregate (AGGREGATE_LINES, a full match) and carries no id."""

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
        body = line.rstrip("\n")
        if not ANY_ID.search(body) and any(t.fullmatch(body) for t in AGGREGATE_LINES):
            self.inner.write(line)
        else:
            self.counter[0] += 1

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


def ids_in(obj) -> list:
    """Every string anywhere in a JSON value that is a document id (the
    strict ID_RE): what a tool reading a recorded artefact will touch."""
    out = []
    if isinstance(obj, str):
        if S.ID_RE.fullmatch(obj):
            out.append(obj)
    elif isinstance(obj, dict):
        for k, v in obj.items():
            out += ids_in(k) + ids_in(v)
    elif isinstance(obj, (list, tuple)):
        for v in obj:
            out += ids_in(v)
    return out


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
