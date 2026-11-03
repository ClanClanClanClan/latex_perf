"""The sample-3 seal (OPEN-119), enforced: a refusal, not a convention.

Sample 3 is the VIRGIN North-Star sample: frame ranks 721-920 (offset 720,
n 200) of the 2,719-paper frame ordered by sha256(arxiv_id), drawn and graded
once, SEALED FOR MEASUREMENT ONLY (PROJECT_STATE OPEN-119): nothing is fixed,
tuned or triaged on it. Owner ruling 2026-10-21: the P2 diagnostics baseline
uses samples 1-2 ONLY, and does not read, grade, list or hash-inspect any
sample-3 document or output.

Until this module the seal was prose: diff_real_roots.py --offset 720 and
every other tool would run on sample 3 without a word (OPEN-138). This module
is the mechanical refusal for the P2 tools (p2_baseline.py calls it before it
opens the corpus, builds an oracle or reads a results artefact). It does NOT
gate the tools that legitimately RE-MEASURE sample 3 (diff_real_roots.py
--refresh-cli on results_sample3.json, gen_proven_coverage.py): changing them
would change grading blob 9859cccf, and their sample-3 runs are the sanctioned
measurement; gating them is OPEN-139.

What the refusal checks, each of which check_p2_diag.py tries to defeat:
  * the sample NUMBER: only 1 and 2 are accepted (3, "3", " 3", "03", 3.0,
    True, any other value are refused);
  * a frame WINDOW (offset, n): refused when it meets ranks [720, 920) or is
    malformed (n <= 0, a negative offset, a non-integer);
  * document IDS: refused when any is a sealed document, compared on the
    BASE id (basename, case-folded, surrounding space and the arXiv version
    suffix removed: "../papers/X", " x ", "Xv9" are X);
  * an input ARTEFACT: refused when its name (or its symlink target's) says
    sample 3, when it IS a committed sample-3 artefact under another name (a
    symlink or a hard link: same device and inode), when its JSON
    records frame offset 720 or a sealed window, or when any document id in it
    is sealed (a renamed copy);
  * the SEALED SET itself: read from corpora/real_roots/manifest_sample3.json
    by this module only, never printed; when it cannot be read, or does not
    hold exactly SEALED_N distinct ids, EVERY request is refused (an empty
    seal set must not read as "nothing is sealed").

Messages name counts only, never a sealed id.
"""
from __future__ import annotations

import json
import os
import re
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent.parent
SEALED_OFFSET = 720
SEALED_N = 200
SEALED_MANIFEST = Path("corpora/real_roots/manifest_sample3.json")
# Samples P2 may use (owner ruling 2026-10-21): number -> (offset, n, the
# results artefact under corpora/real_roots that holds its grade of record).
ALLOWED = {1: (0, 200, "results.json"), 2: (200, 200, "results_sample2.json")}
_SAMPLE3_NAME = re.compile(r"sample[_-]?0*3(?!\d)", re.I)


class SealError(Exception):
    """A request that would touch sealed sample 3."""


def base_id(x) -> str:
    s = os.path.basename(str(x).strip().rstrip("/\\")).strip().lower()
    return re.sub(r"v\d+$", "", s)


def sealed_ids(repo: Path = REPO, manifest: Path | None = None) -> frozenset:
    """The sealed set's base ids. Raises SealError (refuse everything) when
    the manifest is missing, unreadable, or does not hold SEALED_N ids."""
    p = Path(manifest) if manifest is not None else Path(repo) / SEALED_MANIFEST
    try:
        d = json.loads(p.read_text())
        frame = d.get("frame") or {}
        ids = frozenset(base_id(r["arxiv_id"]) for r in d["docs"])
    except Exception as e:  # noqa: BLE001 -- any failure means: cannot enforce
        raise SealError(f"the sample-3 seal cannot be read ({type(e).__name__}); "
                        f"refusing every request until it can") from None
    if len(ids) != SEALED_N or frame.get("offset") != SEALED_OFFSET:
        raise SealError(f"the sample-3 seal holds {len(ids)} distinct ids at offset "
                        f"{frame.get('offset')!r}, not {SEALED_N} at {SEALED_OFFSET}: "
                        f"refusing every request")
    return ids


def sample_spec(k) -> tuple[int, int, str]:
    """(offset, n, results artefact name) of an allowed sample number."""
    if isinstance(k, bool):
        raise SealError("a sample number must be 1 or 2")
    if isinstance(k, str) and re.fullmatch(r"[12]", k):
        k = int(k)
    if isinstance(k, int) and not isinstance(k, bool) and k in ALLOWED:
        return ALLOWED[k]
    raise SealError("P2 uses samples 1 and 2 only (owner ruling 2026-10-21); "
                    "sample 3 is sealed (OPEN-119) and no other sample is defined")


def refuse_window(offset, n) -> None:
    if (isinstance(offset, bool) or isinstance(n, bool) or not isinstance(offset, int)
            or not isinstance(n, int) or offset < 0 or n <= 0):
        raise SealError(f"malformed frame window (offset {offset!r}, n {n!r})")
    if offset < SEALED_OFFSET + SEALED_N and SEALED_OFFSET < offset + n:
        raise SealError(f"frame window [{offset}, {offset + n}) meets the sealed "
                        f"sample-3 ranks [{SEALED_OFFSET}, {SEALED_OFFSET + SEALED_N})")


def refuse_ids(ids, sealed: frozenset) -> None:
    hit = sum(1 for x in ids if base_id(x) in sealed)
    if hit:
        raise SealError(f"{hit} of the {len(list(ids))} requested documents are in sealed "
                        f"sample 3 (OPEN-119); P2 uses samples 1-2 only")


def _sealed_artefacts(repo: Path) -> set:
    """(st_dev, st_ino) of every committed sample-3 artefact: the identity a
    symlink OR a hard link with an innocent name still shares."""
    out = set()
    for d in ("corpora/real_roots", "corpora/oracle_baseline"):
        for p in (Path(repo) / d).glob("*"):
            if _SAMPLE3_NAME.search(p.name):
                st = os.stat(p)
                out.add((st.st_dev, st.st_ino))
    return out


def refuse_artefact(path, sealed: frozenset, repo: Path = REPO) -> dict:
    """Load a results-like JSON artefact for P2, refusing a sample-3 one.
    Returns the parsed JSON. The NAME and the symlink target are checked
    before a byte is read."""
    p = Path(path)
    if _SAMPLE3_NAME.search(p.name) or _SAMPLE3_NAME.search(p.resolve().name):
        raise SealError("the artefact's name says sample 3 (sealed, OPEN-119)")
    st = os.stat(p)
    if (st.st_dev, st.st_ino) in _sealed_artefacts(repo):
        raise SealError("the artefact is (a link to) a sealed sample-3 artefact")
    d = json.loads(p.read_text())
    frame = d.get("frame") if isinstance(d, dict) else None
    if isinstance(frame, dict) and "offset" in frame:
        refuse_window(frame.get("offset"), frame.get("n", SEALED_N))
    if isinstance(d, dict) and isinstance(d.get("sample"), (int, str)):
        sv = str(d["sample"])
        if re.fullmatch(r"\s*0*3\s*", sv) or re.search(r"\bsample\s*0*3\b", sv, re.I):
            raise SealError("the artefact records sample 3 (sealed, OPEN-119)")
    rows = []
    if isinstance(d, dict):
        for key in ("docs", "rows"):
            if isinstance(d.get(key), list):
                rows += d[key]
    refuse_ids([r.get("arxiv_id", "") for r in rows if isinstance(r, dict)], sealed)
    return d
