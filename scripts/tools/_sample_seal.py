"""The P2 seals, enforced: refusals, not conventions.

TWO SEALED SETS, both refused for every P2 use (baseline, design, scoring):
  * SAMPLE 3 -- the VIRGIN North-Star sample, frame ranks 721-920 (offset 720,
    n 200), sealed for the verdict tier's measurement only (OPEN-119). P2 may
    not use it for anything: ruling R2 (the assistant's recommendations of
    2026-11-03, adopted by the owner; RULINGS-2026-11-03.md).
  * THE P2 HELD-OUT SET -- frame offsets 920-1999 (n 1,080), ruling R3 (same
    provenance): measurement only, aggregate output only, one pre-registered
    run per milestone, no P2 design, triage or per-document reading. No P2
    command reads it today; a measuring command needs a pre-registered
    amendment (pre-registration §2.3).
Both are windows of the 2,719-paper frame ordered by sha256(arxiv_id).

Until this module the seal was prose (C-180). This module is the mechanical
refusal for the P2 tools; the other tools are OPEN-139 (R5: Track B).

FAIL CLOSED, BY ALLOW-LIST (review of 758e0e18, H1/H2): this module ACCEPTS
only what it can prove is sample 1 or 2 and refuses everything else:
  * a document id is accepted only when it is a str that fully matches the
    ASCII pattern ID_RE (new-style arXiv: 4 digits, '.', 4-5 digits, 'v',
    digits). Nothing is normalised. (MEASURED 2026-11-03: every id of samples
    1, 2, 3 and of the held-out window matches.) A paper is compared by its
    version-less key, so another version of a sealed paper is sealed too;
  * the sealed sets and the grades of record of samples 1-2 are read from
    the COMMITTED blob at HEAD (`committed`), and the working-tree file must
    equal it; the caller stamps the blob ids it read;
  * a sample is 1 or 2 (int, or exactly the string "1"/"2"); its ids are
    exactly its grade of record's 200, valid, distinct, none sealed;
  * each sealed set must hold exactly its n valid, distinct ids at its
    offset, and the sets must be disjoint, or EVERY request is refused (an
    empty seal must not read as "nothing is sealed").

Messages name counts only, never a sealed id.
"""
from __future__ import annotations

import json
import re
import subprocess
import unicodedata
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent.parent
SEALED_OFFSET = 720
SEALED_N = 200
SEALED_MANIFEST = "corpora/real_roots/manifest_sample3.json"
HELDOUT_OFFSET = 920
HELDOUT_N = 1080
HELDOUT_MANIFEST = "corpora/real_roots/manifest_p2_heldout.json"
# (name, manifest, offset, n): every set P2 must never touch.
SEALS = (("sample 3 (OPEN-119, ruling R2)", SEALED_MANIFEST, SEALED_OFFSET, SEALED_N),
         ("the P2 held-out set (ruling R3)", HELDOUT_MANIFEST, HELDOUT_OFFSET, HELDOUT_N))
# Samples P2 may use (ruling R2): number -> (offset, n, the results artefact
# that holds its grade of record).
ALLOWED = {1: (0, 200, "corpora/real_roots/results.json"),
           2: (200, 200, "corpora/real_roots/results_sample2.json")}
ID_RE = re.compile(r"[0-9]{4}\.[0-9]{4,5}v[0-9]+", re.ASCII)


class SealError(Exception):
    """A request that would touch sealed sample 3, or that cannot be proven
    not to."""


def _git(repo: Path, *args: str) -> subprocess.CompletedProcess:
    return subprocess.run(["git", "--no-optional-locks", *args], cwd=repo, capture_output=True)


def committed(repo: Path, rel: str) -> tuple[bytes, str]:
    """(bytes, git blob id) of `rel` at HEAD of `repo`; refuses (SealError)
    when it is not tracked at HEAD or the working-tree file differs."""
    rel = str(rel)
    p = _git(Path(repo), "rev-parse", f"HEAD:{rel}")
    if p.returncode != 0:
        raise SealError(f"{rel} is not committed at HEAD: P2 reads only committed inputs")
    blob = p.stdout.decode().strip()
    wt = Path(repo) / rel
    h = _git(Path(repo), "hash-object", "--", rel)
    if not wt.is_file() or wt.is_symlink() or h.returncode != 0 \
            or h.stdout.decode().strip() != blob:
        raise SealError(f"{rel} in the working tree differs from HEAD: commit it or "
                        f"restore it (P2 reads the committed blob only)")
    data = _git(Path(repo), "cat-file", "blob", blob)
    if data.returncode != 0:
        raise SealError(f"cannot read the blob of {rel}")
    return data.stdout, blob


def valid_id(x) -> str:
    """`x` when it is a valid id (ID_RE, exact); SealError otherwise."""
    if not isinstance(x, str) or not ID_RE.fullmatch(x):
        raise SealError("a document id is not of the form NNNN.NNNNNvN (refused, not "
                        "normalised)")
    return x


def paper_key(x) -> str:
    return valid_id(x).rsplit("v", 1)[0]


def _load_seal(repo: Path, name: str, rel: str, offset: int, n: int) -> frozenset:
    try:
        data, _blob = committed(repo, rel)
        d = json.loads(data)
        frame = d.get("frame") or {}
        keys = [paper_key(r["arxiv_id"]) for r in d["docs"]]
    except SealError as e:
        raise SealError(f"the seal of {name} cannot be read ({e}); refusing every request") \
            from None
    except Exception as e:  # noqa: BLE001 -- any failure means: cannot enforce
        raise SealError(f"the seal of {name} cannot be read ({type(e).__name__}); "
                        f"refusing every request until it can") from None
    if len(keys) != n or len(set(keys)) != n or frame.get("offset") != offset \
            or frame.get("n", n) != n:
        raise SealError(f"the seal of {name} holds {len(set(keys))} distinct ids at offset "
                        f"{frame.get('offset')!r}, not {n} at {offset}: refusing every request")
    return frozenset(keys)


def sealed_ids(repo: Path = REPO) -> frozenset:
    """The paper keys of EVERY sealed set (SEALS), from the committed
    manifests. SealError (refuse everything) when one is missing, edited,
    unreadable, not exactly its n valid distinct ids at its offset, or when
    two sets overlap."""
    sets = [_load_seal(repo, *s) for s in SEALS]
    union = frozenset().union(*sets)
    if len(union) != sum(len(x) for x in sets):
        raise SealError("the sealed sets overlap: refusing every request")
    return union


def seal_blobs(repo: Path = REPO) -> dict:
    return {rel: committed(repo, rel)[1] for _name, rel, _o, _n in SEALS}


def seal_blob(repo: Path = REPO) -> str:
    """One id for every seal manifest's blob (the stamp a record carries)."""
    return ",".join(f"{rel}={b}" for rel, b in sorted(seal_blobs(repo).items()))


def sample_spec(k) -> tuple[int, int, str]:
    """(offset, n, grade-of-record path) of an allowed sample number."""
    if isinstance(k, bool):
        raise SealError("a sample number must be 1 or 2")
    if isinstance(k, str) and k in ("1", "2"):
        k = int(k)
    if type(k) is int and k in ALLOWED:
        return ALLOWED[k]
    raise SealError("P2 uses samples 1 and 2 only (ruling R2 of 2026-11-03); "
                    "sample 3 is sealed (OPEN-119) and no other sample is defined")


def refuse_window(offset, n) -> None:
    if type(offset) is not int or type(n) is not int or offset < 0 or n <= 0:
        raise SealError(f"malformed frame window (offset {offset!r}, n {n!r})")
    for name, _rel, so, sn in SEALS:
        if offset < so + sn and so < offset + n:
            raise SealError(f"frame window [{offset}, {offset + n}) meets {name}, offsets "
                            f"[{so}, {so + sn})")


def refuse_ids(ids, sealed: frozenset) -> None:
    """Every id valid (refused, not normalised, otherwise) and none sealed."""
    ids = list(ids)
    hit = sum(1 for x in ids if paper_key(x) in sealed)
    if hit:
        raise SealError(f"{hit} of the {len(ids)} requested documents are in a sealed set "
                        f"(sample 3 or the P2 held-out set); P2 uses samples 1-2 only "
                        f"(rulings R2, R3)")


_SAMPLE3_NAME = re.compile(r"sample0*3(?![0-9])|(?<![a-z0-9])s0*3(?![0-9])|heldout")


def refuse_name(path) -> None:
    """A belt over the allow-list: refuse a path whose NFKC-folded name says
    sample 3 (separators and case ignored)."""
    name = unicodedata.normalize("NFKC", Path(path).name).lower()
    squeezed = re.sub(r"[^a-z0-9.]", "", name)
    if _SAMPLE3_NAME.search(squeezed) or _SAMPLE3_NAME.search(name):
        raise SealError("the path's name says sample 3 or the held-out set (sealed)")


def sample_docs(repo: Path, k, sealed: frozenset) -> tuple[list[dict], str, str]:
    """(docs, grade-of-record path, its blob) of allowed sample `k`, read
    from HEAD: exactly n rows, every id valid, distinct by paper, none
    sealed. Refuses (SealError) otherwise."""
    offset, n, rel = sample_spec(k)
    refuse_window(offset, n)
    data, blob = committed(repo, rel)
    try:
        docs = json.loads(data)["docs"]
    except Exception:  # noqa: BLE001
        raise SealError(f"{rel} has no `docs` list") from None
    if not isinstance(docs, list) or len(docs) != n:
        raise SealError(f"{rel} holds {len(docs) if isinstance(docs, list) else '?'} rows, "
                        f"not {n}")
    if any(not isinstance(d, dict) for d in docs):
        raise SealError(f"{rel} has a row that is not an object")
    keys = [paper_key(d.get("arxiv_id")) for d in docs]
    if len(set(keys)) != n:
        raise SealError(f"{rel} repeats a paper")
    refuse_ids([d["arxiv_id"] for d in docs], sealed)
    return docs, rel, blob
