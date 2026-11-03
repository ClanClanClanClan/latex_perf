#!/usr/bin/env python3
"""Reproduce corpora/real_roots/manifest_p2_heldout.json (ruling R3: the P2
held-out set, frame offsets 920-1999) from frame METADATA ONLY.

  build_p2_heldout.py --corpus-root R --check    compare with the committed file
  build_p2_heldout.py --corpus-root R --write    rewrite it (a visible change;
                                                 the seal's pin must then change too)

The frame is diff_real_roots.build_frame's: a paper is in the frame when its
00README.json declares compiler pdflatex and exactly one toplevel, and that
toplevel exists. This script reads ONLY 00README.json files and calls
is_file() on the toplevel -- no document is opened (check_p2_diag.py traces
every file it opens on a synthetic corpus and fails if anything else is
read). The order is sha256(arxiv_id) ascending; the window is [920, 2000).

The manifest records ids and verification counts only: the frame size, that
samples 1-3 equal their ranks (compared with the committed grades of record
and the sample-3 seal, as sets; no id is printed), and that the window's ids
are valid, distinct and disjoint from samples 1-3.

Exit 0 ok / identical; 1 the committed manifest differs; 2 a precondition.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import _sample_seal as seal  # noqa: E402

REPO = HERE.parent.parent
OFFSET, N = seal.HELDOUT_OFFSET, seal.HELDOUT_N
CORPUS_NAME = "LP_v24_FULL_BACKUP_20250716_165548/corpus/papers"
PURPOSE = ("P2 held-out set (ruling R3, the assistant's recommendations of 2026-11-03 "
           "adopted by the owner): measurement only, aggregate output only, one "
           "pre-registered run per milestone; no P2 design, triage or per-document "
           "reading. Sealed by scripts/tools/_sample_seal.py (SEALS).")


def frame_ids(root: Path) -> list[str]:
    """build_frame's membership rule, metadata only, sorted by sha256(id)."""
    from diff_real_roots import build_frame
    return [r["arxiv_id"] for r in sorted(
        build_frame(Path(root)), key=lambda r: hashlib.sha256(r["arxiv_id"].encode()).hexdigest())]


def build(root: Path, repo: Path = REPO, frame_size: int = 2719) -> dict:
    ids = frame_ids(root)
    s1 = {d["arxiv_id"] for d in json.loads(seal.committed(repo, seal.ALLOWED[1][2])[0])["docs"]}
    s2 = {d["arxiv_id"] for d in json.loads(seal.committed(repo, seal.ALLOWED[2][2])[0])["docs"]}
    s3 = {seal.paper_key(d["arxiv_id"]) for d in
          json.loads(seal.committed(repo, seal.SEALED_MANIFEST)[0])["docs"]}
    win = ids[OFFSET:OFFSET + N]
    checks = {"frame_size": len(ids),
              "sample1_equals_ranks_0_200": set(ids[0:200]) == s1,
              "sample2_equals_ranks_200_400": set(ids[200:400]) == s2,
              "sample3_equals_ranks_720_920": {seal.paper_key(x) for x in ids[720:920]} == s3,
              "window_920_2000_size": len(win),
              "window_ids_valid": all(seal.ID_RE.fullmatch(x) for x in win),
              "window_disjoint_from_samples_1_3": not (set(win) & (s1 | s2))
              and not ({seal.paper_key(x) for x in win} & s3)}
    return {"purpose": PURPOSE,
            "frame": {"corpus": CORPUS_NAME, "frame_size": frame_size,
                      "selection": "sha256(arxiv_id) ascending", "offset": OFFSET, "n": N},
            "built": {"date": "2026-11-03",
                      "rule": "diff_real_roots.build_frame (00README.json: compiler pdflatex, "
                              "exactly one toplevel, toplevel exists) then sorted by "
                              "sha256(arxiv_id); ranks [920, 2000)",
                      "read": "00README.json metadata and a stat of each toplevel only; no "
                              "document in the window was read",
                      "verification": checks},
            "docs": [{"arxiv_id": x} for x in win]}


def render(man: dict) -> str:
    return json.dumps(man, indent=1) + "\n"


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--corpus-root", required=True)
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--check", action="store_true")
    g.add_argument("--write", action="store_true")
    ns = ap.parse_args(argv)
    root = Path(ns.corpus_root)
    if not root.is_dir():
        print(f"[p2-heldout] no corpus at {root}", file=sys.stderr)
        return 2
    man = build(root)
    if not all(v is True or (isinstance(v, int) and not isinstance(v, bool))
               for v in man["built"]["verification"].values()) \
            or man["built"]["verification"]["frame_size"] != 2719:
        print(f"[p2-heldout] the frame does not verify: {man['built']['verification']}",
              file=sys.stderr)
        return 2
    path = REPO / seal.HELDOUT_MANIFEST
    if ns.write:
        path.write_text(render(man))
        print(f"[p2-heldout] wrote {path}")
        return 0
    same = path.read_text() == render(man)
    print(f"[p2-heldout] {'IDENTICAL' if same else 'DIFFERS'}: the committed manifest vs a "
          f"rebuild from frame metadata ({man['built']['verification']['frame_size']} papers, "
          f"window {len(man['docs'])})")
    return 0 if same else 1


if __name__ == "__main__":
    sys.exit(main())
