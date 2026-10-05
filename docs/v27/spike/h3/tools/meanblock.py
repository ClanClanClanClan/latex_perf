#!/usr/bin/env python3
"""The terminal input of H.3's meaning dump, generated from the committed kernel contract.

usage: meanblock.py REPO OUTDIR [N]

Writes OUTDIR/stdin-meanings: "&pdflatex", then the contract generator's own dump_block
(scripts/tools/gen_contract.py; no actives, no UTF-8 sweep) for the contract's names in its
order, then "\\csname @@end\\endcsname"; and OUTDIR/names.json, the names in that order (what
meandigest.py reads). With N, only the first N names (a prefix, for memory measurements).
The names are those of corpora/contracts/kernel/aarch64-a476533c0d6e64f0.json, whose
meanings_sha256 (4879fa65...) the pinned binary reproduces from this input (H3-report.md)."""
import hashlib
import json
import sys
from pathlib import Path

repo, out = Path(sys.argv[1]), Path(sys.argv[2])
sys.path.insert(0, str(repo / "scripts" / "tools"))
import gen_contract as g  # noqa: E402

k = json.loads((repo / "corpora/contracts/kernel/aarch64-a476533c0d6e64f0.json").read_text())
names = list(k["names"])
if len(sys.argv) > 3:
    names = names[:int(sys.argv[3])]
block, unwritable = g.dump_block([g.name_bytes(n) for n in names], actives=False, u8_sweep=False)
assert not unwritable, unwritable
stdin = b"&pdflatex\n" + block + b"\\csname @@end\\endcsname\n"
out.mkdir(parents=True, exist_ok=True)
(out / "stdin-meanings").write_bytes(stdin)
(out / "names.json").write_text(json.dumps(names))
print(json.dumps({"names": len(names), "stdin_bytes": len(stdin), "stdin_sha256": hashlib.sha256(stdin).hexdigest()}))
