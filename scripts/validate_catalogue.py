#!/usr/bin/env python3
"""Catalogue compliance gate.

Verifies every rule emitted at runtime appears in the catalogue
(`specs/rules/rules_v3.yaml`). Catches drift where a new validator
ships without its corresponding spec entry, and where a spec entry
is removed but the runtime still emits the id.

Pre-v26.0 the rule definitions all lived in `latex-parse/src/validators.ml`.
v26.0 split them across `validators_l0.ml`, `validators_l1.ml`, etc.; the
top-level `validators.ml` is now a dispatcher with `include Validators_*`
clauses, so a script that only reads `validators.ml` finds 0 rules and
silently passes. Scan the full glob.

v26.2.1 introduced the labelled-arg helper-call syntax
(`mk_result ~id:"X"`, `mk_result_with_fix ~id:"X"`) alongside the
legacy record-literal syntax (`{ id = "X"; ... }`); both forms count
as runtime emissions.

Sanity check: if runtime_rules has fewer than 100 entries, the script
fails loudly. The repo ships 600+ rules; an empty/near-empty count
means either the glob broke or the regex broke — either way the gate
is not actually validating anything.
"""

from __future__ import annotations
import re
import sys
from pathlib import Path

SRC_DIR = Path("latex-parse/src")
CATALOG = Path("specs/rules/rules_v3.yaml")
PILOT = Path("specs/rules/pilot_v1.yaml")

# Conservative lower bound. Repo currently ships ~620 runtime rules;
# anything well below that flags a scope/regex breakage rather than a
# legitimate rules removal.
MIN_RUNTIME_RULES = 100

for path in (SRC_DIR, CATALOG, PILOT):
    if not path.exists():
        print(f"[catalog] ERROR: Missing required path: {path}", file=sys.stderr)
        sys.exit(2)

# Collect every runtime-emitted rule ID across the validators*.ml glob.
# Two emission patterns are accepted:
#   1. Legacy record literal:    { id = "FAMILY-NNN"; severity = ...; ... }
#   2. v26.2.1+ helper call:     mk_result ~id:"FAMILY-NNN" ~severity:...
#                                mk_result_with_fix ~id:"FAMILY-NNN" ...
ID_PATTERNS = [
    re.compile(r'\bid\s*=\s*"([A-Z][A-Z0-9]*-[0-9]+)"'),
    re.compile(r'~id\s*:\s*"([A-Z][A-Z0-9]*-[0-9]+)"'),
]

runtime_ids: set[str] = set()
files_scanned = 0
for p in sorted(SRC_DIR.glob("validators*.ml")):
    if "conflicted" in p.name:
        continue
    files_scanned += 1
    text = p.read_text(encoding="utf-8", errors="replace")
    for pat in ID_PATTERNS:
        for m in pat.finditer(text):
            runtime_ids.add(m.group(1))

if files_scanned == 0:
    print(
        f"[catalog] ERROR: glob '{SRC_DIR}/validators*.ml' matched no "
        f"files. Has the layout changed again?",
        file=sys.stderr,
    )
    sys.exit(2)

if len(runtime_ids) < MIN_RUNTIME_RULES:
    print(
        f"[catalog] ERROR: only found {len(runtime_ids)} runtime rule "
        f"IDs across {files_scanned} files (expected ≥ {MIN_RUNTIME_RULES}). "
        f"Either the regex no longer matches the rule-definition syntax, "
        f"or rules were mass-removed. Investigate before this gate is "
        f"trusted again.",
        file=sys.stderr,
    )
    sys.exit(2)

# Catalogue IDs from rules_v3.yaml.
catalog_ids: set[str] = set()
for line in CATALOG.read_text().splitlines():
    m = re.match(r'^\s*- id: "([^"]+)"', line)
    if m:
        catalog_ids.add(m.group(1))

orphans = sorted(runtime_ids - catalog_ids)
if orphans:
    for rid in orphans[:20]:
        print(
            f"[catalog] FAIL: runtime rule not in catalog: {rid}",
            file=sys.stderr,
        )
    if len(orphans) > 20:
        print(f"[catalog] FAIL: ... and {len(orphans) - 20} more", file=sys.stderr)
    print(
        f"[catalog] FAIL: {len(orphans)} runtime rule(s) missing from "
        f"specs/rules/rules_v3.yaml",
        file=sys.stderr,
    )
    sys.exit(4)

print(
    f"[catalog] PASS: catalogue compliance checks OK "
    f"({len(runtime_ids)} runtime rules across {files_scanned} sources, "
    f"all in catalogue of {len(catalog_ids)} entries)"
)
