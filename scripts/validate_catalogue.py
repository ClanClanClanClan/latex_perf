#!/usr/bin/env python3
import json
import re
import sys
from pathlib import Path

RUNTIME = Path("latex-parse/src/validators.ml")
CATALOG = Path("specs/rules/rules_v3.yaml")
PILOT = Path("specs/rules/pilot_v1.yaml")

for path in (RUNTIME, CATALOG, PILOT):
    if not path.is_file():
        print(f"[catalog] ERROR: Missing required file: {path}", file=sys.stderr)
        sys.exit(2)

runtime_rules: dict[str, dict[str, str]] = {}
current_rule = None

for line in RUNTIME.read_text().splitlines():
    m_rule = re.match(r"let\s+([A-Za-z0-9_]+)\s*:\s*rule\s*=\s*", line)
    if m_rule:
        current_rule = m_rule.group(1)
        continue
    if current_rule is not None:
        m_id = re.search(r"id\s*=\s*\"([A-Z0-9-]+)\"", line)
        m_sev = re.search(r"severity\s*=\s*(Error|Warning|Info)", line)
        if m_id:
            rid = m_id.group(1)
        if m_sev and 'rid' in locals():
            runtime_rules[rid] = {
                'severity': m_sev.group(1).lower(),
                'rule': current_rule,
                'precondition': '',
            }
            del rid
    if line.strip() == "":
        current_rule = None

section_layers = {
    'rules_basic': 'L0_Lexer',
    'rules_pilot': 'L0_Lexer',
    'rules_l1': 'L1_Expanded',
}

current_section = None
for line in RUNTIME.read_text().splitlines():
    stripped = line.strip()
    m_sec = re.match(r"let\s+(rules_[A-Za-z0-9_]+)\s*:\s*rule list", stripped)
    if m_sec:
        current_section = m_sec.group(1)
        continue
    if current_section and stripped.startswith(']'):
        current_section = None
        continue
    if current_section:
        for name in re.findall(r"([A-Za-z0-9_]+)_rule", stripped):
            rule_name = name + '_rule'
            layer = section_layers.get(current_section, '')
            for info in runtime_rules.values():
                if info['rule'] == rule_name:
                    info['precondition'] = layer

catalog_ids = set()
for line in CATALOG.read_text().splitlines():
    m = re.match(r"^\s*- id: \"([^\"]+)\"", line)
    if m:
        catalog_ids.add(m.group(1))

pilot_data: dict[str, tuple[str, str]] = {}
current_id = None
current_pre = ''
for line in PILOT.read_text().splitlines():
    m_id = re.match(r"^\s*- id: \"([^\"]+)\"", line)
    if m_id:
        current_id = m_id.group(1)
        current_pre = ''
        continue
    if current_id:
        line_stripped = line.strip()
        m_pre = re.match(r"precondition:\s*([A-Za-z_0-9]+)", line_stripped)
        if m_pre:
            current_pre = m_pre.group(1)
            continue
        m_sev = re.match(r"default_severity:\s*([A-Za-z]+)", line_stripped)
        if m_sev:
            pilot_data[current_id] = (m_sev.group(1).lower(), current_pre)
            current_id = None
            current_pre = ''

fail = 0

for rid, info in runtime_rules.items():
    layer = info['precondition']
    if layer != 'L0_Lexer':
        continue
    if rid not in catalog_ids:
        print(f"[catalog] FAIL: runtime rule not in catalog: {rid}", file=sys.stderr)
        fail = 1

if fail:
    print("[catalog] FAIL: catalogue compliance checks failed", file=sys.stderr)
    sys.exit(4)

print("[catalog] PASS: catalogue compliance checks OK")
