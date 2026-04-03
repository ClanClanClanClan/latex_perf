#!/usr/bin/env python3
"""Parse governance/risk-register.md and check residual risk scores.

CI gate: exits 1 if any Residual score >= 4 (threshold for red badge).
Usage: python3 scripts/risk_heatmap.py [--threshold 4]
"""
import re
import sys
from pathlib import Path

REGISTER_PATH = Path(__file__).parent.parent / "governance" / "risk-register.md"
DEFAULT_THRESHOLD = 4


def parse_register(path: Path) -> list[dict]:
    """Parse markdown table rows from risk register."""
    rows = []
    in_table = False
    with open(path) as f:
        for line in f:
            line = line.strip()
            if line.startswith("|") and "---" not in line:
                cells = [c.strip() for c in line.split("|")[1:-1]]
                if len(cells) >= 8:
                    # Header row detection
                    if cells[0] in ("#", "ID"):
                        in_table = True
                        continue
                    if in_table:
                        try:
                            rows.append({
                                "id": cells[0],
                                "area": cells[1],
                                "risk": cells[2],
                                "p": int(cells[3]) if cells[3].isdigit() else 0,
                                "i": int(cells[4]) if cells[4].isdigit() else 0,
                                "score": int(cells[5]) if cells[5].isdigit() else 0,
                                "residual": int(cells[6]) if cells[6].isdigit() else 0,
                                "critical": cells[7].strip().upper() == "Y",
                            })
                        except (IndexError, ValueError):
                            continue
    return rows


def main():
    threshold = DEFAULT_THRESHOLD
    if "--threshold" in sys.argv:
        idx = sys.argv.index("--threshold")
        threshold = int(sys.argv[idx + 1])

    if not REGISTER_PATH.exists():
        print(f"ERROR: {REGISTER_PATH} not found", file=sys.stderr)
        sys.exit(2)

    rows = parse_register(REGISTER_PATH)
    if not rows:
        print("ERROR: no risk rows parsed", file=sys.stderr)
        sys.exit(2)

    max_residual = max(r["residual"] for r in rows)
    critical_count = sum(1 for r in rows if r["critical"])
    high_residual = [r for r in rows if r["residual"] >= threshold]

    print(f"Risk Register: {len(rows)} risks parsed")
    print(f"  Max residual: {max_residual}")
    print(f"  Critical flags: {critical_count}")
    print(f"  Residual >= {threshold}: {len(high_residual)}")

    if high_residual:
        print(f"\nFAIL: {len(high_residual)} risk(s) exceed threshold {threshold}:")
        for r in high_residual:
            print(f"  {r['id']} ({r['area']}): {r['risk'][:60]}... Residual={r['residual']}")
        sys.exit(1)
    else:
        print(f"\nPASS: all residuals below {threshold}")
        sys.exit(0)


if __name__ == "__main__":
    main()
