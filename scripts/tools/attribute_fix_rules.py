#!/usr/bin/env python3
"""Per-RULE reach and break attribution for the CONVERGED default fixer.

    python3 scripts/tools/attribute_fix_rules.py --offset 400 --n 40 --out shard.json

WHY. OPEN-109: no REGION guard moves the out-of-sample break rate; the breaks
are a long tail of per-rule defects. Both remaining options -- withdraw the
auto-fix of rules that break papers, or allow-list rules that do not -- need one
table: per rule, how many papers the converged fixer actually EDITS with it
(reach, the value side) and in how many papers it is part of the REPAIR SET
(the risk side), on papers never used for fixer work.

MECHANISM. Uses the CLI's env-gated measurement hooks (validators_cli.ml):
  LP_FIX_TRACE=<file>   one line per APPLIED edit per pass, tagged with its rule
  LP_FIX_ONLY=A,B       converge using only these rules
  LP_FIX_EXCLUDE=A,B    converge using every rule except these
so every arm runs the engine's OWN fixpoint loop (no Python approximation).

PER PAPER
  1. CTRL: pristine compiles (rc 0), else excluded.
  2. FULL: default fixer with LP_FIX_TRACE -> cell preserved/broken, and the
     set of rules that applied >= 1 edit (reach).
  3. If broken, the REPAIR SET, greedily:
       excluded = {}
       repeat: arm EXCLUDE=excluded compiles? -> done.
               else among the rules that applied edits in that arm, halve with
               ONLY=half until ONE rule alone breaks the paper; add it to
               excluded. If neither half breaks alone -> INTERACTION, stop.
     Each culprit is thereby SUFFICIENT alone (it broke the pristine paper by
     itself), and the final EXCLUDE arm compiling makes the set jointly
     NECESSARY. Individual necessity is tested too (EXCLUDE={r} alone).
A fixer crash or timeout raises: the paper becomes a harness error, which
fails the run, and is never graded with an unfixed file.
"""
from __future__ import annotations

import sys
sys.dont_write_bytecode = True

import argparse, hashlib, json, os, pathlib, shutil, subprocess, tempfile

REPO = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / "scripts/tools"))
from diff_real_roots import PIN, build_frame, run_to_fixpoint  # noqa: E402
import _measurement_provenance as _mp  # noqa: E402
from gen_apply_fixes_real_differential import first_error  # noqa: E402

CLI = REPO / "_build/default/latex-parse/src/validators_cli.exe"
MAX_CULPRITS = 6


def tex_env(td):
    return dict(os.environ, TEXMFHOME=str(pathlib.Path(td) / "th"),
                TEXMFVAR=str(pathlib.Path(td) / "tv"),
                openin_any="p", openout_any="p", SOURCE_DATE_EPOCH="0")


class Arm:
    """One fresh copy -> optional fixer (with hooks) -> compile."""

    def __init__(self, pkg, top, timeout):
        self.pkg, self.top, self.timeout = pkg, top, timeout

    def run(self, fix_env=None, fix=True):
        """fix_env: extra env for the fixer (LP_FIX_ONLY/EXCLUDE). Returns
        (rc, first_error, applied_rules_count_dict, changed_files)."""
        with tempfile.TemporaryDirectory(dir="/private/tmp") as td:
            work = pathlib.Path(td) / "w"
            shutil.copytree(self.pkg, work)
            trace = pathlib.Path(td) / "trace.tsv"
            changed = []
            if fix:
                # main() refuses a caller env carrying LP_FIX_*, so only
                # fix_env's own restriction can reach the fixer.
                env = dict(os.environ, LP_FIX_TRACE=str(trace), **(fix_env or {}))
                for tex in sorted(work.rglob("*.tex")):
                    before = tex.read_bytes()
                    try:
                        # --apply-fixes-all: this instrument measures the FULL fixer (every rule's
                        # fix), which is what the unqualified --apply-fixes meant before the
                        # OPEN-105 allow-list made it apply only Fix_policy.default_allowlist.
                        # LP_FIX_ONLY replaces the all-rules base and
                        # LP_FIX_EXCLUDE subtracts from it, as before.
                        r = subprocess.run([str(CLI), "--apply-fixes-all", str(tex)],
                                           capture_output=True, env=env,
                                           timeout=self.timeout)
                    except subprocess.TimeoutExpired:
                        # An unfixed file would be graded as if fixed: the
                        # silent class this harness exists to avoid.
                        raise RuntimeError(f"fixer timed out on {tex} ({fix_env})")
                    if r.returncode not in (0, 1):
                        raise RuntimeError(
                            f"fixer crashed (exit {r.returncode}) on {tex}: "
                            f"{r.stderr[-300:]!r}")
                    if r.stdout and r.stdout != before:
                        tex.write_bytes(r.stdout)
                        changed.append(str(tex.relative_to(work)))
            applied = {}
            if trace.is_file():
                for line in trace.read_text(errors="replace").splitlines():
                    parts = line.split("\t")
                    if len(parts) >= 2:
                        applied[parts[1]] = applied.get(parts[1], 0) + 1
            rc, _ = run_to_fixpoint(work, self.top, tex_env(td), self.timeout)
            return rc, first_error(work, self.top), applied, changed


def find_culprit(arm, candidates, excluded, log):
    """Halve `candidates` with ONLY=half until one rule alone breaks the paper.
    Returns (rule, error) or (None, reason)."""
    pool = sorted(candidates)
    while len(pool) > 1:
        mid = len(pool) // 2
        a, b = pool[:mid], pool[mid:]
        rc_a, e_a, _, _ = arm.run({"LP_FIX_ONLY": ",".join(a)})
        log.append({"only": a, "rc": rc_a, "err": e_a})
        if rc_a not in (0,):
            pool = a
            continue
        rc_b, e_b, _, _ = arm.run({"LP_FIX_ONLY": ",".join(b)})
        log.append({"only": b, "rc": rc_b, "err": e_b})
        if rc_b not in (0,):
            pool = b
            continue
        return None, "INTERACTION: neither half breaks alone"
    rc, e, _, _ = arm.run({"LP_FIX_ONLY": pool[0]})
    log.append({"only": pool, "rc": rc, "err": e})
    if rc == 0:
        return None, f"single candidate {pool[0]} does not break alone"
    return pool[0], e


def attribute(arm, full_applied):
    excluded, culprits, log = [], [], []
    note = ""
    applied = full_applied
    for _ in range(MAX_CULPRITS):
        cand = [r for r in applied if r not in excluded]
        if not cand:
            note = "no applied rules left but paper still broken"
            break
        rule, info = find_culprit(arm, cand, excluded, log)
        if rule is None:
            note = info
            break
        culprits.append({"rule": rule, "first_error_alone": info})
        excluded.append(rule)
        rc, e, applied, _ = arm.run({"LP_FIX_EXCLUDE": ",".join(excluded)})
        log.append({"exclude": list(excluded), "rc": rc, "err": e})
        if rc == 0:
            note = "REPAIRED by excluding the repair set"
            break
    else:
        note = f"cap of {MAX_CULPRITS} culprits reached, still broken"
    repaired = note.startswith("REPAIRED")
    # individual necessity: does excluding ONLY this rule repair the paper?
    for c in culprits:
        rc, e, _, _ = arm.run({"LP_FIX_EXCLUDE": c["rule"]})
        c["exclude_alone_repairs"] = (rc == 0)
    return {"repair_set": excluded if repaired else None, "culprits": culprits,
            "note": note, "probes": log}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--offset", type=int, required=True)
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--only-ids", default="", help="comma list (validation)")
    ap.add_argument("--timeout", type=int, default=180)
    ns = ap.parse_args()

    root = pathlib.Path(os.environ["LP_REAL_CORPUS"]).resolve()
    banner = subprocess.run(["pdflatex", "--version"], capture_output=True,
                            text=True).stdout.split("\n")[0]
    if PIN not in banner:
        sys.exit(f"FATAL: engine skew {banner!r}")
    for k in ("LP_FIX_ONLY", "LP_FIX_EXCLUDE", "LP_FIX_TRACE"):
        if os.environ.get(k):
            sys.exit(f"FATAL: {k} set in the caller's environment")
    frame = build_frame(root)
    ordered = sorted(frame, key=lambda r: hashlib.sha256(
        r["arxiv_id"].encode()).hexdigest())
    if ns.only_ids:
        want = set(ns.only_ids.split(","))
        window = [r for r in ordered if r["arxiv_id"] in want]
        assert len(window) == len(want), "unknown id"
    else:
        window = ordered[ns.offset:ns.offset + ns.n]
        if len(window) < ns.n:
            sys.exit("FATAL: window overruns frame")

    prov = {"frame_size": len(frame), "selection": "sha256(arxiv_id) ascending",
            "offset": ns.offset, "n": ns.n, "only_ids": ns.only_ids or None,
            "engine": banner,
            "cli_sha256": hashlib.sha256(CLI.read_bytes()).hexdigest(),
            "cli_platform": _mp.cli_platform(),
            "cli_build_root": _mp.cli_build_root(CLI),  # C-72
            "src_tree_sha": subprocess.run(
                ["git", "--no-optional-locks", "rev-parse", "HEAD:latex-parse/src"],
                cwd=REPO, capture_output=True, text=True).stdout.strip()}
    rows, errors = [], []
    outp = pathlib.Path(ns.out)

    def dump(complete):
        outp.write_text(json.dumps({"provenance": prov, "complete": complete,
                                    "harness_errors": errors, "rows": rows},
                                   indent=1, ensure_ascii=False) + "\n")

    for i, rec in enumerate(window, 1):
        aid = rec["arxiv_id"]
        row = {"rank": ordered.index(rec), "arxiv_id": aid,
               "toplevel": rec["toplevel"]}
        try:
            arm = Arm(root / aid, rec["toplevel"], ns.timeout)
            rc0, e0, _, _ = arm.run(fix=False)
            row["rc_before"] = rc0
            if rc0 != 0:
                row["cell"], row["first_error_before"] = "excluded-did-not-compile", e0
            else:
                rc1, e1, applied, changed = arm.run()
                row.update(rc_after=rc1, first_error_after=e1,
                           applied_rules=applied, changed_files=changed,
                           cell="broken" if rc1 != 0 else "preserved")
                if rc1 != 0:
                    row["attribution"] = attribute(arm, applied)
        except Exception as ex:  # recorded AND fails the run
            errors.append({"arxiv_id": aid, "error": repr(ex)})
            row["cell"] = "harness-error"
        rows.append(row)
        a = row.get("attribution", {})
        print(f"[{i}/{len(window)}] {aid:<16} {row['cell']} "
              f"{a.get('repair_set', '')} {a.get('note', '')}", flush=True)
        dump(False)
    dump(True)
    print("SENTINEL_DONE", flush=True)
    return 2 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
