#!/usr/bin/env python3
"""P2 diagnostics baseline (product track P2, "exactly why"): record and score.

Pre-registration (read it first; it defines every term used here):
docs/v27/product/P2-baseline-preregistration.md.

  record --sample {1,2} --corpus-root R --out F.json [--timeout S] [--cli EXE]
      For every document of the sample: verify its tree against the grade of
      record, run the CLI's `--compile-check` (the PREDICTION) and the pinned
      oracle under the recorded protocol (the GROUND TRUTH), and record the
      oracle's diagnostic record (_p2_diag.diag_record: the full first error,
      its l.N, the file stack, the verified location, the cause class) beside
      the CLI's parsed prediction (_p2_diag.cli_prediction). RUNS THE ORACLE:
      stage 2 only, after Track B's LANES_DONE and the owner's approval of the
      lines.
  score --records F1.json [F2.json] --prereg DOC --out S.json
      Joins the recorded rows and computes the pre-registered metrics. REFUSES
      unless the pre-registration's lines block says "status": "FIXED" (the
      owner fixed the lines) and its definitions version is this code's.

SEALED SAMPLE 3 (OPEN-119; owner ruling 2026-10-21). Both commands call
_sample_seal before they open the corpus, construct an oracle or read a
results artefact: sample 3, any frame window meeting ranks 721-920, any
sealed document id and any sample-3 artefact are refused (exit 3). There is no
flag, environment variable or option that disables this.

WHY A PRODUCER OF ITS OWN (not new fields in diff_real_roots.py's rows):
every recorded grade names the git blobs of its grading code (OPEN-126);
changing diff_real_roots.py or _oracle.py in behaviour makes every recorded
results*.json fail grading_code_drift. This producer imports them unchanged,
and its artefact names ITS grading code (the oracle core plus GRADERS).

Exit codes: 0 done; 2 infrastructure / refused precondition; 3 seal refusal.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import _p2_diag as diag  # noqa: E402
import _sample_seal as seal  # noqa: E402

REPO = HERE.parent.parent
GRADERS = ("scripts/tools/p2_baseline.py", "scripts/tools/_p2_diag.py",
           "scripts/tools/_sample_seal.py", "scripts/tools/diff_real_roots.py")
PREREG = Path("docs/v27/product/P2-baseline-preregistration.md")
LINES_BEGIN, LINES_END = "<!-- P2-LINES:BEGIN -->", "<!-- P2-LINES:END -->"
SF_DATALESS = 0x40000000  # macOS: the file's bytes are online-only (Dropbox)


def die(code: int, msg: str) -> int:
    print(f"[p2-baseline] {msg}", file=sys.stderr)
    return code


def dataless_files(d: Path) -> int:
    """Files of `d` whose bytes are not on disk. Checked BEFORE any read,
    because reading one triggers a download (or blocks) instead of failing."""
    n = 0
    for f in d.rglob("*"):
        try:
            if f.is_file() and getattr(os.lstat(f), "st_flags", 0) & SF_DATALESS:
                n += 1
        except OSError:
            n += 1
    return n


def read_lines_block(prereg: Path) -> dict:
    text = prereg.read_text()
    if text.count(LINES_BEGIN) != 1 or text.count(LINES_END) != 1:
        raise ValueError(f"{prereg} has no single {LINES_BEGIN} ... {LINES_END} block")
    body = text.split(LINES_BEGIN, 1)[1].split(LINES_END, 1)[0]
    body = body.strip().removeprefix("```json").removesuffix("```").strip()
    return json.loads(body)


def require_fixed(block: dict) -> None:
    if block.get("status") != "FIXED":
        raise PermissionError(
            f"the pre-registered lines are {block.get('status')!r}, not 'FIXED': nothing "
            f"is scored until the owner fixes them (pre-registration §7)")
    if block.get("definitions") != diag.DEFINITIONS_VERSION:
        raise PermissionError(
            f"the pre-registration fixes definitions {block.get('definitions')!r} but "
            f"this code implements {diag.DEFINITIONS_VERSION!r}")
    for ln in block.get("lines", []):
        if ln.get("value") is None:
            raise PermissionError(f"line {ln.get('id')} has no value")


def evaluate_lines(block: dict, scores: dict) -> list[dict]:
    """Each line: {"id","kind","metric","stat","op","value"}; `stat` is k, n,
    point (k/n), lower95 or upper95 of the metric (or an inputs/excluded
    count when metric starts with "inputs." / "excluded.")."""
    out = []
    for ln in block.get("lines", []):
        m = ln["metric"]
        if m.startswith(("inputs.", "excluded.")):
            sec, key = m.split(".", 1)
            v = scores[sec][key]
        else:
            r = scores[m]
            v = (r["k"] / r["n"] if r["n"] else None) if ln["stat"] == "point" else r[ln["stat"]]
        ops = {">=": lambda a, b: a >= b, "<=": lambda a, b: a <= b,
               "==": lambda a, b: a == b, "<": lambda a, b: a < b, ">": lambda a, b: a > b}
        held = None if v is None else ops[ln["op"]](v, ln["value"])
        out.append({**ln, "observed": v, "holds": held})
    return out


def record(ns) -> int:
    sealed = seal.sealed_ids(REPO)
    offset, n, res_name = seal.sample_spec(ns.sample)
    seal.refuse_window(offset, n)
    out = Path(ns.out)
    if seal._SAMPLE3_NAME.search(out.name):
        raise seal.SealError("the output's name says sample 3")
    graded = seal.refuse_artefact(REPO / "corpora/real_roots" / res_name, sealed, REPO)
    docs = graded["docs"]
    seal.refuse_ids([d["arxiv_id"] for d in docs], sealed)
    if len(docs) != n:
        return die(2, f"the grade of record holds {len(docs)} rows, not {n}")
    if not ns.corpus_root:
        return die(2, "no --corpus-root (LP_REAL_CORPUS)")
    root = Path(ns.corpus_root)
    cli = Path(ns.cli) if ns.cli else REPO / "_build/default/latex-parse/src/validators_cli.exe"
    if not cli.is_file():
        return die(2, f"{cli} not built")

    import _oracle  # noqa: E402  (imported only here: `score` needs no oracle)
    from diff_real_roots import row_compiles, run_to_fixpoint_full, sha256_tree  # noqa: E402
    oracle = _oracle.get_oracle()
    stamp = _oracle.RunStamp(GRADERS, REPO)
    rows = []
    for d in docs:
        row = {"arxiv_id": d["arxiv_id"], "toplevel": d["toplevel"], "graded": False,
               "excluded": None, "record_rc": d.get("pdflatex_rc"),
               "record_compiles": row_compiles(d)}
        pkg = root / d["arxiv_id"]
        if not pkg.is_dir():
            row["excluded"] = "missing from the corpus"
        elif dataless_files(pkg):
            row["excluded"] = "online-only (dataless) files in the tree"
        elif not d.get("sha256_tree"):
            row["excluded"] = "the grade of record carries no tree hash"
        elif sha256_tree(pkg) != d["sha256_tree"]:
            row["excluded"] = "tree differs from the grade of record"
        if row["excluded"]:
            rows.append(row)
            continue
        with oracle.tempdir() as td:
            work = Path(td) / "w"
            shutil.copytree(pkg, work)
            top = work / d["toplevel"]
            env = dict(os.environ, L0_VALIDATORS="pilot")
            try:
                r = subprocess.run([str(cli), "--compile-check", str(top)],
                                   capture_output=True, timeout=ns.timeout, env=env)
                row["cli_rc"] = r.returncode
                row["pred"] = diag.cli_prediction(r.stdout.decode("utf-8", "replace"),
                                                  r.stderr.decode("utf-8", "replace"))
            except subprocess.TimeoutExpired:
                row["cli_rc"], row["pred"] = -1, {"verdict": "TIMEOUT", "predictions": []}
            run = run_to_fixpoint_full(work, d["toplevel"], oracle.tex_env(td), ns.timeout)
            row.update(rc=run.rc, passes=run.passes, pdf=run.pdf,
                       compiles=run.rc == 0 and run.pdf)
            logp = _oracle.job_output(work, d["toplevel"], ".log")
            log = logp.read_bytes() if logp.is_file() else None
            row["log_sha256"] = hashlib.sha256(log).hexdigest() if log else None

            def read_source(rel, work=work):
                f = (work / rel).resolve()
                try:
                    f.relative_to(work.resolve())
                except ValueError:
                    return None
                return f.read_bytes() if f.is_file() else None

            row["gold"] = diag.diag_record(
                log, read_source=read_source,
                in_tree=lambda name, work=work: (work / name).is_file(),
                work_prefixes=(str(work), str(work.resolve())))
        row["graded"] = run.rc != -1 and row["cli_rc"] != -1
        row["agrees_with_record"] = (row["compiles"] == row["record_compiles"]
                                     and run.rc == d.get("pdflatex_rc"))
        rows.append(row)
    stamp.require()
    art = {"schema": diag.SCHEMA, "definitions": diag.DEFINITIONS_VERSION,
           "sample": int(ns.sample), "frame_window": {"offset": offset, "n": n},
           "grade_of_record": f"corpora/real_roots/{res_name}",
           "oracle": stamp.oracle_block(oracle), "measured_at_sha": stamp.head,
           "counts": {"rows": len(rows), "graded": sum(r["graded"] for r in rows),
                      "excluded": sum(1 for r in rows if r["excluded"])},
           "rows": rows}
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(art, indent=1, sort_keys=True) + "\n")
    print(f"[p2-baseline] recorded {art['counts']} -> {out}")
    return 0


def score(ns) -> int:
    sealed = seal.sealed_ids(REPO)
    block = read_lines_block(Path(ns.prereg))
    require_fixed(block)
    rows = []
    for f in ns.records:
        art = seal.refuse_artefact(Path(f), sealed, REPO)
        seal.sample_spec(art.get("sample"))
        if art.get("definitions") != diag.DEFINITIONS_VERSION:
            return die(2, f"{f} was recorded under {art.get('definitions')!r}")
        rows += [r for r in art["rows"] if not r.get("excluded")]
    if not rows:
        return die(2, "zero rows to score (an empty input is not a result)")
    scores = diag.score_rows(rows)
    scores["lines"] = evaluate_lines(block, scores)
    Path(ns.out).write_text(json.dumps(scores, indent=1, sort_keys=True) + "\n")
    print(f"[p2-baseline] scored {scores['inputs']} -> {ns.out}")
    return 0


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("record")
    r.add_argument("--sample", required=True)
    r.add_argument("--corpus-root", default=os.environ.get("LP_REAL_CORPUS"))
    r.add_argument("--out", required=True)
    r.add_argument("--timeout", type=int, default=600)
    r.add_argument("--cli", default=None)
    s = sub.add_parser("score")
    s.add_argument("--records", nargs="+", required=True)
    s.add_argument("--prereg", default=str(REPO / PREREG))
    s.add_argument("--out", required=True)
    ns = ap.parse_args(argv)
    try:
        return record(ns) if ns.cmd == "record" else score(ns)
    except seal.SealError as e:
        return die(3, f"REFUSED (sample-3 seal): {e}")
    except PermissionError as e:
        return die(2, f"REFUSED: {e}")


if __name__ == "__main__":
    sys.exit(main())
