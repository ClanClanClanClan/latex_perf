#!/usr/bin/env python3
"""P2 diagnostics baseline (product track P2, "exactly why"): record and score.

Pre-registration (read it first; it defines every term used here):
docs/v27/product/P2-baseline-preregistration.md.

  record --sample {1,2} --corpus-root R --out F.json [--timeout S] [--cli EXE]
      For every document of the sample: check its id, its toplevel and its
      tree, run the CLI's `--compile-check` (the PREDICTION) and the pinned
      oracle under the recorded protocol (the GROUND TRUTH), and record the
      oracle's diagnostic record beside the CLI's parsed prediction. RUNS THE
      ORACLE: stage 2 only, after Track B's LANES_DONE and the owner's
      approval of the lines.
  score --records SAMPLE1.json SAMPLE2.json --out S.json
      Computes the pre-registered metrics. The lines are read from the
      pre-registration COMMITTED AT HEAD at its canonical path -- there is no
      option naming another file -- and scoring REFUSES unless they say
      "status": "FIXED" with this code's definitions version.

FAIL CLOSED. Every input is read from its COMMITTED blob at HEAD, and the
working-tree file must equal it (_sample_seal.committed): the grades of
record, the seal manifest, the pre-registration and the two records. Their
blob ids are stamped into the output.

SEALED SAMPLE 3 (OPEN-119; samples 1-2 only is the assistant's default
pending owner ruling §8 #16). Both commands refuse
(exit 3), before they open the corpus, construct an oracle or read a record,
anything they cannot prove is sample 1 or 2 (_sample_seal: allow-list of
ids, strict id syntax, committed inputs). No flag, environment variable or
option disables this.

WHY A PRODUCER OF ITS OWN (not new fields in diff_real_roots.py's rows):
every recorded grade names the git blobs of its grading code (OPEN-126);
changing diff_real_roots.py or _oracle.py in behaviour makes every recorded
results*.json fail grading_code_drift. This producer imports them unchanged,
and its artefact names ITS grading code (the oracle core plus GRADERS).

Exit codes: 0 done; 2 infrastructure / refused precondition; 3 seal refusal;
4 the run is VOID (a validity line failed: no metric is presented as a result).
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import stat
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
PREREG = "docs/v27/product/P2-baseline-preregistration.md"
LINES_BEGIN, LINES_END = "<!-- P2-LINES:BEGIN -->", "<!-- P2-LINES:END -->"
SF_DATALESS = 0x40000000  # macOS: the file's bytes are online-only (Dropbox)
RUN_DIR = "/lp/run"       # _oracle.RUN_DIR: where the container sees the run
EXIT_VOID = 4


class InputError(Exception):
    """A precondition that is not the seal's."""


def die(code: int, msg: str) -> int:
    print(f"[p2-baseline] {msg}", file=sys.stderr)
    return code


# ── inputs ───────────────────────────────────────────────────────────────────

def parse_lines_block(text: str) -> dict:
    if text.count(LINES_BEGIN) != 1 or text.count(LINES_END) != 1:
        raise InputError(f"the pre-registration has no single {LINES_BEGIN} ... "
                         f"{LINES_END} block")
    body = text.split(LINES_BEGIN, 1)[1].split(LINES_END, 1)[0]
    body = body.strip().removeprefix("```json").removesuffix("```").strip()
    return json.loads(body)


def read_lines_block(path) -> dict:
    """The lines block of a pre-registration FILE (for the unit tests'
    reading of the committed document; the scorer uses committed_lines)."""
    return parse_lines_block(Path(path).read_text())


def committed_lines(repo: Path) -> tuple[dict, str]:
    data, blob = seal.committed(repo, PREREG)
    return parse_lines_block(data.decode("utf-8")), blob


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
    if not any(ln.get("kind") == "validity" for ln in block.get("lines", [])):
        raise PermissionError("the lines block has no validity line")


def _git_head(repo: Path) -> str:
    p = subprocess.run(["git", "--no-optional-locks", "rev-parse", "HEAD"], cwd=repo,
                       capture_output=True)
    if p.returncode != 0:
        raise InputError("cannot read HEAD")
    return p.stdout.decode().strip()


def repo_rel(repo: Path, path) -> str:
    p = Path(path)
    p = p if p.is_absolute() else Path.cwd() / p
    try:
        return str(p.resolve().relative_to(Path(repo).resolve()))
    except ValueError:
        raise InputError(f"{path} is not inside the repository (records are read "
                         f"from HEAD)") from None


# ── record ───────────────────────────────────────────────────────────────────

def safe_toplevel(pkg: Path, top) -> str | None:
    """Why `top` is not a file inside `pkg`, or None. Relative, no `..`, no
    NUL, and it RESOLVES inside the package (an absolute toplevel would make
    `work / top` discard `work`)."""
    if not isinstance(top, str) or not top or "\x00" in top:
        return "toplevel is not a non-empty string"
    if top.startswith("/") or top.startswith("\\") or (len(top) > 1 and top[1] == ":"):
        return "toplevel is absolute"
    if any(part == ".." for part in top.replace("\\", "/").split("/")):
        return "toplevel has a `..` component"
    try:
        r = (pkg / top).resolve()
        r.relative_to(pkg.resolve())
    except (ValueError, OSError):
        return "toplevel resolves outside the package"
    if not r.is_file():
        return "toplevel is not a file of the package"
    return None


def tree_problem(pkg: Path) -> str | None:
    """Why the package tree cannot be graded faithfully, or None. Walks with
    lstat only, BEFORE any read: a symlink anywhere (copytree follows it, and
    diff_real_roots.sha256_tree's rglob does not see through a symlinked
    directory, C-182), an online-only (dataless) file, or a special file."""
    for root, dirs, files in os.walk(pkg, followlinks=False):
        for n in dirs + files:
            q = os.path.join(root, n)
            try:
                st = os.lstat(q)
            except OSError:
                return "unreadable entry in the package tree"
            if stat.S_ISLNK(st.st_mode):
                return "symlink in the package tree"
            if getattr(st, "st_flags", 0) & SF_DATALESS:
                return "online-only (dataless) files in the tree"
            if not (stat.S_ISDIR(st.st_mode) or stat.S_ISREG(st.st_mode)):
                return "special file in the package tree"
    return None


def cli_provenance(cli: Path) -> dict:
    """The CLI that made the predictions (pre-registration §4.1): its binary
    hash and the checkout it was built in, whose latex-parse/src must be
    clean (a dirty tree names no commit)."""
    cli = Path(cli).resolve()
    if not cli.is_file():
        raise InputError(f"{cli} not built")
    top = subprocess.run(["git", "-C", str(cli.parent), "rev-parse", "--show-toplevel"],
                         capture_output=True)
    if top.returncode != 0:
        raise InputError("the CLI is not inside a git checkout; its source cannot be named")
    root = Path(top.stdout.decode().strip())

    def g(*a):
        return subprocess.run(["git", "--no-optional-locks", *a], cwd=root, capture_output=True)
    if g("diff", "--quiet", "HEAD", "--", "latex-parse/src").returncode != 0 or \
            g("ls-files", "--others", "--exclude-standard", "--", "latex-parse/src").stdout.strip():
        raise InputError("the CLI's checkout has uncommitted latex-parse/src changes")
    return {"path": str(cli), "sha256": hashlib.sha256(cli.read_bytes()).hexdigest(),
            "checkout": str(root), "head": g("rev-parse", "HEAD").stdout.decode().strip(),
            "src_tree": g("rev-parse", "HEAD:latex-parse/src").stdout.decode().strip()}


def run_cli(argv, cwd, timeout, env):
    """The CLI run (a seam for the unit tests' fake)."""
    return subprocess.run(argv, cwd=cwd, capture_output=True, timeout=timeout, env=env)


def record(ns, repo: Path) -> int:
    sealed = seal.sealed_ids(repo)
    seal_blob = seal.seal_blob(repo)
    offset, n, _ = seal.sample_spec(ns.sample)
    k = int(ns.sample)
    seal.refuse_name(ns.out)
    docs, gor_rel, gor_blob = seal.sample_docs(repo, k, sealed)
    if not ns.corpus_root:
        raise InputError("no --corpus-root (LP_REAL_CORPUS)")
    root = Path(ns.corpus_root)
    cli = Path(ns.cli) if ns.cli else repo / "_build/default/latex-parse/src/validators_cli.exe"
    cli_prov = cli_provenance(cli)

    import _oracle  # noqa: E402  (imported only here: `score` needs no oracle)
    from diff_real_roots import row_compiles, run_to_fixpoint_full, sha256_tree  # noqa: E402
    oracle = _oracle.get_oracle()
    stamp = _oracle.RunStamp(GRADERS, repo)
    rows = []
    for d in docs:
        row = {"arxiv_id": d["arxiv_id"], "toplevel": d.get("toplevel"), "graded": False,
               "excluded": None, "record_rc": d.get("pdflatex_rc"),
               "record_cli_rc": d.get("cli_rc"), "record_compiles": row_compiles(d)}
        pkg = root / seal.valid_id(d["arxiv_id"])
        if not pkg.is_dir() or pkg.is_symlink():
            row["excluded"] = "missing from the corpus"
        else:
            row["excluded"] = (tree_problem(pkg) or safe_toplevel(pkg, d.get("toplevel"))
                               or (None if d.get("sha256_tree") else
                                   "the grade of record carries no tree hash")
                               or (None if sha256_tree(pkg) == d["sha256_tree"] else
                                   "tree differs from the grade of record"))
        if row["excluded"]:
            rows.append(row)
            continue
        with oracle.tempdir() as td:
            work = Path(td) / "w"
            shutil.copytree(pkg, work, symlinks=True)
            roots = (str(work), str(work.resolve()))
            env = dict(os.environ, L0_VALIDATORS="pilot")
            try:
                r = run_cli([cli_prov["path"], "--compile-check", d["toplevel"]],
                            work, ns.timeout, env)
                row["cli_rc"] = r.returncode
                row["pred"] = diag.cli_prediction(r.stdout.decode("utf-8", "replace"),
                                                  r.stderr.decode("utf-8", "replace"), roots)
            except subprocess.TimeoutExpired:
                row["cli_rc"], row["pred"] = -1, {"verdict": "TIMEOUT", "predictions": []}
            run = run_to_fixpoint_full(work, d["toplevel"], oracle.tex_env(td), ns.timeout)
            row.update(rc=run.rc, passes=run.passes, pdf=run.pdf,
                       compiles=run.rc == 0 and run.pdf)
            logp = _oracle.job_output(work, d["toplevel"], ".log")
            log = logp.read_bytes() if logp.is_file() else None
            row["log_sha256"] = hashlib.sha256(log).hexdigest() if log else None

            def read_source(rel, work=work):
                c = diag.canon_path(rel)
                if c is None:
                    return None
                f = (work / c).resolve()
                try:
                    f.relative_to(work.resolve())
                except ValueError:
                    return None
                return f.read_bytes() if f.is_file() else None

            def in_tree(name, work=work):
                c = diag.canon_path(name, roots + (RUN_DIR,))
                return c is not None and (work / c).is_file()

            row["gold"] = diag.diag_record(log, read_source=read_source, in_tree=in_tree,
                                           work_prefixes=(RUN_DIR,) + roots)
        row["graded"] = run.rc != -1 and row["cli_rc"] != -1
        row["agrees_with_record"] = (row["compiles"] == row["record_compiles"]
                                     and run.rc == d.get("pdflatex_rc"))
        rows.append(row)
    stamp.require()
    if seal.sample_docs(repo, k, sealed)[2] != gor_blob or seal.seal_blob(repo) != seal_blob:
        raise InputError("the grade of record or the seal changed during the run")
    art = {"schema": diag.SCHEMA, "definitions": diag.DEFINITIONS_VERSION,
           "sample": k, "frame_window": {"offset": offset, "n": n},
           "grade_of_record": {"path": gor_rel, "blob": gor_blob}, "seal_blob": seal_blob,
           "cli": cli_prov, "oracle": stamp.oracle_block(oracle), "measured_at_sha": stamp.head,
           "counts": {"rows": len(rows), "graded": sum(r["graded"] for r in rows),
                      "excluded": sum(1 for r in rows if r["excluded"])},
           "rows": rows}
    out = Path(ns.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(art, indent=1, sort_keys=True) + "\n")
    print(f"[p2-baseline] recorded {art['counts']} -> {out}")
    return 0


# ── score ────────────────────────────────────────────────────────────────────

def load_record(repo: Path, path, sealed: frozenset) -> tuple[dict, dict]:
    """A record, validated against its sample by CONTENT, never by its own
    labels alone. Returns (artefact, provenance)."""
    seal.refuse_name(path)
    rel = repo_rel(repo, path)
    data, blob = seal.committed(repo, rel)
    art = json.loads(data)
    if not isinstance(art, dict) or art.get("schema") != diag.SCHEMA \
            or art.get("definitions") != diag.DEFINITIONS_VERSION:
        raise InputError(f"{rel} is not a {diag.SCHEMA} record of {diag.DEFINITIONS_VERSION}")
    k = art.get("sample")
    if type(k) is not int:
        raise seal.SealError(f"{rel}: its sample is not the integer 1 or 2")
    offset, n, _ = seal.sample_spec(k)
    if art.get("frame_window") != {"offset": offset, "n": n}:
        raise seal.SealError(f"{rel}: its frame window is not sample {k}'s")
    docs, gor_rel, gor_blob = seal.sample_docs(repo, k, sealed)
    if art.get("grade_of_record") != {"path": gor_rel, "blob": gor_blob}:
        raise InputError(f"{rel} was recorded against another grade of record")
    if art.get("seal_blob") != seal.seal_blob(repo):
        raise InputError(f"{rel} was recorded under another seal")
    rows = art.get("rows")
    if not isinstance(rows, list) or len(rows) != n or any(not isinstance(r, dict) for r in rows):
        raise InputError(f"{rel} must hold exactly {n} row objects")
    seal.refuse_ids([r.get("arxiv_id") for r in rows], sealed)
    keys = [seal.paper_key(r["arxiv_id"]) for r in rows]
    if len(set(keys)) != n or set(keys) != {seal.paper_key(d["arxiv_id"]) for d in docs}:
        raise InputError(f"{rel}: its rows are not exactly sample {k}'s documents, once each")
    return art, {"path": rel, "blob": blob, "sha256": hashlib.sha256(data).hexdigest(),
                 "sample": k}


def evaluate_lines(block: dict, scores: dict) -> list[dict]:
    """Each line: {"id","kind","metric","stat","op","value"[, "min_n"]}.
    `stat` is k, n, point (k/n), lower95 or upper95 of the metric, or the
    count itself for an "inputs." / "excluded." metric. A line whose metric
    has n < min_n (or no observation) is NOT EVALUABLE: holds = None. A
    success line that is not evaluable is not met; a kill line that is not
    evaluable does not fire (pre-registration §7)."""
    ops = {">=": lambda a, b: a >= b, "<=": lambda a, b: a <= b,
           "==": lambda a, b: a == b, "<": lambda a, b: a < b, ">": lambda a, b: a > b}
    out = []
    for ln in block.get("lines", []):
        m = ln["metric"]
        if m.startswith(("inputs.", "excluded.")):
            sec, key = m.split(".", 1)
            v, nn = scores[sec][key], None
        else:
            r = scores[m]
            nn = r["n"]
            v = (r["k"] / r["n"] if r["n"] else None) if ln["stat"] == "point" else r[ln["stat"]]
        if v is None or (ln.get("min_n") is not None and (nn or 0) < ln["min_n"]):
            out.append({**ln, "observed": v, "holds": None, "status": "not-evaluable"})
            continue
        held = ops[ln["op"]](v, ln["value"])
        out.append({**ln, "observed": v, "holds": held,
                    "status": "holds" if held else "fails"})
    return out


def score_artefacts(arts: list[dict], block: dict) -> tuple[dict, bool]:
    """(output, void) from validated records."""
    by_reason: dict = {}
    graded = []
    for art in arts:
        for r in art["rows"]:
            if r.get("excluded"):
                by_reason[r["excluded"]] = by_reason.get(r["excluded"], 0) + 1
            else:
                graded.append(r)
    scores = diag.score_rows(graded)
    scores["inputs"]["rows_recorded"] = sum(len(a["rows"]) for a in arts)
    scores["excluded"]["at_record"] = sum(by_reason.values())
    scores["excluded_at_record_by_reason"] = dict(sorted(by_reason.items()))
    lines = evaluate_lines(block, scores)
    void = any(ln["kind"] == "validity" and ln["holds"] is not True for ln in lines)
    if void:
        out = {"void": True, "definitions": diag.DEFINITIONS_VERSION,
               "why": [f"{ln['id']} {ln['status']}" for ln in lines
                       if ln["kind"] == "validity" and ln["holds"] is not True],
               "inputs": scores["inputs"], "excluded": scores["excluded"],
               "excluded_at_record_by_reason": scores["excluded_at_record_by_reason"],
               "location_unverified_by_reason": scores["location_unverified_by_reason"],
               "validity": [ln for ln in lines if ln["kind"] == "validity"]}
        return out, True
    scores["void"] = False
    scores["lines"] = lines
    return scores, False


def score(ns, repo: Path) -> int:
    sealed = seal.sealed_ids(repo)
    block, prereg_blob = committed_lines(repo)
    require_fixed(block)
    if len(ns.records) != 2:
        raise InputError("score takes exactly two records: sample 1's and sample 2's")
    seal.refuse_name(ns.out)
    loaded = [load_record(repo, f, sealed) for f in ns.records]
    if sorted(p["sample"] for _, p in loaded) != [1, 2]:
        raise InputError("the two records must be sample 1 and sample 2, once each")
    out, void = score_artefacts([a for a, _ in loaded], block)
    out["provenance"] = {"head": _git_head(repo), "prereg": {"path": PREREG, "blob": prereg_blob},
                         "seal_blob": seal.seal_blob(repo), "records": [p for _, p in loaded]}
    Path(ns.out).write_text(json.dumps(out, indent=1, sort_keys=True) + "\n")
    if void:
        print(f"[p2-baseline] VOID ({'; '.join(out['why'])}): no metric is a result -> {ns.out}",
              file=sys.stderr)
        return EXIT_VOID
    print(f"[p2-baseline] scored {out['inputs']} -> {ns.out}")
    return 0


def build_parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0], allow_abbrev=False)
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("record", allow_abbrev=False)
    r.add_argument("--sample", required=True)
    r.add_argument("--corpus-root", default=os.environ.get("LP_REAL_CORPUS"))
    r.add_argument("--out", required=True)
    r.add_argument("--timeout", type=int, default=600)
    r.add_argument("--cli", default=None)
    s = sub.add_parser("score", allow_abbrev=False)
    s.add_argument("--records", nargs="+", required=True)
    s.add_argument("--out", required=True)
    return ap


def main(argv=None) -> int:
    ns = build_parser().parse_args(argv)
    repo = REPO
    try:
        return record(ns, repo) if ns.cmd == "record" else score(ns, repo)
    except seal.SealError as e:
        return die(3, f"REFUSED (sample-3 seal): {e}")
    except (PermissionError, InputError) as e:
        return die(2, f"REFUSED: {e}")


if __name__ == "__main__":
    sys.exit(main())
