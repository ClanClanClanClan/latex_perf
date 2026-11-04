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
4 the run is VOID (a validity line failed: no metric is presented as a result);
5 SOUNDNESS DEFECT (a wrong certified claim, ruling R4: the certified channel
stops and the class is fixed; it is not a statistical kill, and it is
reported even when the run is also void).
"""
from __future__ import annotations

import argparse
import base64
import hashlib
import json
import os
import re
import shutil
import stat
import subprocess
import sys
import zlib
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
EXIT_SOUNDNESS = 5   # a wrong CERTIFIED claim (R4): takes precedence over VOID


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
    try:
        return json.loads(body)
    except ValueError:
        raise InputError("the lines block is not JSON") from None


def read_lines_block(path) -> dict:
    """The lines block of a pre-registration FILE (for the unit tests'
    reading of the committed document; the scorer uses committed_lines)."""
    return parse_lines_block(Path(path).read_text())


LABEL_DIR = "corpora/p2_baseline/cause_labels"
LABEL_FILES = {"A": f"{LABEL_DIR}/labeller_a.json", "B": f"{LABEL_DIR}/labeller_b.json",
               "adj": f"{LABEL_DIR}/adjudication.json"}


def _git_ok(repo, *a) -> subprocess.CompletedProcess:
    return subprocess.run(["git", "--no-optional-locks", *a], cwd=repo, capture_output=True)


def _tracked(repo, rel) -> bool:
    return _git_ok(repo, "rev-parse", f"HEAD:{rel}").returncode == 0


def _commits_touching(repo, rel) -> list[tuple[str, str, str]]:
    """(sha, author email, author name) of every commit touching rel, newest first."""
    out = _git_ok(repo, "log", "--format=%H%x09%ae%x09%an", "--", rel).stdout.decode()
    return [tuple(l.split("\t")) for l in out.splitlines() if l.strip()]


LABELLERS = f"{LABEL_DIR}/labellers.json"
LABELLERS_SCHEMA = "p2-labellers/1"


def _ssh_fingerprint(key: str) -> str:
    """SHA256:... of an SSH public key line (ssh-keygen -lf)."""
    import tempfile
    with tempfile.NamedTemporaryFile("w", suffix=".pub", delete=False) as f:
        f.write(key.strip() + "\n")
    try:
        r = subprocess.run(["ssh-keygen", "-lf", f.name], capture_output=True, text=True)
    finally:
        os.unlink(f.name)
    parts = r.stdout.split()
    if r.returncode != 0 or len(parts) < 2 or not parts[1].startswith("SHA256:"):
        raise InputError("a labeller key in the allow-list is not an SSH public key")
    return parts[1]


def check_label_signatures(repo: Path, present: dict, docs: dict) -> None:
    """WHAT THE TOOL CAN PROVE ABOUT WHO LABELLED (review 3, H2). Git
    authorship is self-asserted, so it proves nothing on its own. The tool
    therefore requires:
      * a committed allow-list of the three people (LABELLERS: role -> name,
        e-mail, SSH public key); their names, e-mails and keys pairwise
        DISJOINT; each label file's declared identity equal to its role's;
      * EVERY commit touching a label file signed (SSH signing, gpg.format
        ssh) with a GOOD signature by exactly that role's listed key, with that
        role's author name and e-mail;
      * no commit touching more than one label file.
    The residual trust is stated in the pre-registration (§5.5): WHO the
    three keys belong to is an owner-designated fact outside the tool."""
    import tempfile
    try:
        allow = json.loads(seal.committed(repo, LABELLERS)[0])
    except seal.SealError as e:
        raise InputError(f"cause labels need the committed labeller allow-list: {e}") from None
    except ValueError:
        raise InputError(f"{LABELLERS} is not JSON") from None
    if not isinstance(allow, dict) or allow.get("schema") != LABELLERS_SCHEMA:
        raise InputError(f"{LABELLERS} is not a {LABELLERS_SCHEMA} file")
    roles = {}
    for k in present:
        e = allow.get(k)
        if not isinstance(e, dict) or not all(isinstance(e.get(x), str) and e[x].strip()
                                              for x in ("name", "email", "ssh_key")):
            raise InputError(f"{LABELLERS} has no complete entry for role {k}")
        roles[k] = dict(e, fingerprint=_ssh_fingerprint(e["ssh_key"]))
    for field in ("name", "email", "fingerprint"):
        vals = [diag.norm_identity(r[field]) for r in roles.values()]
        if len(set(vals)) != len(vals):
            raise InputError(f"the labellers' {field}s are not pairwise disjoint")
    for k in present:
        declared = docs[k].get("adjudicator" if k == "adj" else "labeller")
        if diag.norm_identity(declared) != diag.norm_identity(roles[k]["name"]):
            raise InputError(f"{present[k]} declares {declared!r}, not its role's listed name")
    label_rels = set(LABEL_FILES.values())
    with tempfile.NamedTemporaryFile("w", suffix=".allowed_signers", delete=False) as f:
        for r in roles.values():
            f.write(f"{r['email']} {r['ssh_key'].strip()}\n")
    try:
        for k, rel in present.items():
            for sha, _e, _n in _commits_touching(repo, rel):
                touched = set(_git_ok(repo, "show", "--name-only", "--format=", sha)
                              .stdout.decode().split()) & label_rels
                if len(touched) > 1:
                    raise InputError(f"commit {sha[:10]} touches {len(touched)} label files: "
                                     f"each label file must be committed on its own")
                info = _git_ok(repo, "-c", "gpg.format=ssh", "-c",
                               f"gpg.ssh.allowedSignersFile={f.name}", "log", "-1",
                               "--format=%G?%x09%GF%x09%an%x09%ae", sha).stdout.decode()
                parts = info.rstrip("\n").split("\t")
                if len(parts) != 4 or parts[0] != "G":
                    raise InputError(f"commit {sha[:10]} of {rel} is not signed with a good "
                                     f"signature by a listed labeller key")
                if parts[1] != roles[k]["fingerprint"]:
                    raise InputError(f"commit {sha[:10]} of {rel} is signed by another key "
                                     f"than role {k}'s")
                if (diag.norm_identity(parts[2]), diag.norm_identity(parts[3])) != \
                        (diag.norm_identity(roles[k]["name"]), diag.norm_identity(roles[k]["email"])):
                    raise InputError(f"commit {sha[:10]} of {rel} has another author than "
                                     f"role {k}'s listed name and e-mail")
    finally:
        os.unlink(f.name)


def committed_labels(repo: Path, record_rels: list[str]) -> tuple[dict, dict | None]:
    """The two-labeller cause-line gold (§5.5), or ({}, None) when no label
    file exists. FAIL CLOSED (review 2, H4, M4): the files are read from HEAD
    (a working-tree copy that differs is refused); every id in them is
    checked against the seals FIRST; each file must be committed ONLY by its
    declared labeller (author e-mail or name, after norm_identity); and every
    commit touching a label file must be a strict ancestor of the commit that
    introduced each record -- the labels predate the predictions they score
    (the blindness claim)."""
    present = {k: rel for k, rel in LABEL_FILES.items()
               if _tracked(repo, rel) or (Path(repo) / rel).exists()
               or (Path(repo) / rel).is_symlink()}
    if not present:
        return {}, None
    if "A" not in present or "B" not in present:
        raise InputError("cause labels need both labeller files (A and B)")
    docs, blobs = {}, {}
    for k, rel in present.items():
        data, blobs[rel] = seal.committed(repo, rel)
        try:
            docs[k] = json.loads(data)
        except ValueError:
            raise InputError(f"{rel} is not JSON") from None
    sealed = seal.sealed_ids(repo)
    try:
        gold, st = diag.cause_line_gold(docs["A"], docs["B"], docs.get("adj"),
                                        lambda ids: seal.refuse_ids(ids, sealed))
    except ValueError as e:
        raise InputError(f"cause labels: {e}") from None
    check_label_signatures(repo, present, docs)
    for rec in record_rels:
        intro = _commits_touching(repo, rec)
        if not intro:
            raise InputError(f"{rec} is not committed")
        first = intro[-1][0]
        for rel in present.values():
            for sha, _e, _n in _commits_touching(repo, rel):
                if sha == first or _git_ok(repo, "merge-base", "--is-ancestor", sha,
                                           first).returncode != 0:
                    raise InputError(f"{rel} was committed at or after the record {rec}: the "
                                     f"labels must predate the predictions they score (§5.5)")
    return gold, {"files": {rel: blobs[rel] for rel in present.values()}, "stats": st}


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
    validate_lines(block)


LINE_KINDS = ("validity", "prediction", "success", "kill")
LINE_STATS = ("k", "n", "point", "lower95", "upper95")
LINE_OPS = (">=", "<=", "==", "<", ">")
RATE_METRICS = ("cause_recall_top1", "cause_precision_top1_certified",
                "cause_precision_top1_heuristic", "location_precision_line_certified",
                "location_precision_line_heuristic", "location_precision_cause_heuristic",
                "location_recall_line", "location_recall_file")
COUNT_METRICS = ("inputs.rows", "inputs.fails", "inputs.compiles", "inputs.cause_scored",
                 "inputs.location_scored", "inputs.cause_line_labelled", "inputs.rows_recorded",
                 "excluded.ungraded", "excluded.disagrees_with_record",
                 "excluded.cause_no_error_block", "excluded.cause_inconsistent",
                 "excluded.cause_unclassified", "excluded.location_no_line",
                 "excluded.location_system_frame", "excluded.location_unverified",
                 "excluded.at_record")


def validate_lines(block: dict, require_validity: bool = True) -> None:
    """The FIXED block's schema (review 2, LOW): every line has exactly the
    known keys, a known kind, metric, stat and op, a numeric value and an
    optional non-negative integer min_n; ids are distinct; there is a
    validity line. InputError (exit 2) otherwise -- never a crash."""
    lines = block.get("lines") if isinstance(block, dict) else None
    if not isinstance(lines, list) or not lines:
        raise InputError("the lines block has no lines")
    ids = []
    for ln in lines:
        if not isinstance(ln, dict) or not ({"id", "kind", "metric", "stat", "op", "value"}
                                            <= set(ln) <= {"id", "kind", "metric", "stat",
                                                           "op", "value", "min_n"}):
            raise InputError(f"line {ln!r:.60} has unknown or missing keys")
        if ln["kind"] not in LINE_KINDS or ln["stat"] not in LINE_STATS \
                or ln["op"] not in LINE_OPS:
            raise InputError(f"line {ln['id']}: unknown kind, stat or op")
        if ln["metric"] not in RATE_METRICS + COUNT_METRICS:
            raise InputError(f"line {ln['id']}: unknown metric {ln['metric']!r}")
        if ln["metric"] in COUNT_METRICS and ln["stat"] != "n":
            raise InputError(f"line {ln['id']}: a count metric takes stat 'n'")
        if type(ln["value"]) not in (int, float):
            raise InputError(f"line {ln['id']}: value is not a number")
        if "min_n" in ln and (type(ln["min_n"]) is not int or ln["min_n"] < 0):
            raise InputError(f"line {ln['id']}: min_n is not a non-negative integer")
        ids.append(ln["id"])
    if len(set(ids)) != len(ids):
        raise InputError("duplicate line ids")
    if require_validity and not any(ln["kind"] == "validity" for ln in lines):
        raise InputError("the lines block has no validity line")


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
            row["exclusion_evidence"] = {"package_is_dir": pkg.is_dir(),
                                         "package_is_symlink": pkg.is_symlink()}
        else:
            row["excluded"] = (tree_problem(pkg) or safe_toplevel(pkg, d.get("toplevel"))
                               or (None if d.get("sha256_tree") else
                                   "the grade of record carries no tree hash")
                               or (None if sha256_tree(pkg) == d["sha256_tree"] else
                                   "tree differs from the grade of record"))
            if row["excluded"]:
                # the raw evidence the scorer requires of every exclusion (review 3, M1)
                ev = {"toplevel": d.get("toplevel"), "recorded_sha256_tree": d.get("sha256_tree")}
                if row["excluded"] == "tree differs from the grade of record":
                    ev["observed_sha256_tree"] = sha256_tree(pkg)
                if row["excluded"] in ("symlink in the package tree",
                                       "online-only (dataless) files in the tree",
                                       "special file in the package tree",
                                       "unreadable entry in the package tree"):
                    ev["entries"] = sorted(str(Path(r_).relative_to(pkg) / n_)
                                           for r_, ds, fs in os.walk(pkg, followlinks=False)
                                           for n_ in ds + fs)[:200]
                row["exclusion_evidence"] = ev
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
                row["cli_stdout"] = r.stdout.decode("utf-8", "replace")
                row["cli_stderr"] = r.stderr.decode("utf-8", "replace")
                row["run_roots"] = list(roots)
                row["pred"] = diag.cli_prediction(row["cli_stdout"], row["cli_stderr"], roots)
            except subprocess.TimeoutExpired:
                row["cli_rc"], row["pred"] = -1, {"verdict": "TIMEOUT", "predictions": []}
            run = run_to_fixpoint_full(work, d["toplevel"], oracle.tex_env(td), ns.timeout)
            row.update(rc=run.rc, passes=run.passes, pdf=run.pdf,
                       compiles=run.rc == 0 and run.pdf)
            logp = _oracle.job_output(work, d["toplevel"], ".log")
            log = logp.read_bytes() if logp.is_file() else None
            row["log_sha256"] = hashlib.sha256(log).hexdigest() if log else None
            if log and not row["compiles"]:
                # kept so the scorer can RE-DERIVE the gold (review 2, M2)
                row["log_gz_b64"] = base64.b64encode(zlib.compress(log, 9)).decode()

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
            row["tree_files"] = sorted(str(q.relative_to(work)) for q in work.rglob("*")
                                       if q.is_file())
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

TIERS = ("certified", "heuristic")
# Every reason `record` can give, each with the raw evidence it must carry
# (review 3, M1): an excluded row with another reason, or without its
# evidence, is refused.
EXCLUSION_REASONS = {
    "missing from the corpus": ("package_is_dir", "package_is_symlink"),
    "tree differs from the grade of record": ("recorded_sha256_tree", "observed_sha256_tree"),
    "the grade of record carries no tree hash": ("recorded_sha256_tree",),
    "symlink in the package tree": ("entries",),
    "online-only (dataless) files in the tree": ("entries",),
    "special file in the package tree": ("entries",),
    "unreadable entry in the package tree": ("entries",),
    "toplevel is not a non-empty string": ("toplevel",),
    "toplevel is absolute": ("toplevel",),
    "toplevel has a `..` component": ("toplevel",),
    "toplevel resolves outside the package": ("toplevel",),
    "toplevel is not a file of the package": ("toplevel",),
}


def _kept_log(r: dict) -> bytes | None:
    """The row's kept log, verified against its sha256; None when absent or
    when it does not decode to the logged bytes."""
    if not isinstance(r.get("log_gz_b64"), str):
        return None
    try:
        log = zlib.decompress(base64.b64decode(r["log_gz_b64"], validate=True))
    except Exception:  # noqa: BLE001 -- an undecodable log is no log; the caller refuses
        return None
    return log if hashlib.sha256(log).hexdigest() == r.get("log_sha256") else None


def _gold_from_raw(r: dict, log: bytes) -> dict:
    files = set(r.get("tree_files") or [])
    roots = tuple(r.get("run_roots") or ())
    return diag.diag_record(log, read_source=None,
                            in_tree=lambda n: diag.canon_path(n, roots + (RUN_DIR,)) in files,
                            work_prefixes=(RUN_DIR,) + roots)


def raw_view(r: dict) -> dict:
    """The row AS ITS RAW STORED FIELDS SAY, best effort and never raising:
    the soundness pass (review 3, M2) judges every certified claim the raw
    CLI output contains, before -- and whatever -- the integrity checks say.
    The prediction comes from the stored CLI stdout/stderr whenever present
    (also when cli_rc is -1, M1); compiles from rc and pdf; the gold from the
    kept log, with `verified` taken from the record only when the corpus-free
    facts allow it."""
    rc, pdf = r.get("rc"), r.get("pdf")
    ok_types = type(rc) is int and type(pdf) is bool
    out = {"arxiv_id": r.get("arxiv_id"), "rc": rc if ok_types else -1,
           "compiles": ((rc == 0 and pdf) if rc != -1 else None) if ok_types else None,
           "graded": False, "agrees_with_record": False}
    so, se = r.get("cli_stdout"), r.get("cli_stderr", "")
    roots = r.get("run_roots") if isinstance(r.get("run_roots"), list) else []
    if isinstance(so, str) and isinstance(se, str):
        out["pred"] = diag.cli_prediction(so, se, tuple(str(x) for x in roots))
    else:
        out["pred"] = {"verdict": None, "predictions": []}
    log = _kept_log(r)
    out["gold"] = _gold_from_raw(r, log) if log is not None else diag.diag_record(None)
    if log is not None:
        _set_verified(out["gold"], r)
    return out


def _set_verified(g: dict, r: dict) -> None:
    """`verified` needs the corpus, so it comes from the record -- but only
    when the CORPUS-FREE facts agree (review 3, M3): a certain stack (no
    suspect pop, no underflow) and the gold file among the run's files."""
    L = g.get("location") or {}
    st = L.get("stack_stats") or {}
    stored = ((r.get("gold") or {}).get("location") or {}).get("verified")
    free_ok = (not st.get("suspect_file_pops") and not st.get("underflow")
               and L.get("file") in set(r.get("tree_files") or []))
    L["verified"] = bool(stored) and free_ok
    L["verify_why"] = ((r.get("gold") or {}).get("location") or {}).get("verify_why")
    g["location"] = L


def rederive_row(r: dict, gor_doc: dict, where: str) -> dict:
    """A record row with every scored field RE-DERIVED from what the run
    produced (reviews 2 and 3): graded / compiles / agrees_with_record from
    rc, pdf and cli_rc against the LOADED grade of record; the prediction
    from the CLI's stdout/stderr and run roots WHENEVER they are present; the
    gold from the kept log and the run's file list. The stored prediction and
    gold must equal the re-derived ones; `verified` is the record's only when
    the corpus-free facts agree (and a stored `verified` they contradict is
    refused). An excluded row must give a known reason with its raw evidence
    and carry no prediction or gold. InputError otherwise."""
    from diff_real_roots import row_compiles
    if r.get("excluded"):
        need = EXCLUSION_REASONS.get(r["excluded"])
        if need is None:
            raise InputError(f"{where}: unknown exclusion reason {r['excluded']!r}")
        ev = r.get("exclusion_evidence")
        if not isinstance(ev, dict) or any(k not in ev for k in need):
            raise InputError(f"{where}: an exclusion without its raw evidence {list(need)}")
        if any(k in r for k in ("pred", "gold", "cli_stdout", "log_gz_b64")):
            raise InputError(f"{where}: an excluded row carries a prediction, a gold or run output")
        return r
    out = dict(r)
    for k in ("rc", "pdf", "cli_rc"):
        if k not in r:
            raise InputError(f"{where}: a graded row lacks {k!r}")
    if type(r["rc"]) is not int or type(r["cli_rc"]) is not int or type(r["pdf"]) is not bool:
        raise InputError(f"{where}: rc / cli_rc / pdf have the wrong types")
    out["graded"] = r["rc"] != -1 and r["cli_rc"] != -1
    out["compiles"] = (r["rc"] == 0 and r["pdf"]) if r["rc"] != -1 else None
    out["agrees_with_record"] = (out["compiles"] is not None
                                 and out["compiles"] == row_compiles(gor_doc)
                                 and r["rc"] == gor_doc.get("pdflatex_rc"))
    has_out = isinstance(r.get("cli_stdout"), str) and isinstance(r.get("cli_stderr"), str) \
        and isinstance(r.get("run_roots"), list)
    if has_out:
        pred = diag.cli_prediction(r["cli_stdout"], r["cli_stderr"], tuple(r["run_roots"]))
    elif r["cli_rc"] == -1:
        pred = {"verdict": "TIMEOUT", "predictions": []}
    else:
        raise InputError(f"{where}: a graded row lacks the CLI's output or run roots")
    if r.get("pred") != pred:
        raise InputError(f"{where}: the stored prediction is not the one the CLI's output gives")
    out["pred"] = pred
    for x in pred.get("predictions") or []:
        if x.get("tier") not in TIERS:
            raise InputError(f"{where}: a prediction with tier {x.get('tier')!r}")
    log = _kept_log(r)
    if log is None and isinstance(r.get("log_gz_b64"), str):
        raise InputError(f"{where}: the kept log does not decode to the logged run's")
    if out["compiles"] is False and log is None:
        raise InputError(f"{where}: a failing row lacks its log: the gold cannot be re-derived")
    if log is not None:
        g = _gold_from_raw(r, log)
        stored = r.get("gold") or {}
        sl, gl = dict(stored.get("location") or {}), dict(g.get("location") or {})
        for k in ("verified", "verify_why"):
            sl.pop(k, None)
            gl.pop(k, None)
        if {k: v for k, v in stored.items() if k != "location"} != \
                {k: v for k, v in g.items() if k != "location"} or sl != gl:
            raise InputError(f"{where}: the stored gold is not the one the kept log gives")
        _set_verified(g, r)
        if bool((stored.get("location") or {}).get("verified")) and not g["location"]["verified"]:
            raise InputError(f"{where}: the stored `verified` contradicts the corpus-free facts "
                             f"(stack certainty, file among the run's files)")
        out["gold"] = g
    return out


HEX40, HEX64 = re.compile(r"[0-9a-f]{40}"), re.compile(r"[0-9a-f]{64}")


def check_stamps(repo: Path, art: dict, rel: str, gor_art: dict) -> None:
    """The record is bound to real runs as far as the repository allows
    (reviews 2 and 3): its oracle is the SAME ORACLE as the grade of record's
    (_oracle.require_same_oracle); its grading code is exactly the oracle core
    plus GRADERS, each at its recorded behaviour; measured_at is a commit;
    the CLI provenance is well-formed -- a 64-hex binary sha, a commit, the
    src tree that commit really has -- and, when a CLI built from that same
    src tree is present, its sha256 must match. What remains trusted
    (the corpus bytes, the oracle having run) is stated in §6."""
    import _oracle
    blk = art.get("oracle") or {}
    try:
        _oracle.require_same_oracle(gor_art.get("oracle"), blk, f"{rel} vs its grade of record")
    except _oracle.OracleError as e:
        raise InputError(str(e)) from None
    gc = blk.get("grading_code")
    if not isinstance(gc, dict) or set((gc.get("files") or {})) != \
            set(_oracle.GRADING_CODE_CORE) | set(GRADERS):
        raise InputError(f"{rel}: its grading_code does not name the oracle core and this "
                         f"producer's GRADERS")
    findings, _ = _oracle.grading_code_drift(gc, Path(repo))
    if findings:
        raise InputError(f"{rel}: recorded by other grading code: {findings[0]}")

    def is_commit(x):
        return isinstance(x, str) and HEX40.fullmatch(x) and subprocess.run(
            ["git", "cat-file", "-e", f"{x}^{{commit}}"], cwd=repo,
            capture_output=True).returncode == 0
    if not is_commit(art.get("measured_at_sha")):
        raise InputError(f"{rel}: measured_at_sha is not a commit of this repository")
    cli = art.get("cli") or {}
    if not (isinstance(cli.get("sha256"), str) and HEX64.fullmatch(cli["sha256"])
            and is_commit(cli.get("head"))):
        raise InputError(f"{rel}: its CLI provenance is incomplete or malformed")
    tree = subprocess.run(["git", "rev-parse", f"{cli['head']}:latex-parse/src"], cwd=repo,
                          capture_output=True)
    if tree.returncode != 0 or tree.stdout.decode().strip() != cli.get("src_tree"):
        raise InputError(f"{rel}: its CLI src_tree is not the tree of its head commit")
    built = Path(repo) / "_build/default/latex-parse/src/validators_cli.exe"
    here = subprocess.run(["git", "rev-parse", "HEAD:latex-parse/src"], cwd=repo,
                          capture_output=True).stdout.decode().strip()
    if built.is_file() and here == cli["src_tree"] and subprocess.run(
            ["git", "diff", "--quiet", "HEAD", "--", "latex-parse/src"], cwd=repo).returncode == 0:
        if hashlib.sha256(built.read_bytes()).hexdigest() != cli["sha256"]:
            raise InputError(f"{rel}: the CLI built from its src tree has another sha256")


def seal_stage(repo: Path, path, sealed: frozenset) -> dict:
    """What the SEAL needs before anything of a record is read (review 3, M2):
    its name, its committed blob, JSON, its sample and frame window, and its
    rows being exactly its sample's documents once each. SealError / InputError."""
    seal.refuse_name(path)
    rel = repo_rel(repo, path)
    data, blob = seal.committed(repo, rel)
    try:
        art = json.loads(data)
    except ValueError:
        raise InputError(f"{rel} is not JSON") from None
    if not isinstance(art, dict):
        raise InputError(f"{rel} is not a {diag.SCHEMA} record")
    k = art.get("sample")
    if type(k) is not int:
        raise seal.SealError(f"{rel}: its sample is not the integer 1 or 2")
    offset, n, _ = seal.sample_spec(k)
    if art.get("frame_window") != {"offset": offset, "n": n}:
        raise seal.SealError(f"{rel}: its frame window is not sample {k}'s")
    docs, gor_rel, gor_blob = seal.sample_docs(repo, k, sealed)
    rows = art.get("rows")
    if not isinstance(rows, list) or len(rows) != n or any(not isinstance(r, dict) for r in rows):
        raise InputError(f"{rel} must hold exactly {n} row objects")
    seal.refuse_ids([r.get("arxiv_id") for r in rows], sealed)
    keys = [seal.paper_key(r["arxiv_id"]) for r in rows]
    by_key = {seal.paper_key(d["arxiv_id"]): d for d in docs}
    if len(set(keys)) != n or set(keys) != set(by_key):
        raise InputError(f"{rel}: its rows are not exactly sample {k}'s documents, once each")
    return {"art": art, "rel": rel, "blob": blob, "data": data, "sample": k, "by_key": by_key,
            "gor": (gor_rel, gor_blob)}


def integrity_stage(repo: Path, st: dict) -> tuple[dict, dict]:
    """Everything else (InputError): schema and definitions, the grade of
    record and seal the record names, its stamps, every row re-derived."""
    art, rel = st["art"], st["rel"]
    if art.get("schema") != diag.SCHEMA or art.get("definitions") != diag.DEFINITIONS_VERSION:
        raise InputError(f"{rel} is not a {diag.SCHEMA} record of {diag.DEFINITIONS_VERSION}")
    gor_rel, gor_blob = st["gor"]
    if art.get("grade_of_record") != {"path": gor_rel, "blob": gor_blob}:
        raise InputError(f"{rel} was recorded against another grade of record")
    if art.get("seal_blob") != seal.seal_blob(repo):
        raise InputError(f"{rel} was recorded under another seal")
    check_stamps(repo, art, rel, json.loads(seal.committed(repo, gor_rel)[0]))
    art = dict(art, rows=[rederive_row(r, st["by_key"][seal.paper_key(r["arxiv_id"])],
                                       f"{rel} row {i}") for i, r in enumerate(art["rows"])])
    return art, {"path": rel, "blob": st["blob"],
                 "sha256": hashlib.sha256(st["data"]).hexdigest(), "sample": st["sample"]}


def load_record(repo: Path, path, sealed: frozenset) -> tuple[dict, dict]:
    """seal_stage then integrity_stage (for callers that need both at once)."""
    return integrity_stage(repo, seal_stage(repo, path, sealed))


def evaluate_lines(block: dict, scores: dict) -> list[dict]:
    """Each line: {"id","kind","metric","stat","op","value"[, "min_n"]}.
    `stat` is k, n, point (k/n), lower95 or upper95 of the metric, or the
    count itself for an "inputs." / "excluded." metric. A line whose metric
    has n < min_n (or no observation) is NOT EVALUABLE: holds = None. A
    success line that is not evaluable is not met; a kill line that is not
    evaluable does not fire (pre-registration §7)."""
    validate_lines(block, require_validity=False)
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


def score_artefacts(arts: list[dict], block: dict,
                    cause_labels: dict | None = None) -> tuple[dict, bool]:
    """(output, void) from validated records. The soundness block (R4) is in
    the output whether or not the run is void."""
    by_reason: dict = {}
    graded = []
    for art in arts:
        for r in art["rows"]:
            if r.get("excluded"):
                by_reason[r["excluded"]] = by_reason.get(r["excluded"], 0) + 1
            else:
                graded.append(r)
    scores = diag.score_rows(graded, cause_labels)
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
               "validity": [ln for ln in lines if ln["kind"] == "validity"],
               "soundness": scores["soundness"]}
        return out, True
    scores["void"] = False
    scores["lines"] = lines
    return scores, False


def score(ns, repo: Path) -> int:
    """THE ORDER (pre-registration §6; review 3, M2):
      (1) the SEAL only (exit 3; a record that is not JSON exits 2): nothing
          of a record is read before its ids are proven to be sample 1-2's;
      (2) SOUNDNESS from the RAW stored fields of every seal-passing row: a
          wrong certified claim is reported (exit 5) whatever follows -- the
          record's integrity, the lines' status; when integrity also fails the
          outcome says so ("SOUNDNESS-DEFECT (record integrity also failed)");
      (3) INTEGRITY (exit 2): schema, grade of record, seal, stamps, every row
          re-derived;
      (4) the lines must be FIXED and valid (exit 2); (5) the cause labels;
      (6) the metrics, VOID (exit 4) or SCORED (exit 0)."""
    sealed = seal.sealed_ids(repo)
    if len(ns.records) != 2:
        raise InputError("score takes exactly two records: sample 1's and sample 2's")
    seal.refuse_name(ns.out)
    staged = [seal_stage(repo, f, sealed) for f in ns.records]
    if sorted(st["sample"] for st in staged) != [1, 2]:
        raise InputError("the two records must be sample 1 and sample 2, once each")
    raw = [raw_view(r) for st in staged for r in st["art"]["rows"]]
    snd = diag.score_rows(raw)["soundness"]
    loaded, integrity = [], []
    for st in staged:
        try:
            loaded.append(integrity_stage(repo, st))
        except (InputError, seal.SealError) as e:
            integrity.append(str(e))
    prov = {"head": _git_head(repo), "seal_blob": seal.seal_blob(repo),
            "records": [{"path": st["rel"], "blob": st["blob"],
                         "sha256": hashlib.sha256(st["data"]).hexdigest(),
                         "sample": st["sample"]} for st in staged]}
    if snd["certified_wrong"] > 0:
        out = {"outcome": "SOUNDNESS-DEFECT" + (" (record integrity also failed)"
                                                if integrity else ""),
               "definitions": diag.DEFINITIONS_VERSION, "soundness": snd,
               "integrity_failures": integrity, "provenance": prov}
        Path(ns.out).write_text(json.dumps(out, indent=1, sort_keys=True) + "\n")
        print(f"[p2-baseline] {out['outcome']}: {snd['certified_wrong']} wrong certified "
              f"claim(s) -- the certified channel stops and the class is fixed (R4; not a "
              f"kill; judged from the raw stored output) -> {ns.out}", file=sys.stderr)
        return EXIT_SOUNDNESS
    if integrity:
        raise InputError(integrity[0])
    block, prereg_blob = committed_lines(repo)
    require_fixed(block)
    labels, labels_prov = committed_labels(repo, [p["path"] for _, p in loaded])
    out, void = score_artefacts([a for a, _ in loaded], block, labels)
    out["provenance"] = dict(prov, prereg={"path": PREREG, "blob": prereg_blob},
                             cause_labels=labels_prov)
    out["outcome"] = "VOID" if void else "SCORED"
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
