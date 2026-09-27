#!/usr/bin/env python3
"""Gate: every pdflatex grade the project publishes names the ONE oracle.

WHY (ADR-012 decision 7, OPEN-118). Every earlier pin check compared the
`pdflatex --version` banner with `pdfTeX 3.141592653-2.6-1.40.29`. The banner
pins the engine binary and nothing else: the maintainer's laptop printed that
exact banner while its macro layer differed from CI's image in 190 TeX Live
packages (89 at newer revisions, 94 absent from its package database,
pdfmanagement among them). So a banner check passed while the thing it was
meant to guarantee -- that two graders agree -- was false.

The oracle is now the digest-pinned image in tex-oracle.yml, run through
`scripts/tools/_oracle.py`. This gate is pure (no TeX, no docker, no corpus)
and checks four things:

  1. `_oracle.py`'s recorded tree fingerprints were measured for the digest
     tex-oracle.yml pins, for both platform images (arm64 and amd64), and the
     two agree on the macro layer. A re-pin that forgets to re-measure fails.
  2. Every graded artefact in GRADED records `image` equal to the pinned
     digest, the pinned engine version, a `backend` in {container, native},
     and, for its recorded `arch`, the `tlpdb_sha256`, `macro_layer_sha256`
     and `fmt_sha256` that `_oracle.TREE_FINGERPRINTS` holds for that
     architecture. The image string alone is not evidence: two of these
     blocks were stamped by hand, and a hand edit of `image` satisfied the
     old check. An artefact still carrying a host-graded block fails, unless
     it is in PRE_BASELINE with the ledger row that removes it.
  3. PRE_BASELINE is pinned to its exact contents: widening it silently fails,
     and an entry whose artefact has since been re-graded fails too.
  4. No tracked code starts a TeX engine (pdflatex, latexmk, xelatex,
     lualatex) outside `_oracle.py` and `_oracle.sh`. Scanned: every tracked
     .py, .sh/.bash, Makefile/.mk, .ml and workflow file, not only scripts/.
     The rules, each with a kill-test in check_gate_selftests.py:
       Python  every string literal that names an engine, found by the
               tokenizer (so a list split over lines is still one list), is a
               finding unless it is data: a dict key (`"pdflatex": ...`), the
               value of a recorded-metadata key (`"engine": "pdflatex"`, the
               keys in DATA_KEYS only: any other dict value is a finding,
               because `E = {"tex": "pdflatex"}; run([E["tex"], t])` evaded
               the old blanket dict-value exemption), a subscript
               (`x["pdflatex"]`), an argument of .get/.setdefault/.pop, or an
               operand of ==, !=, in. Bytes literals are scanned like str
               ones, and adjacent literals are joined first (`"pdf" "latex"`
               is one literal to Python). That catches
               `["timeout", "60", "pdflatex", t]`, `("pdflatex", t)`,
               `ENGINE = "pdflatex"`, `shutil.which("pdflatex")`, and a shell
               string such as `f"pdflatex {t}"` or `"pdflatex main.tex"`.
       shell   a bare engine token anywhere on a code line (comments
               stripped), except inside an echo/printf message. The message
               exemption covers ONE command: the line is split at `;`, `&&`,
               `||` and `|` outside quotes first, so `echo x && pdflatex t`
               and `printf t | xargs pdflatex` are findings. An engine name
               assembled from a variable (`${P}latex`, `pdf$X`) is a finding.
               .zsh/.ksh files are scanned as shell.
       other   in a tracked .c/.h/.rs/.js/.ts/.rb/.pl/.go/.lua file, a
               quoted literal that is an engine or an engine command line.
       OCaml   a file that spawns processes (Sys.command, Unix.create_process,
               Unix.open_process*, Unix.exec*) must not name an engine in a
               string literal.
       workflow  as shell, minus `name:` keys, with an exact allow-list of the
               in-image canary lines of tex-oracle.yml (they run INSIDE the
               pinned image, which is the oracle).
     This is a static scan and cannot be complete (an engine name built at
     run time evades it); it closes the shapes measured to evade the previous
     regex, which matched only a Python list whose FIRST element was the
     literal "pdflatex", and only under scripts/.

Run: python3 scripts/tools/check_oracle_pin.py --repo .
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import _oracle  # noqa: E402

# (artefact, key path to the recorded oracle block)
GRADED = (
    ("corpora/real_roots/results.json", ("oracle",)),
    ("corpora/real_roots/manifest.json", ("oracle",)),
    ("corpora/real_roots/results_sample2.json", ("oracle",)),
    ("corpora/apply_fixes_real/results.json", ("provenance", "oracle")),
    ("corpora/apply_fixes_real/results_virgin.json", ("provenance", "oracle")),
    ("corpora/apply_fixes_real/results_fresh.json", ("provenance", "oracle")),
    ("corpora/strict_battery/manifest.json", ("provenance", "oracle_provenance")),
    ("corpora/false_ready/manifest.json", ("oracle",)),
    ("corpora/apply_fixes/manifest.json", ("oracle",)),
    ("corpora/oracle_baseline/equivalence.json", ("oracle",)),
)

# Graded artefacts NOT re-graded in the oracle-baseline change, each with the
# reason and the ledger row that removes it. Exact contents are pinned.
PRE_BASELINE = {
    "corpora/apply_fixes_real/rule_attribution_400_719.json":
        "OPEN-118: a greedy per-rule bisection over 320 papers (thousands of "
        "compiles); its conclusions are per-rule, and re-grading it is a new "
        "experiment, not a re-grade. Its engine field names the host TeX Live.",
    "corpora/apply_fixes_real/guard_simulation.json":
        "OPEN-118: a hunk-reversion SIMULATION of a guard that was never built "
        "(OPEN-109); historical evidence for a decision already taken.",
    "corpora/apply_fixes_real/policy_confirmation_2600.json":
        "OPEN-118: the sealed-window confirmation of OPEN-112's allow-list, "
        "taken under the host TeX Live.",
    "corpora/apply_fixes_real/fix_meaning_audit.json":
        "OPEN-118: the per-rule meaning audit (word/layout diffs of PDFs); its "
        "rc columns were graded by the host TeX Live.",
}
PRE_BASELINE_SIZE = 4

# Files allowed to start pdflatex: the oracle itself. And files not scanned
# because they NAME engines as data about this scan: this gate (its ENGINES
# tuple) and the selftest harness (its kill-test payloads are the evasion
# shapes, written out).
ORACLE_FILES = {"scripts/tools/_oracle.py", "scripts/tools/_oracle.sh"}
SCANNER_FILES = {"scripts/tools/check_oracle_pin.py",
                 "scripts/tools/check_gate_selftests.py"}
ENGINES = ("pdflatex", "latexmk", "xelatex", "lualatex")
_ENG_ALT = "|".join(ENGINES)
ENGINE_LITERAL = re.compile(rf"^(\S*/)?({_ENG_ALT})$")
# A string that is a shell command line starting with an engine.
ENGINE_CMDLINE = re.compile(rf"^\s*(\S*/)?({_ENG_ALT})\s+(-|\S+\.tex\b|\{{|\$|\"|')")
BARE_TOKEN = re.compile(rf"(^|[^A-Za-z0-9_./-])({_ENG_ALT})([^A-Za-z0-9_.-]|$)")
SH_MESSAGE = re.compile(r"^\s*(echo|printf|die_infra|die|warn|log)\b")
ML_SPAWN = re.compile(r"Sys\.command|create_process|open_process|Unix\.exec")
ML_LITERAL = re.compile(rf'"[^"\n]*\b({_ENG_ALT})\b[^"\n]*"')
DATA_CALLS = {"get", "setdefault", "pop"}
# Dict keys whose engine-valued VALUE is recorded metadata, not a command.
DATA_KEYS = {"engine", "declared_compiler", "compiler", "protocol"}
# An engine name assembled at run time in shell: `${P}latex`, `$P"latex"`,
# `pdf${X}`, `pdf$X`.
SH_BUILT = re.compile(r"(\$\{?[A-Za-z_][A-Za-z0-9_]*\}?|\$\([^)]*\))[\"']?(la)?tex(mk)?\b"
                      r"|\b(pdf|xe|lua)[\"']?\$\{?[A-Za-z_(]")
SH_SPLIT = re.compile(r"&&|\|\||;|\|")
OTHER_CODE_EXT = (".c", ".h", ".rs", ".js", ".mjs", ".ts", ".rb", ".pl",
                  ".pm", ".go", ".lua", ".java")
OTHER_LITERAL = re.compile(r"\"((?:[^\"\\\n]|\\.)*)\"|'((?:[^'\\\n]|\\.)*)'")
COMPARE_OPS = {"==", "!=", "in"}
# Workflow lines that run an engine INSIDE the pinned image (the oracle
# itself). Exact stripped lines, pinned by count: a new one fails.
WORKFLOW_ALLOW = {
    ".github/workflows/tex-oracle.yml": (
        'got=$(docker run --rm "$TEX_IMAGE" pdflatex --version | head -1)',
        'if ! pdflatex -interaction=nonstopmode -halt-on-error canary.tex >canary.stdout 2>&1 \\',
        '&& pdflatex -interaction=nonstopmode -halt-on-error t.tex >t.log 2>&1 \\',
    ),
}
FINGERPRINT_KEYS = ("tlpdb_sha256", "macro_layer_sha256", "fmt_sha256")
BACKENDS = {"container", "native"}


def _py_string_value(tok: str) -> str | None:
    """The text of a string token, prefixes and quotes removed. f-strings
    keep their `{...}` fields verbatim, which is what ENGINE_CMDLINE needs."""
    m = re.match(r"^([rRbBuUfF]*)('\'\'|\"\"\"|'|\")(.*)\2$", tok, re.S)
    if not m:
        return None
    # Bytes literals are scanned too: `subprocess.run([b"pdflatex", t])`
    # starts an engine exactly as the str literal does.
    return m.group(3)


def scan_python(text: str) -> list[tuple[int, str]]:
    """(line, literal) for every engine literal in executable position."""
    import io
    import tokenize
    try:
        toks = list(tokenize.generate_tokens(io.StringIO(text).readline))
    except (tokenize.TokenError, SyntaxError, IndentationError):
        # Untokenizable file: fall back to a line scan for engine literals.
        return [(n, m.group(0)) for n, line in enumerate(text.split("\n"), 1)
                for m in [re.search(rf"[\"']({_ENG_ALT})[\s\"']", line)] if m
                and not line.lstrip().startswith("#")]
    skip = (tokenize.NL, tokenize.NEWLINE, tokenize.COMMENT, tokenize.INDENT,
            tokenize.DEDENT)
    raw = [t for t in toks if t.type not in skip]
    # Python >= 3.12 tokenizes an f-string as FSTRING_START ... FSTRING_END;
    # collapse each into ONE string unit carrying its source text, so
    # `f"pdflatex {t}"` is seen exactly as it is on 3.11.
    fs_start = getattr(tokenize, "FSTRING_START", None)
    fs_end = getattr(tokenize, "FSTRING_END", None)
    lines = text.split("\n")

    def src(a, b):
        (l0, c0), (l1, c1) = a, b
        if l0 == l1:
            return lines[l0 - 1][c0:c1]
        return "\n".join([lines[l0 - 1][c0:]] + lines[l0:l1 - 1] + [lines[l1 - 1][:c1]])

    class _U:
        def __init__(self, type_, string, start):
            self.type, self.string, self.start = type_, string, start
    sig, j = [], 0
    while j < len(raw):
        t = raw[j]
        if fs_start is not None and t.type == fs_start:
            depth, k = 1, j + 1
            while k < len(raw) and depth:
                depth += (raw[k].type == fs_start) - (raw[k].type == fs_end)
                k += 1
            sig.append(_U(tokenize.STRING, src(t.start, raw[k - 1].end), t.start))
            j = k
            continue
        sig.append(t)
        j += 1
    # Implicit concatenation: `"pdf" "latex"` is ONE literal to Python, so
    # adjacent string units are joined before matching (quotes re-added so
    # _py_string_value can strip them).
    joined = []
    for t in sig:
        if (t.type == tokenize.STRING and joined
                and joined[-1].type == tokenize.STRING):
            a = _py_string_value(joined[-1].string)
            b = _py_string_value(t.string)
            if a is not None and b is not None:
                joined[-1] = _U(tokenize.STRING, '"' + a + b + '"', joined[-1].start)
                continue
        joined.append(t)
    sig = joined
    hits = []
    for i, t in enumerate(sig):
        if t.type != tokenize.STRING:
            continue
        val = _py_string_value(t.string)
        if val is None or not (ENGINE_LITERAL.match(val) or ENGINE_CMDLINE.match(val)):
            continue
        prev = sig[i - 1].string if i else ""
        nxt = sig[i + 1].string if i + 1 < len(sig) else ""
        before_prev = sig[i - 2].string if i >= 2 else ""
        if True:  # data positions exempt both an engine name and a command line
            if nxt == ":" and prev in ("{", ","):
                continue                       # dict key
            if (prev == ":" and i >= 2 and sig[i - 2].type == tokenize.STRING
                    and _py_string_value(sig[i - 2].string) in DATA_KEYS):
                continue                       # recorded metadata {"engine": ...}
            if prev == "[" and nxt == "]" and before_prev not in ("", "=", "(", ",", "[", "return"):
                continue                       # subscript x["pdflatex"]
            if prev == "(" and before_prev in DATA_CALLS:
                continue                       # d.get("pdflatex")
            if prev in COMPARE_OPS or nxt in COMPARE_OPS or (prev == "not" and nxt != ","):
                continue                       # comparison operand
        hits.append((t.start[0], val))
    return hits


SH_QUOTED = re.compile(r"""\"(?:[^\"\\]|\\.)*\"|'[^']*'""")


def scan_shell(text: str, allow: tuple = ()) -> list[tuple[int, str]]:
    """A shell line starts an engine when the engine is a bare word OUTSIDE
    quotes (`pdflatex x.tex`, `PDF=pdflatex`, `cmd=(pdflatex -x)`), or when a
    quoted word IS an engine or an engine command line (`PDF="pdflatex"`,
    `sh -c 'pdflatex x.tex'`). An engine named inside a longer quoted string
    is a message or a pattern (`echo "... pdflatex failed"`, `grep 'pdftex\\|
    pdflatex'`), and `x['pdflatex']` is a subscript."""
    hits = []
    for n, line in enumerate(text.split("\n"), 1):
        code = line.split("#", 1)[0] if not line.lstrip().startswith("#") else ""
        if not code.strip():
            continue
        if re.match(r"^\s*-?\s*name:", code):
            continue                           # a workflow step's display name
        if line.strip() in allow:
            continue
        hit = False
        for seg in _sh_commands(code):
            if SH_MESSAGE.match(seg):
                continue                       # this ONE command is a message
            unquoted = SH_QUOTED.sub('""', seg)
            if BARE_TOKEN.search(unquoted) or SH_BUILT.search(
                    SH_QUOTED.sub(lambda m: m.group(0) if m.group(0).startswith('"')
                                  else "''", seg)):
                hit = True
            for m in SH_QUOTED.finditer(seg):
                inner = m.group(0)[1:-1]
                subscript = (seg[:m.start()].endswith("[")
                             and seg[m.end():].startswith("]"))
                if not subscript and (ENGINE_LITERAL.match(inner)
                                      or ENGINE_CMDLINE.match(inner)):
                    hit = True
        if hit:
            hits.append((n, line.strip()))
    return hits


def _sh_commands(code: str) -> list[str]:
    """Split a shell line into its commands at `;`, `&&`, `||`, `|` that lie
    OUTSIDE quotes. The echo/printf exemption then applies per command: it
    used to exempt the whole line, so `echo x && pdflatex t.tex` passed."""
    masked = SH_QUOTED.sub(lambda m: "\0" * len(m.group(0)), code)
    out, last = [], 0
    for m in SH_SPLIT.finditer(masked):
        out.append(code[last:m.start()])
        last = m.end()
    out.append(code[last:])
    return [c for c in out if c.strip()]


def scan_other(text: str) -> list[tuple[int, str]]:
    """C, Rust, JS, Ruby, Perl, Go, Lua, Java: a quoted literal that IS an
    engine or an engine command line."""
    hits = []
    for n, line in enumerate(text.split("\n"), 1):
        for m in OTHER_LITERAL.finditer(line):
            inner = m.group(1) if m.group(1) is not None else m.group(2)
            if ENGINE_LITERAL.match(inner) or ENGINE_CMDLINE.match(inner):
                hits.append((n, line.strip()))
                break
    return hits


def scan_ocaml(text: str) -> list[tuple[int, str]]:
    if not ML_SPAWN.search(text):
        return []
    return [(n, m.group(0)) for n, line in enumerate(text.split("\n"), 1)
            for m in [ML_LITERAL.search(line)] if m]


def tracked_files(repo: Path) -> list[str]:
    import subprocess
    r = subprocess.run(["git", "-C", str(repo), "ls-files"], capture_output=True,
                       text=True)
    if r.returncode != 0:
        raise RuntimeError(f"git ls-files failed: {r.stderr.strip()}")
    return r.stdout.split("\n")


def dig(d, path):
    for k in path:
        if not isinstance(d, dict):
            return None
        d = d.get(k)
    return d


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", default=".")
    repo = Path(ap.parse_args().repo).resolve()
    image, version = _oracle.workflow_pin()
    findings: list[str] = []

    # 1. fingerprints measured for THIS digest, both platforms, same macro layer
    if _oracle.FINGERPRINTED_IMAGE != image:
        findings.append(f"tex-oracle.yml pins {image} but _oracle.py's tree "
                        f"fingerprints were measured for "
                        f"{_oracle.FINGERPRINTED_IMAGE}; re-measure both "
                        f"platform images in the re-pin PR")
    fps = _oracle.TREE_FINGERPRINTS
    if set(fps) != {"aarch64", "x86_64"}:
        findings.append(f"_oracle.TREE_FINGERPRINTS covers {sorted(fps)}, "
                        f"expected both aarch64 (local) and x86_64 (CI)")
    elif fps["aarch64"]["macro_layer_sha256"] != fps["x86_64"]["macro_layer_sha256"]:
        findings.append("the arm64 and amd64 images of the pinned digest have "
                        "DIFFERENT macro layers: a local grade would not be the "
                        "CI grade")
    for arch, fp in fps.items():
        for k in FINGERPRINT_KEYS:
            if not re.fullmatch(r"[0-9a-f]{64}", str(fp.get(k, ""))):
                findings.append(f"_oracle.TREE_FINGERPRINTS[{arch}][{k}] is not a sha256")

    # 2./3. every graded artefact names the pinned image
    graded_paths = {p for p, _ in GRADED}
    if len(PRE_BASELINE) != PRE_BASELINE_SIZE:
        findings.append(f"PRE_BASELINE holds {len(PRE_BASELINE)} entries, pinned at "
                        f"{PRE_BASELINE_SIZE}; widening it needs a ledger row and a "
                        f"deliberate edit here")
    for rel in sorted(graded_paths & set(PRE_BASELINE)):
        findings.append(f"{rel} is in both GRADED and PRE_BASELINE")
    for rel, path in GRADED:
        f = repo / rel
        if not f.is_file():
            findings.append(f"{rel}: missing")
            continue
        try:
            block = dig(json.loads(f.read_text()), path)
        except (OSError, json.JSONDecodeError) as e:
            findings.append(f"{rel}: unreadable ({e})")
            continue
        if not isinstance(block, dict):
            findings.append(f"{rel}: no oracle block at {'.'.join(path)}")
            continue
        if block.get("image") != image:
            findings.append(
                f"{rel}: graded by {block.get('image') or 'a host TeX Live (no image recorded)'}"
                f", not the pinned image {image}. Re-grade it through "
                f"scripts/tools/_oracle.py (ADR-012 decision 7).")
        if version not in str(block.get("version", "")):
            findings.append(f"{rel}: oracle version {block.get('version')!r} is not "
                            f"the pin {version!r}")
        if block.get("backend") not in BACKENDS:
            findings.append(f"{rel}: oracle backend {block.get('backend')!r} is not "
                            f"one of {sorted(BACKENDS)}")
        want = fps.get(block.get("arch"))
        if want is None:
            findings.append(f"{rel}: oracle arch {block.get('arch')!r} has no "
                            f"recorded tree fingerprint")
        else:
            for k in FINGERPRINT_KEYS:
                if block.get(k) != want.get(k):
                    findings.append(
                        f"{rel}: oracle {k} {block.get(k)!r} is not the pinned "
                        f"image's {block.get('arch')} tree fingerprint "
                        f"{want.get(k)!r}")
    for rel in sorted(PRE_BASELINE):
        f = repo / rel
        if not f.is_file():
            findings.append(f"{rel}: listed in PRE_BASELINE but missing")
            continue
        if f'"image": "{image}"' in f.read_text():
            findings.append(f"{rel} now records the pinned image but is still in "
                            f"PRE_BASELINE; move it to GRADED")

    # 4. nothing else starts a TeX engine
    scanned = 0
    for rel in sorted(tracked_files(repo)):
        if not rel or rel in ORACLE_FILES or rel in SCANNER_FILES:
            continue
        p = repo / rel
        name = p.name
        if rel.endswith(".py"):
            scan = scan_python
        elif rel.endswith((".sh", ".bash", ".zsh", ".ksh", ".mk")) or name == "Makefile":
            scan = scan_shell
        elif rel.endswith(OTHER_CODE_EXT):
            scan = scan_other
        elif rel.endswith(".ml"):
            scan = scan_ocaml
        elif rel.startswith(".github/workflows/") and rel.endswith((".yml", ".yaml")):
            allow = WORKFLOW_ALLOW.get(rel, ())
            scan = (lambda t, a=allow: scan_shell(t, a))
        else:
            continue
        if not p.is_file():
            continue
        scanned += 1
        for n, what in scan(p.read_text(errors="replace")):
            findings.append(f"{rel}:{n}: starts a TeX engine directly ({what[:60]!r}); "
                            f"go through scripts/tools/_oracle.py (the host TeX "
                            f"Live is not the oracle)")
    for rel, lines in WORKFLOW_ALLOW.items():
        f = repo / rel
        text = f.read_text() if f.is_file() else ""
        stripped = {ln.strip() for ln in text.split("\n")}
        for ln in lines:
            if ln not in stripped:
                findings.append(f"{rel}: allow-listed in-image line no longer "
                                f"present, prune WORKFLOW_ALLOW: {ln[:60]!r}")

    if findings:
        print("[oracle-pin] FAIL:", file=sys.stderr)
        for f in findings:
            print(f"  - {f}", file=sys.stderr)
        return 1
    print(f"[oracle-pin] OK: {len(GRADED)} graded artefacts name {image} with "
          f"its tree fingerprints; {len(PRE_BASELINE)} pre-baseline artefacts "
          f"pinned; {scanned} tracked code files start no TeX engine directly")
    return 0


if __name__ == "__main__":
    sys.exit(main())
