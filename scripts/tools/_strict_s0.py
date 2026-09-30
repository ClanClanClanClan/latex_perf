"""Shared harness of the strict-tier kernel L_S0 (ADR-012, milestone M2 phase 1).

Used by `gen_strict_signatures.py` (the probe-attested signatures of the
article contract) and `strict_differential.py` (the directed rule probes and
the generated differential). Three things live here, each written once:

* `Kernel`: the EXTRACTED Coq decider and renderer, run through
  `latex-parse/strict/strict_decide.exe` (built from
  `latex-parse/strict/strict_kernel_extracted.ml`, the extraction of
  `proofs/Strict`). The harness never re-implements the semantics in Python:
  every model verdict it reports is the extracted `decide`'s, and every
  document it grades is the extracted `render`'s bytes.
* `grade`: one document through the ONE oracle (`_oracle.py`, the pinned
  image; ADR-012 decision 7), with the log's first error and its line.
* `agrees`: the comparison rule. A model verdict agrees with the oracle iff
    - READY: rc 0 and a PDF;
    - NOT-READY E0: rc 0 and no PDF;
    - NOT-READY other: rc != 0, the first `!` message is one pdfTeX gives for
      that reason at that token in that mode (`EXPECTED`), and the line of
      the fatal token equals the oracle's `l.N` (both absent at end of file).
  A wrong reason or a wrong line is a disagreement (ADR-012 decision 6:
  wrong reason or location counts as strict_wrong).
"""
from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import _oracle  # noqa: E402
from check_strict_kernel import MAX_BRACE_DEPTH, MAX_TOKENS  # noqa: E402,F401

REPO = Path(__file__).resolve().parents[2]
CONTRACT = REPO / "corpora/contracts/article.json"
SIGNATURES = REPO / "corpora/contracts/strict/article-s0-signatures.json"
EXE_REL = "latex-parse/strict/strict_decide.exe"
EXTRACT = REPO / "latex-parse/strict/strict_kernel_extracted.ml"
# M2 phase 2: the decision on bytes (proofs/Strict/ExtractBytes.v) and the
# lexical contract it reads (gen_strict_lexical.py).
BYTES_EXTRACT = REPO / "latex-parse/strict/strict_bytes_extracted.ml"
LEXICAL = REPO / "corpora/contracts/strict/article-s0-lexical.json"


def sha256_file(p: Path) -> str:
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def kernel_path() -> Path:
    c = json.loads(CONTRACT.read_text())
    return REPO / c["kernel"]["file"]


def members() -> set[str]:
    """The closed world at body start, by the loader's rule (strict_decide.ml
    `load_members`): kernel names, updated by the contract's defined_names."""
    k = json.loads(kernel_path().read_text())
    c = json.loads(CONTRACT.read_text())
    m = set(k["names"])
    for n, v in c["defined_names"].items():
        if v.get("kind") == "Undefined":
            m.discard(n)
        else:
            m.add(n)
    return m


def primitives() -> set[str]:
    """The engine's primitives, from the kernel file (gen_contract.py counts
    them against TeX's own count)."""
    k = json.loads(kernel_path().read_text())
    return set(k["primitives"]["names"])


def source_block() -> dict:
    k = json.loads(kernel_path().read_text())
    c = json.loads(CONTRACT.read_text())
    return {
        "kernel": str(kernel_path().relative_to(REPO)),
        "kernel_sha256": sha256_file(kernel_path()),
        "kernel_meanings_sha256": k["meanings_sha256"],
        "contract": str(CONTRACT.relative_to(REPO)),
        "contract_sha256": sha256_file(CONTRACT),
        "contract_config_key": c["config_key"],
    }


def build_exe() -> Path:
    r = subprocess.run(["opam", "exec", "--", "dune", "build", "--root", str(REPO),
                        EXE_REL], cwd=REPO, capture_output=True, text=True)
    if r.returncode != 0:
        raise SystemExit(f"cannot build {EXE_REL}:\n{r.stderr[-2000:]}")
    return REPO / "_build/default" / EXE_REL


class Kernel:
    """The extracted decider. `signatures=None` runs with no attested name
    (every defined control word is then outside the tier)."""

    def __init__(self, signatures: Path | None = SIGNATURES):
        self.exe = build_exe()
        self.args = [str(self.exe), "--kernel", str(kernel_path()),
                     "--contract", str(CONTRACT)]
        if signatures is not None:
            sig = json.loads(Path(signatures).read_text())
            src = source_block()
            for k in ("kernel_sha256", "contract_sha256"):
                if sig["source"][k] != src[k]:
                    raise SystemExit(f"{signatures} was generated from another "
                                     f"{k.split('_')[0]} file ({k} differs)")
            self.args += ["--signatures", str(signatures)]

    def run(self, requests: list[dict]) -> list[dict]:
        """Each request: {"doc": {...}, optional "signatures": {...}}."""
        payload = "".join(json.dumps({"id": i, **r}) + "\n"
                          for i, r in enumerate(requests))
        p = subprocess.run(self.args, input=payload, capture_output=True,
                           text=True)
        if p.returncode != 0:
            raise SystemExit(f"strict_decide failed rc={p.returncode}: "
                             f"{p.stderr[-2000:]}")
        out = [json.loads(line) for line in p.stdout.splitlines() if line.strip()]
        if len(out) != len(requests):
            raise SystemExit(f"strict_decide answered {len(out)} of "
                             f"{len(requests)} requests")
        for o in out:
            if "error" in o:
                raise SystemExit(f"strict_decide rejected request {o['id']}: "
                                 f"{o['error']}")
        return sorted(out, key=lambda o: o["id"])


class BytesKernel:
    """The extracted decider on BYTES (DecideBytes.decide_bytes), with the
    committed signature file and lexical contract. Each request is a file's
    bytes; each answer is strict_decide.ml's `decide_bytes_json` record
    (verdict, reason, line, the token and mode of the fatal, the reader's and
    the kernel's coverage labels, `explain`)."""

    def __init__(self, signatures: Path = SIGNATURES, lexical: Path = LEXICAL):
        self.exe = build_exe()
        src = source_block()
        for path in (signatures, lexical):
            d = json.loads(Path(path).read_text())
            for k in ("kernel_sha256", "contract_sha256"):
                if d["source"][k] != src[k]:
                    raise SystemExit(f"{path} was generated from another "
                                     f"{k.split('_')[0]} file ({k} differs)")
        self.args = [str(self.exe), "--bytes", "--kernel", str(kernel_path()),
                     "--contract", str(CONTRACT), "--signatures", str(signatures),
                     "--lexical", str(lexical)]

    def run(self, files: list[bytes]) -> list[dict]:
        payload = "".join(json.dumps({"id": i, "hex": b.hex()}) + "\n"
                          for i, b in enumerate(files))
        p = subprocess.run(self.args, input=payload, capture_output=True, text=True)
        if p.returncode != 0:
            raise SystemExit(f"strict_decide --bytes failed rc={p.returncode}: "
                             f"{p.stderr[-2000:]}")
        out = [json.loads(line) for line in p.stdout.splitlines() if line.strip()]
        if len(out) != len(files):
            raise SystemExit(f"strict_decide answered {len(out)} of {len(files)}")
        for o in out:
            if "error" in o:
                raise SystemExit(f"strict_decide rejected request {o['id']}: {o['error']}")
        return sorted(out, key=lambda o: o["id"])


# ---------------------------------------------------------------- oracle ---

def _first_error(log_text: str) -> tuple[str, int | None]:
    """The first `!` message (re-joined across TeX's 79-column wrap) and the
    first `l.N` after it (None when TeX shows no source line, e.g. at end of
    file)."""
    lines = log_text.split("\n")
    for i, line in enumerate(lines):
        if line.startswith("!"):
            msg = line
            j = i
            while len(lines[j]) == 79 and j + 1 < len(lines):
                j += 1
                msg += lines[j]
            ln = None
            for k in range(i + 1, min(len(lines), i + 60)):
                m = re.match(r"^l\.(\d+)", lines[k])
                if m:
                    ln = int(m.group(1))
                    break
                if lines[k].startswith("!"):
                    break
            return msg, ln
    return "", None


# The oracle timeout is PART of oracle_ok (Bridge.v, design §B.4): a run that
# times out is not "compiles". Inside the capacity bounds the slowest documents
# measured are 6,666 forced pages (47-52 s) and 19,995 \mathstrut in one display
# (54.7 s, under load) -- the final OPEN-121 review, r1f/adv3.log. The default
# is the harnesses' 300 s (strict_differential, gen_strict_signatures), so an
# ad-hoc caller cannot get a flaky disagreement from a tighter one.
GRADE_TIMEOUT_S = 300


def grade(oracle, tex: str, timeout: int = GRADE_TIMEOUT_S) -> dict:
    """One document through the oracle's protocol. An OracleError propagates:
    an infrastructure failure is never a grade."""
    with oracle.tempdir("lp-strict-s0-") as td:
        td = Path(td)
        (td / "main.tex").write_text(tex, encoding="ascii")
        r = oracle.run_to_fixpoint(td, "main.tex", oracle.tex_env(td), timeout)
        log = _oracle.job_output(td, "main.tex", ".log")  # pdfTeX's job name
        text = log.read_text(errors="replace") if log.is_file() else ""
        msg, ln = _first_error(text)
        return {"rc": r.rc, "pdf": r.pdf, "passes": r.passes,
                "timed_out": r.timed_out, "error": msg, "line": ln}


def grade_bytes(oracle, b: bytes, timeout: int = GRADE_TIMEOUT_S) -> dict:
    """`grade` for a file given as BYTES (written byte for byte)."""
    with oracle.tempdir("lp-strict-bytes-") as td:
        td = Path(td)
        (td / "main.tex").write_bytes(b)
        r = oracle.run_to_fixpoint(td, "main.tex", oracle.tex_env(td), timeout)
        log = _oracle.job_output(td, "main.tex", ".log")  # pdfTeX's job name
        text = log.read_text(errors="replace") if log.is_file() else ""
        msg, ln = _first_error(text)
        return {"rc": r.rc, "pdf": r.pdf, "passes": r.passes,
                "timed_out": r.timed_out, "error": msg, "line": ln}


# ------------------------------------------------------------ comparison ---

# (reason, token at the fatal, mode) -> the first `!` messages pdfTeX gives.
# Each is attested by the rule probes (corpora/strict_s0/rule_probes.json);
# a message outside its row is a wrong reason, i.e. a disagreement.
_MISSING_DOLLAR = r"^! Missing \$ inserted\.$"
_MATH_ONLY = r"^! LaTeX Error: .*allowed only in math mode\.$"
_NOT_IN_MATH = r"^! (You can't use `.*' in math mode\.|LaTeX Error: .* invalid in math mode\.)$"
_TOO_MANY = r"^! Too many \}'s\.$"
_EXTRA_CLOSE = r"^! Extra \}, or forgotten \$\.$"
_MISSING_CLOSE = r"^! Missing \} inserted\.$"
_BAD_DELIM = r"^! LaTeX Error: Bad math environment delimiter\.$"
_DISPLAY_END = r"^! Display math should end with \$\$\.$"
# E5 by the token that raised it and the mode it met (Semantics.v comments).
_E5 = {
    ("close", "text"): (_TOO_MANY,),
    ("close", "math"): (_EXTRA_CLOSE,),
    # $ in display with a bad follower / $ inside a math brace group
    ("dollar", "math"): (_DISPLAY_END, _MISSING_CLOSE),
    ("open_paren", "math"): (_BAD_DELIM,),
    ("open_bracket", "math"): (_BAD_DELIM,),
    ("close_paren", "text"): (_BAD_DELIM,),
    # \) in display / inside a math brace group
    ("close_paren", "math"): (_BAD_DELIM, _MISSING_CLOSE),
    ("close_bracket", "text"): (_BAD_DELIM,),
    ("close_bracket", "math"): (_BAD_DELIM,),
    ("end", "math"): (_MISSING_DOLLAR,),
    ("eof", "text"): (r"^! Emergency stop\.$",),
    ("eof", "math"): (r"^! Emergency stop\.$",),
}


def expected_messages(reason: str, tok: str, mode: str) -> tuple[str, ...]:
    if reason == "E1":
        return (r"^! Undefined control sequence\.$",)
    if reason == "E3":
        if tok in ("sup", "sub"):
            return (_MISSING_DOLLAR,)
        if tok == "cs":
            return (_MISSING_DOLLAR, _MATH_ONLY) if mode == "text" else (_NOT_IN_MATH,)
    if reason == "E4":
        return {"sup": (r"^! Double superscript\.$",),
                "sub": (r"^! Double subscript\.$",)}.get(tok, ())
    if reason == "E5":
        return _E5.get((tok, mode), ())
    if reason == "E6":
        if tok in ("blank_line", "par") or (tok == "cs" and mode == "math"):
            return (_MISSING_DOLLAR,)
    return ()


def agrees(model: dict, oracle: dict) -> tuple[bool, str]:
    """(agreement, why) for one extracted-decider verdict against one grade."""
    v = model["verdict"]
    if v == "not_strict":
        return False, "model: outside the tier (the harness generated a non-strict document)"
    if oracle["timed_out"]:
        return False, "oracle timed out"
    rc, pdf = oracle["rc"], oracle["pdf"]
    if v == "ready":
        if rc == 0 and pdf:
            return True, "ready"
        return False, f"model READY, oracle rc={rc} pdf={pdf} {oracle['error']!r}"
    r = model["reason"]
    if r == "E0":
        if rc == 0 and not pdf:
            return True, "E0"
        return False, f"model E0, oracle rc={rc} pdf={pdf} {oracle['error']!r}"
    if rc == 0:
        return False, f"model {r}, oracle rc 0 pdf={pdf}"
    pats = expected_messages(r, model["loc_tok"], model.get("loc_mode", ""))
    if not any(re.match(p, oracle["error"]) for p in pats):
        return False, (f"wrong reason: model {r} at {model['loc_tok']} "
                       f"({model.get('loc_mode')}), oracle {oracle['error']!r}")
    if model["loc_line"] != oracle["line"]:
        return False, (f"wrong location: model line {model['loc_line']}, "
                       f"oracle l.{oracle['line']}")
    return True, r


def verdict_class(model: dict) -> str:
    if model["verdict"] == "not_ready":
        return model["reason"]
    return model["verdict"].upper()


# --------------------------------------------------------- node builders ---

def text(w): return ["text", w]
def space(): return ["space"]
def par(explicit=False): return ["par", explicit]
def group(*b): return ["group", list(b)]
def stray(): return ["stray"]
def math(kind, *b): return ["math", kind, list(b)]
def script(up, a): return ["script", up, a]
def cmd(n): return ["cmd", n]
def doc(*body, has_end=True): return {"body": list(body), "has_end": has_end}
