#!/usr/bin/env python3
"""ABLATION: which EDIT CLASS causes the remaining breaks? (OPEN-107)

Applies the default fixer, then reverts whole classes of changed lines back to
their original text and recompiles. No engine change, no rebuild.

Arm CTRL reverts EVERYTHING and therefore MUST compile: without that control an
after-number is compatible with the change having helped, hurt, or done nothing
(C-57). Its absence from v1 of this harness was a real omission.
"""
import json, os, pathlib, re, shutil, subprocess, sys, tempfile, difflib

CLI = pathlib.Path("_build/default/latex-parse/src/validators_cli.exe").resolve()
ROOT = pathlib.Path(os.environ["LP_REAL_CORPUS"])
NORM = re.compile(r"\s+")


def _ops(o, n):
    sm = difflib.SequenceMatcher(None, o, n, autojunk=False)
    return [(t, o[a1:a2], n[b1:b2]) for t, a1, a2, b1, b2 in sm.get_opcodes()
            if t != "equal"]


def is_ws(o, n):
    return NORM.sub(" ", o).strip() == NORM.sub(" ", n).strip()


def is_tie(o, n):
    return any(a == " " and b == "~" for _, a, b in _ops(o, n))


def is_nonascii(o, n):
    return any(b != a and any(ord(c) > 127 for c in b) for _, a, b in _ops(o, n))


def is_math(o, n):
    return any(re.search(r"[\^_]\{", a) or re.search(r"[\^_]\{", b)
               for _, a, b in _ops(o, n))


def build(work, preds, revert_all=False):
    for tex in sorted(work.rglob("*.tex")):
        before = tex.read_bytes()
        try:
            # --apply-fixes-all: this instrument measures the FULL fixer (every rule's
            # fix), which is what the unqualified --apply-fixes meant before the
            # OPEN-105 allow-list made it apply only Fix_policy.default_allowlist.
            p = subprocess.run([str(CLI), "--apply-fixes-all", str(tex)],
                               capture_output=True, timeout=120)
        except subprocess.TimeoutExpired:
            raise RuntimeError(f"fixer timed out on {tex}")
        if p.returncode not in (0, 1):
            # Never read a crash as "changed nothing" (it would score the arm).
            raise RuntimeError(f"fixer crashed (exit {p.returncode}) on {tex}: "
                               f"{p.stderr[-300:]!r}")
        if not (p.returncode in (0, 1) and p.stdout and p.stdout != before):
            continue
        if revert_all:
            continue                      # leave the original bytes untouched
        b = before.decode("utf-8", "replace").splitlines(keepends=True)
        a = p.stdout.decode("utf-8", "replace").splitlines(keepends=True)
        out = []
        for t, i1, i2, j1, j2 in difflib.SequenceMatcher(
                None, b, a, autojunk=False).get_opcodes():
            if t == "equal":
                out.extend(b[i1:i2])
            elif t == "replace":
                for ob, oa in zip(b[i1:i2], a[j1:j2]):
                    out.append(ob if any(f(ob, oa) for f in preds) else oa)
                out.extend(a[j1 + min(i2 - i1, j2 - j1):j2])
                out.extend(b[i1 + min(i2 - i1, j2 - j1):i2])
            elif t == "insert":
                out.extend(a[j1:j2])
            elif t == "delete":
                pass
        tex.write_bytes("".join(out).encode("utf-8", "replace"))


def compile_rc(work, top, td):
    env = dict(os.environ, TEXMFHOME=str(pathlib.Path(td) / "th"),
               TEXMFVAR=str(pathlib.Path(td) / "tv"), openin_any="p",
               openout_any="p", SOURCE_DATE_EPOCH="0")
    rc = None
    for _ in range(2):
        try:
            r = subprocess.run(["pdflatex", "-interaction=nonstopmode",
                                "-halt-on-error", top],
                               cwd=work, env=env, capture_output=True, timeout=180)
        except subprocess.TimeoutExpired:
            return "timeout"
        rc = r.returncode
        if rc != 0:
            break
    return rc


def main():
    rows = json.load(open("corpora/apply_fixes_real/results_fresh.json"))["rows"]
    broken = [r for r in rows if r.get("cell") == "broken"]
    arms = [("0 all-fixes", [], False),
            ("T no-tie", [is_tie], False),
            ("U no-uni", [is_nonascii], False),
            ("M no-math", [is_math], False),
            ("S no-semantic", [is_tie, is_nonascii, is_math], False),
            ("CTRL revert-all", [], True)]
    print(f"{'paper':16s} {'recorded error':30s} " +
          " ".join(f"{a[0]:15s}" for a in arms))
    print("-" * 132)
    for r in broken:
        aid, top = r["arxiv_id"], r["toplevel"]
        cells = []
        for _, preds, rall in arms:
            with tempfile.TemporaryDirectory(dir="/private/tmp") as td:
                work = pathlib.Path(td) / "w"
                shutil.copytree(ROOT / aid, work)
                build(work, preds, rall)
                rc = compile_rc(work, top, td)
            cells.append("COMPILES" if rc == 0 else f"rc={rc}")
        print(f"{aid:16s} {r['first_error_after'][:30]:30s} " +
              " ".join(f"{c:15s}" for c in cells))
    return 0


if __name__ == "__main__":
    sys.exit(main())
