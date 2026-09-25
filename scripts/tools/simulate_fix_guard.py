#!/usr/bin/env python3
"""guardsim -- SIMULATE a proposed class-level Fix_guard in Python, to predict
its effect on the default fixer's real-paper break rate before any OCaml.

Per paper (window = gen_apply_fixes_real_differential.py's frame: the
pdflatex/single-toplevel frame from diff_real_roots.build_frame, ordered by
sha256(arxiv_id) ascending, sliced [offset, offset+n)):

  CTRL   pristine copy                               (must be rc 0, else excluded)
  FULL   the gen tool's recipe: --apply-fixes every .tex in the tree, in place,
         sorted order (gen_apply_fixes_real_differential.apply_fixes_tree)
  GUARD  per .tex: original O, full output F, char-level diff hunks O->F;
         every NON-whitespace hunk whose ORIGINAL span intersects R1..R4 is
         reverted.  Whitespace-only hunks are kept in every arm.
  GUARD_R1..GUARD_R4   single-region ablations, only when FULL broke.

Every arm is compiled on a FRESH copy of the package with
diff_real_roots.run_to_fixpoint (identical env to the gen tool).  An arm whose
bytes are identical to an already-compiled arm reuses that result (recorded as
`reused_from`); pdflatex runs here are deterministic (SOURCE_DATE_EPOCH=0).

CAVEAT (recorded in every output): reverting hunks POST HOC approximates a
per-pass guard.  The fixer converges over up to 64 passes; a real guard would
block an edit at pass k, and passes k+1.. would then see different input, so
cascades (an edit enabled only by an earlier guarded edit, or one that a
guarded edit would have pre-empted) can differ.

Regions (spans of the ORIGINAL text):
  R1 preamble: [0, end of first live \\begin{document}) in a file that has one,
     MINUS the first mandatory {..} arg of typeset front-matter commands
     (FRONT below; \\email deliberately absent -> protected).
  R2 macro-definition code: region_census 'C' regions (\\def-family name+params
     +body, \\let, \\newcommand/\\renewcommand/\\providecommand/
     \\DeclareRobustCommand all args, xparse definers, \\newenvironment family,
     \\DeclareMathOperator) + \\newcolumntype, \\DeclareMathSymbol,
     \\NewExpandableDocumentCommand (whole command incl. args).
  R3 region_census 'A1' regions (bracket opt arg whose top level has '=',
     math-aware) + census 'B' mandatory args whose owner is in R3_CMDS.
  R4 drawing code not in fix_guard.ml picture_envs: envs R4_ENVS (matched
     begin/end, nesting-aware), \\xymatrix/\\xygraph (@-modifiers + {..}),
     \\tikz (opts + {..} or path to ';'), \\pic (to ';').
"""
from __future__ import annotations

import sys
sys.dont_write_bytecode = True   # the repo is read-only for us: no __pycache__

import argparse, bisect, concurrent.futures as cf, hashlib, json, os, pathlib
import re, shutil, subprocess, tempfile, time, traceback

REPO = pathlib.Path(__file__).resolve().parents[2]
SCRATCH = pathlib.Path(os.environ.get("GUARDSIM_TMP") or tempfile.gettempdir())
CLI = REPO / "_build/default/latex-parse/src/validators_cli.exe"
TMPROOT = SCRATCH / "guardsim" / "tmp"

sys.path.insert(0, str(REPO / "scripts/tools"))
from diff_real_roots import PIN, build_frame, run_to_fixpoint  # noqa: E402
from gen_apply_fixes_real_differential import (  # noqa: E402
    apply_fixes_tree, first_error)
import census_fix_regions as rc_mod  # noqa: E402
from census_fix_regions import char_edits, decode_pair, scan  # noqa: E402

REGIONS = ("R1", "R2", "R3", "R4")
CAVEAT = ("Post-hoc hunk reversion approximates a per-pass guard: the fixer "
          "converges over up to 64 passes, so a real guard blocking an edit at "
          "pass k changes the input of passes k+1..; cascades may differ.")

FRONT = {"title", "author", "date", "thanks", "address", "affiliation",
         "affil", "keywords", "abstract", "dedicatory", "subjclass",
         "shorttitle", "shortauthors", "titlerunning", "authorrunning",
         "institute"}
R3_CMDS = {"hypersetup", "tikzset", "pgfkeys", "pgfplotsset", "lstset",
           "sisetup", "captionsetup", "setkeys", "definecolor",
           "usetikzlibrary", "geometry", "typeout", "message", "wlog",
           "PackageWarning", "PackageWarningNoLine", "PackageInfo",
           "PackageError", "ClassWarning", "ClassWarningNoLine", "ClassInfo",
           "ClassError", "GenericWarning", "GenericInfo", "GenericError",
           "errmessage"}
R2_EXTRA = {"newcolumntype": "mom", "DeclareMathSymbol": "mmmm",
            "NewExpandableDocumentCommand": "mmm",
            "RenewExpandableDocumentCommand": "mmm",
            "ProvideExpandableDocumentCommand": "mmm",
            "DeclareExpandableDocumentCommand": "mmm"}
R4_ENVS = {"quantikz", "blochsphere", "xy", "pspicture", "pspicture*",
           "forest", "dot2tex", "axis", "semilogxaxis", "semilogyaxis",
           "loglogaxis", "polaraxis", "groupplot"}
R4_BRACE_CMDS = {"xymatrix", "xygraph"}


# ---------------------------------------------------------------- lexing ---
def comment_intervals(src: str):
    """[(start,end)) of live % comments (a % preceded by an even number of
    backslashes), end = the newline index."""
    out = []
    for m in re.finditer(r"%", src):
        i = m.start()
        k = i - 1
        while k >= 0 and src[k] == "\\":
            k -= 1
        if (i - 1 - k) % 2:
            continue
        if out and out[-1][0] <= i < out[-1][1]:
            continue
        e = src.find("\n", i)
        out.append((i, len(src) if e < 0 else e))
    return out


class Lex:
    def __init__(self, src):
        self.src = src
        self.cm = comment_intervals(src)
        self.cms = [a for a, _ in self.cm]

    def commented(self, pos):
        k = bisect.bisect_right(self.cms, pos) - 1
        return k >= 0 and self.cm[k][0] <= pos < self.cm[k][1]

    def live_cs(self, pattern):
        """live control sequences matching `\\(pattern)` not followed by a
        letter, not escaped (\\\\name is a line break + text)."""
        s = self.src
        for m in re.finditer(r"\\(" + pattern + r")(?![A-Za-z])", s):
            i = m.start()
            k = i - 1
            while k >= 0 and s[k] == "\\":
                k -= 1
            if (i - 1 - k) % 2:
                continue
            if self.commented(i):
                continue
            yield m

    def skip_ws(self, i, allow_par=False):
        s, n = self.src, len(self.src)
        nl = 0
        while i < n:
            c = s[i]
            if c == "%":
                e = s.find("\n", i)
                i = n if e < 0 else e + 1
                nl = 0
                continue
            if c == "\n":
                nl += 1
                if nl >= 2 and not allow_par:
                    return i
                i += 1
                continue
            if c in " \t\r":
                i += 1
                continue
            break
        return i

    def match(self, i, opener):
        """src[i]==opener ('{' or '['); index AFTER the matching closer
        (len(src) if unmatched).  Escapes and comments honoured; for '[',
        brackets count only at brace depth 0."""
        s, n = self.src, len(self.src)
        closer = "}" if opener == "{" else "]"
        depth, bd = 0, 0
        while i < n:
            c = s[i]
            if c == "\\":
                i += 2
                continue
            if c == "%":
                e = s.find("\n", i)
                i = n if e < 0 else e + 1
                continue
            if opener == "{":
                if c == "{":
                    depth += 1
                elif c == "}":
                    depth -= 1
                    if depth == 0:
                        return i + 1
            else:
                if c == "{":
                    bd += 1
                elif c == "}":
                    bd -= 1
                elif bd == 0 and c == "[":
                    depth += 1
                elif bd == 0 and c == "]":
                    depth -= 1
                    if depth == 0:
                        return i + 1
            i += 1
        return n

    def token_end(self, i):
        """end of a single TeX token at i (control sequence or char)."""
        s, n = self.src, len(self.src)
        if i >= n:
            return n
        if s[i] == "\\":
            j = i + 1
            if j < n and s[j].isascii() and s[j].isalpha():
                while j < n and s[j].isascii() and s[j].isalpha():
                    j += 1
                return j
            return min(n, j + 1)
        return i + 1

    def parse_args(self, i, spec):
        """consume args per spec ('*' optional star, 'o' optional [..], 'm'
        mandatory {..} or single token).  Returns end index."""
        s, n = self.src, len(self.src)
        for a in spec:
            j = self.skip_ws(i)
            if a == "*":
                if j < n and s[j] == "*":
                    i = j + 1
            elif a == "o":
                if j < n and s[j] == "[":
                    i = self.match(j, "[")
            elif a == "m":
                if j >= n:
                    return n
                i = self.match(j, "{") if s[j] == "{" else self.token_end(j)
        return i


# --------------------------------------------------------------- regions ---
def subtract(base, holes):
    out = []
    for a, b in base:
        cur = a
        for h1, h2 in sorted(holes):
            if h2 <= cur or h1 >= b:
                continue
            if h1 > cur:
                out.append((cur, h1))
            cur = max(cur, h2)
        if cur < b:
            out.append((cur, b))
    return out


def widen(src, r):
    """census region content [start,end) -> include its delimiters."""
    a, b = r.start, r.end if r.end is not None else len(src)
    if a > 0 and src[a - 1] in "{[":
        a -= 1
    if b < len(src) and src[b] in "}]":
        b += 1
    return a, b


def regions_for(src: str):
    """{R1..R4: [(a,b)) intervals of the ORIGINAL text}, plus diagnostics."""
    L = Lex(src)
    n = len(src)
    out = {k: [] for k in REGIONS}
    diag = {}
    # R1 -----------------------------------------------------------------
    D = None
    for m in re.finditer(r"\\begin\s*\{document\}", src):
        i = m.start()
        k = i - 1
        while k >= 0 and src[k] == "\\":
            k -= 1
        if (i - 1 - k) % 2 or L.commented(i):
            continue
        D = m
        break
    if D is not None:
        holes = []
        for m in L.live_cs("|".join(sorted(FRONT, key=len, reverse=True))):
            if m.start() >= D.start():
                break
            j = L.parse_args(m.end(), "*oo")
            j2 = L.skip_ws(j)
            if j2 < n and src[j2] == "{":
                holes.append((j2, L.match(j2, "{")))
        out["R1"] = subtract([(0, D.end())], holes)
        diag["begin_document"] = D.start()
        diag["frontmatter_exempt"] = len(holes)
    # census scan: R2 (C), R3 (A1, B owned by R3_CMDS) ----------------------
    regs, _ = scan(src)
    for r in regs:
        if r.label == "C":
            out["R2"].append(widen(src, r))
        elif r.label == "A1":
            out["R3"].append(widen(src, r))
        elif r.label == "B" and (r.owner or "").rstrip("*") in R3_CMDS:
            out["R3"].append(widen(src, r))
    for m in L.live_cs("|".join(R2_EXTRA)):
        out["R2"].append((m.start(), L.parse_args(m.end(), "*" + R2_EXTRA[m.group(1)])))
    # R4 -----------------------------------------------------------------
    stacks = {}
    for m in re.finditer(r"\\(begin|end)\s*\{([^{}]*)\}", src):
        env = m.group(2).strip()
        if env not in R4_ENVS:
            continue
        i = m.start()
        k = i - 1
        while k >= 0 and src[k] == "\\":
            k -= 1
        if (i - 1 - k) % 2 or L.commented(i):
            continue
        st = stacks.setdefault(env, [])
        if m.group(1) == "begin":
            st.append(i)
        elif st:
            b = st.pop()
            if not st:
                out["R4"].append((b, m.end()))
    for env, st in stacks.items():   # unmatched begin: protect to EOF
        if st:
            out["R4"].append((st[0], n))
    for m in L.live_cs("|".join(R4_BRACE_CMDS)):
        j = m.end()
        # @-modifiers: @R=1em, @C-2pc, @!0, @M=2pt, @*[r]... up to the '{'
        k = L.skip_ws(j)
        if k < n and src[k] == "@":
            b = src.find("{", k)
            k = n if b < 0 else b
        if k < n and src[k] == "{":
            out["R4"].append((m.start(), L.match(k, "{")))
    for m in L.live_cs("tikz|pic"):
        j = m.end()
        while True:
            k = L.skip_ws(j)
            if k < n and src[k] == "[":
                j = L.match(k, "[")
                continue
            break
        if m.group(1) == "tikz" and k < n and src[k] == "{":
            out["R4"].append((m.start(), L.match(k, "{")))
            continue
        # path to ';' at brace depth 0
        i, depth = k, 0
        while i < n:
            c = src[i]
            if c == "\\":
                i += 2
                continue
            if c == "{":
                depth += 1
            elif c == "}":
                depth -= 1
                if depth < 0:
                    break
            elif c == ";" and depth == 0:
                i += 1
                break
            i += 1
        out["R4"].append((m.start(), min(i, n)))
    for k in REGIONS:
        out[k] = merge(out[k])
    return out, diag


def merge(iv):
    iv = sorted((a, b) for a, b in iv if b > a)
    out = []
    for a, b in iv:
        if out and a <= out[-1][1]:
            out[-1] = (out[-1][0], max(out[-1][1], b))
        else:
            out.append((a, b))
    return out


def hits(iv, starts, s, e):
    """does hunk [s,e) (an insertion when s==e) intersect a MERGED (sorted,
    disjoint) interval list?  Span: overlap.  Insertion: a <= s < b."""
    if e > s:
        k = bisect.bisect_left(starts, e) - 1   # last interval with a < e
        return k >= 0 and iv[k][1] > s
    k = bisect.bisect_right(starts, s) - 1      # last interval with a <= s
    return k >= 0 and s < iv[k][1]


def is_ws(old, new):
    return not old.strip() and not new.strip()


_COARSE_LOCK = __import__("threading").Lock()


def hunks_for(o: str, f: str):
    with _COARSE_LOCK:   # CHARDIFF_COARSE is a module global in region_census
        rc_mod.CHARDIFF_COARSE.clear()
        hs = list(char_edits(o, f))
        coarse = len(rc_mod.CHARDIFF_COARSE)
    return hs, coarse


def rebuild(o, hs, accept):
    """apply the hunks with accept(i)=True to o."""
    out, cur = [], 0
    for idx, (s, e, old, new) in enumerate(hs):
        assert s >= cur, ("hunks out of order", s, cur)
        assert o[s:e] == old, ("hunk old-text mismatch", s, e)
        out.append(o[cur:s])
        out.append(new if accept(idx) else old)
        cur = e
    out.append(o[cur:])
    return "".join(out)


def analyse_file(O: bytes, F: bytes):
    o, f, enc = decode_pair(O, F)
    hs, coarse = hunks_for(o, f)
    # exactness: all-accept == F, none-accept == O.  A failure here is a
    # HARNESS defect and is raised, never silently tolerated.
    if rebuild(o, hs, lambda i: True) != f:
        raise AssertionError("reconstruction(all) != F")
    if rebuild(o, hs, lambda i: False) != o:
        raise AssertionError("reconstruction(none) != O")
    regs, diag = regions_for(o)
    starts = {k: [a for a, _ in regs[k]] for k in REGIONS}
    rows = []
    for s, e, old, new in hs:
        inr = [k for k in REGIONS if hits(regs[k], starts[k], s, e)]
        rows.append({"s": s, "e": e, "old": old, "new": new,
                     "ws": is_ws(old, new), "regions": inr})
    return o, enc, hs, rows, coarse, diag


# ----------------------------------------------------------------- arms ---
def tex_env(td):
    return dict(os.environ, TEXMFHOME=str(pathlib.Path(td) / "th"),
                TEXMFVAR=str(pathlib.Path(td) / "tv"),
                openin_any="p", openout_any="p", SOURCE_DATE_EPOCH="0")


def compile_tree(pkg, toplevel, texts, timeout):
    """fresh copy of pkg, overwrite texts {relpath: bytes}, compile."""
    TMPROOT.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=str(TMPROOT)) as td:
        work = pathlib.Path(td) / "w"
        shutil.copytree(pkg, work)
        shipped = {q.relative_to(work) for q in work.rglob("*") if q.is_file()}
        for rel, data in texts.items():
            p = work / rel
            assert p.is_file(), rel
            p.write_bytes(data)
        after = {q.relative_to(work) for q in work.rglob("*") if q.is_file()}
        assert after == shipped
        rc, passes = run_to_fixpoint(work, toplevel, tex_env(td), timeout)
        return {"rc": rc, "passes": passes,
                "first_error": first_error(work, toplevel)}


def run_paper(rank, rec, root, timeout, sample_cap):
    pkg = root / rec["arxiv_id"]
    top = rec["toplevel"]
    row = {"rank": rank, "arxiv_id": rec["arxiv_id"], "toplevel": top,
           "arms": {}}
    t0 = time.time()
    ctrl = compile_tree(pkg, top, {}, timeout)
    row["arms"]["CTRL"] = ctrl
    # --- fixer, exactly the gen tool's recipe, on a fresh copy ---
    TMPROOT.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=str(TMPROOT)) as td:
        work = pathlib.Path(td) / "w"
        shutil.copytree(pkg, work)
        O = {str(t.relative_to(work)): t.read_bytes()
             for t in sorted(work.rglob("*.tex")) if t.is_file()}
        changed = apply_fixes_tree(work, CLI, timeout)
        F = {rel: (work / rel).read_bytes() for rel in O}
    row["changed_files"] = changed
    assert set(changed) == {r for r in O if O[r] != F[r]}, "changed-set mismatch"
    # --- hunks / regions ---
    per_region = {k: {"nonws": 0, "ws": 0, "exclusive_nonws": 0} for k in REGIONS}
    tot = {"nonws": 0, "ws": 0, "coarse": 0}
    shape_by_region = {k: {} for k in REGIONS}
    withheld = []
    arm_texts = {a: {} for a in ("GUARD",) + tuple("GUARD_" + k for k in REGIONS)}
    for rel in changed:
        o, enc, hs, rows, coarse, diag = analyse_file(O[rel], F[rel])
        tot["coarse"] += coarse
        for h in rows:
            tot["ws" if h["ws"] else "nonws"] += 1
            for k in h["regions"]:
                per_region[k]["ws" if h["ws"] else "nonws"] += 1
                if not h["ws"]:
                    sh = rc_mod.shape(h["old"], h["new"])
                    shape_by_region[k][sh] = shape_by_region[k].get(sh, 0) + 1
            if not h["ws"] and len(h["regions"]) == 1:
                per_region[h["regions"][0]]["exclusive_nonws"] += 1
            if not h["ws"] and h["regions"] and len(withheld) < sample_cap:
                withheld.append({"file": rel, "s": h["s"], "e": h["e"],
                                 "regions": h["regions"],
                                 "old": h["old"][:120], "new": h["new"][:120],
                                 "ctx": o[max(0, h["s"] - 80):h["e"] + 50]})

        def arm(keys):
            return rebuild(o, hs, lambda i: rows[i]["ws"] or not any(
                k in keys for k in rows[i]["regions"])).encode(enc)
        for a in arm_texts:
            keys = REGIONS if a == "GUARD" else (a[len("GUARD_"):],)
            b = arm(keys)
            if b != F[rel]:
                arm_texts[a][rel] = b
    row["hunks"] = tot
    row["per_region"] = per_region
    row["shape_by_region"] = shape_by_region
    row["withheld_sample"] = withheld
    if ctrl["rc"] != 0:
        row["cell"] = "excluded-did-not-compile"
        row["secs"] = round(time.time() - t0, 1)
        return row
    # FULL
    full_texts = {rel: F[rel] for rel in changed}
    row["arms"]["FULL"] = (dict(ctrl, reused_from="CTRL") if not changed
                           else compile_tree(pkg, top, full_texts, timeout))
    row["cell"] = "preserved" if row["arms"]["FULL"]["rc"] == 0 else "broken"

    def guard_arm(name):
        diff = arm_texts[name]
        if not diff:
            return dict(row["arms"]["FULL"], reused_from="FULL")
        texts = dict(full_texts)
        texts.update(diff)
        if all(texts[r] == O[r] for r in texts):
            return dict(ctrl, reused_from="CTRL")
        for prev in ("GUARD",) + tuple("GUARD_" + k for k in REGIONS):
            if prev in row["arms"] and row.get("_t_" + prev) == texts:
                return dict(row["arms"][prev], reused_from=prev)
        row["_t_" + name] = texts
        return compile_tree(pkg, top, texts, timeout)
    row["arms"]["GUARD"] = guard_arm("GUARD")
    if row["cell"] == "broken":
        for k in REGIONS:
            row["arms"]["GUARD_" + k] = guard_arm("GUARD_" + k)
    for key in [k for k in row if k.startswith("_t_")]:
        del row[key]
    gok = row["arms"]["GUARD"]["rc"] == 0
    if row["cell"] == "broken":
        row["guard_effect"] = "REPAIRED" if gok else "still-broken"
    else:
        row["guard_effect"] = "preserved" if gok else "GUARD-BROKE-IT"
    row["secs"] = round(time.time() - t0, 1)
    return row


def summarise(rows):
    comp = [r for r in rows if r.get("cell") in ("preserved", "broken")]
    s = {"sampled": len(rows),
         "compiled_before": len(comp),
         "excluded": sum(r.get("cell") == "excluded-did-not-compile" for r in rows),
         "errors": sum("error" in r for r in rows),
         "full_broken": sum(r["cell"] == "broken" for r in comp),
         "guard_broken": sum(r["arms"]["GUARD"]["rc"] != 0 for r in comp),
         "guard_repaired": sum(r.get("guard_effect") == "REPAIRED" for r in comp),
         "guard_introduced_break": sum(r.get("guard_effect") == "GUARD-BROKE-IT" for r in comp)}
    for scope, rs in (("blast_compiling", comp), ("blast_all", [r for r in rows if "per_region" in r])):
        s[scope] = {k: {m: sum(r["per_region"][k][m] for r in rs)
                        for m in ("nonws", "ws", "exclusive_nonws")} for k in REGIONS}
        s[scope]["total_nonws"] = sum(r["hunks"]["nonws"] for r in rs)
        s[scope]["total_ws"] = sum(r["hunks"]["ws"] for r in rs)
        s[scope]["coarse_hunks"] = sum(r["hunks"]["coarse"] for r in rs)
        s[scope]["papers_with_any_withheld"] = sum(
            any(r["per_region"][k]["nonws"] for k in REGIONS) for r in rs)
    return s


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--corpus-root", default=os.environ.get("LP_REAL_CORPUS"))
    ap.add_argument("--offset", type=int, required=True)
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--shard", default="0/1",
                    help="k/K, 0-based: process window positions i with i %% K == k")
    ap.add_argument("--jobs", type=int, default=3, help="papers in parallel")
    ap.add_argument("--timeout", type=int, default=180)
    ap.add_argument("--sample-cap", type=int, default=300)
    ap.add_argument("--out", required=True)
    ns = ap.parse_args()
    k, K = (int(x) for x in ns.shard.split("/"))
    if not (K >= 1 and 0 <= k < K):
        sys.exit(f"FATAL: --shard {ns.shard}: need 0 <= k < K (0-based)")
    if not ns.corpus_root:
        sys.exit("FATAL: LP_REAL_CORPUS unset and no --corpus-root")
    root = pathlib.Path(ns.corpus_root)
    if not CLI.is_file():
        sys.exit(f"FATAL: {CLI} missing")
    banner = subprocess.run(["pdflatex", "--version"], capture_output=True,
                            text=True).stdout.split("\n")[0]
    if PIN not in banner:
        sys.exit(f"FATAL: engine skew {banner!r} vs {PIN!r}")
    frame = build_frame(root)
    ordered = sorted(frame, key=lambda r: hashlib.sha256(
        r["arxiv_id"].encode()).hexdigest())
    window = ordered[ns.offset:ns.offset + ns.n]
    if len(window) < ns.n:
        sys.exit(f"FATAL: frame {len(ordered)} too small for window")
    mine = [(ns.offset + i, r) for i, r in enumerate(window) if i % K == k]
    cli_sha = hashlib.sha256(CLI.read_bytes()).hexdigest()
    prov = {"frame_size": len(frame), "selection": "sha256(arxiv_id) ascending",
            "offset": ns.offset, "n": ns.n, "shard": ns.shard,
            "papers_in_shard": [r["arxiv_id"] for _, r in mine],
            "engine": banner, "cli_sha256": cli_sha,
            "src_tree_sha": subprocess.run(
                ["git", "--no-optional-locks", "rev-parse", "HEAD:latex-parse/src"],
                cwd=REPO, capture_output=True, text=True).stdout.strip(),
            "fix_scope": "gen_apply_fixes_real_differential.apply_fixes_tree",
            "caveat": CAVEAT,
            "whitespace_policy": "whitespace-only hunks kept in every arm"}
    rows = []
    outp = pathlib.Path(ns.out)

    def dump(complete):
        rows.sort(key=lambda r: r["rank"])
        outp.write_text(json.dumps({"provenance": prov, "complete": complete,
                                    "summary": summarise(rows), "rows": rows},
                                   indent=1, ensure_ascii=False) + "\n")

    harness_errors = []

    def one(item):
        rank, rec = item
        try:
            return run_paper(rank, rec, root, ns.timeout, ns.sample_cap)
        except Exception as ex:  # recorded as its own cell AND fails the run
            harness_errors.append(rec["arxiv_id"])
            return {"rank": rank, "arxiv_id": rec["arxiv_id"],
                    "cell": "harness-error", "error": repr(ex),
                    "trace": traceback.format_exc()}
    with cf.ThreadPoolExecutor(ns.jobs) as ex:
        for r in ex.map(one, mine):
            rows.append(r)
            arms = " ".join(f"{a}={v['rc']}" for a, v in r.get("arms", {}).items())
            print(f"[{r['rank']}] {r['arxiv_id']:<14} {r.get('cell')} "
                  f"{r.get('guard_effect', '')} {arms}", flush=True)
            dump(False)
    dump(True)
    s = summarise(rows)
    print(json.dumps(s, indent=1))
    print("SENTINEL_DONE", flush=True)
    if harness_errors:
        # A paper the harness could not measure is not a result; never let the
        # run look complete and clean when it was not.
        print(f"FATAL: harness error on {len(harness_errors)} paper(s): "
              f"{', '.join(harness_errors)}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
