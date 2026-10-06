#!/usr/bin/env python3
"""b2static.py ML_DIR: the static half of B2's standing retention check (spike H.5 stage 2).

Coq's extraction realizes a `match` on nat (ExtrOcamlNatInt), Z, N and positive
(ExtrOcamlZBigInt) and ascii (ExtrOcamlChar) as a function applied to one heap closure per
branch, e.g. for the fuel

    (fun fO fS n -> if n=0 then fO () else fS (n-1)) (fun _ -> A) (fun f -> B) N

If a branch closure makes a call and reads its environment after the call returns, everything
the environment holds stays alive during the call. If that is a state, and the call updates
persistent arrays, the state's old versions keep every later update alive (H5-heap-design.md
§2.2: 211 M words before B2). This check covers EVERY such closure in the extracted tree:

1. Typed (b2cmt.ml on the tree's .cmt files). Each continuation closure of each realizer use is
   DEAD (the closure's environment is dead during every call that can re-enter the interpreter
   or loop over writes: the call is in tail position, or nothing after it reads a free variable),
   STATEFREE (no free variable's type can reach a state), LOOP (it may hold a state across a
   data-bounded write loop only, and retains at most that loop's writes until it returns) or
   HOLDS (it may hold a state across a call that can re-enter the interpreter). b2cmt.ml's
   header defines the four exactly. DEAD, STATEFREE and LOOP pass. Every `fun` of the source
   passed as an argument (kind `lambda`) is classified the same way, and also against its callee.
2. Coverage. The realizer texts are read from the installed Coq's extraction library; the
   number of textual occurrences of each, per file, must equal the number of typed sites b2cmt
   found there. A realizer text this script does not know, found in the tree, FAILS.
3. B2's structure. Interp.callp must contain exactly the ten fuelled members, each one nat
   realizer whose successor closure is a single application on identifiers of NAME_body,
   classified DEAD.
4. Every HOLDS closure must be covered by an ALLOW entry keyed by (file, top-level function,
   realizer, closure index), whose COUNT must equal the number of HOLDS closures under that key
   (a second site in an allowed function fails), and whose CHECK, a function of this file, must
   pass on the tree: the argument for the entry is checked, not only stated.

Exit 0 when everything passes, 1 on any failure, 2 when the check could not run."""
import re
import shutil
import subprocess
import sys
import tempfile
from collections import Counter, defaultdict
from pathlib import Path

T = Path(__file__).resolve().parent
KINDS = {  # parameter names of the realizer's own `fun` -> (kind, number of continuations)
    ("fO", "fS", "n"): ("nat", 2),
    ("fO", "fp", "fn", "z"): ("Z", 3),
    ("fO", "fp", "n"): ("N", 2),
    ("f2p1", "f2p", "f1", "p"): ("positive", 3),
    ("f", "c"): ("ascii", 1),
}
MEMBERS = ["evale", "evall", "evalargs", "evalx", "callp0", "exec", "for_loop", "exec_list",
           "goto_in", "write_items"]
IDENT = r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
OCAML_ENV = "export PATH=$HOME/.opam/l0-testing/bin:$PATH; eval $(opam env --switch=l0-testing 2>/dev/null); "
PKGS = "zarith,coq-core.kernel,unix"


def sh(cmd, cwd):
    r = subprocess.run(["zsh", "-c", OCAML_ENV + cmd], cwd=cwd, capture_output=True, text=True)
    return r.returncode, r.stdout, r.stderr


def realizer_texts():
    """every `Extract Inductive` of Coq's OCaml extraction library that has a match realizer"""
    rc, out, err = sh("coqc -where", ".")
    assert rc == 0, err
    d = Path(out.strip()) / "theories" / "extraction"
    found = {}
    for f in sorted(d.glob("Extr*.v")):
        if "Haskell" in f.name or "Scheme" in f.name:
            continue
        s = f.read_text()
        for m in re.finditer(r"Extract\s+Inductive\s+(\S+)\s*=>.*?\]\s*\"((?:[^\"]|\"\")*)\"\s*\.", s, re.S):
            text = m.group(2)
            if text.lstrip().startswith("(") or "fun" in text:
                found.setdefault(text, []).append(f"{f.name}:{m.group(1)}")
    return found


def text_params(text):
    m = re.search(r"\(fun\s+((?:[A-Za-z0-9_']+\s+)+)->", text)
    return tuple(m.group(1).split()) if m else None


# ------------------------------------------------------------------ checked arguments
def check_instances(ctx, key):
    """a polymorphic library function: every use outside its own definition instantiates its
    type variables at state-free types and passes only global functions as arguments, so the
    values its closures hold are never states"""
    top = key[1]
    uses = [u for u in ctx["uses"] if u[0] == top]
    bad = [u for u in uses if u[2] != "state-free global-function-arguments"]
    return (not bad, f"{len(uses)} uses, all state-free with global function arguments"
            if not bad else f"uses not state-free: {bad}")


def norm(s):
    return " ".join(s.split())


ELOAD_BRANCH = norm("""
  | ELoad (t, l) ->
    (match evall f l st with
     | LOk (lc, st1) ->
       (match read_loc st1 t lc with
        | LdOk v -> EOk (v, st1)
        | LdStuck s -> EStk (s, st1))
     | LHalt (c, st1) -> EHalt (c, st1)
     | LStk (s, st1) -> EStk (s, st1))""")
LGLOB_BRANCH = norm("""
  | LGlob g ->
    LOk ({ lb = (zi g); lo = Big_int_Z.zero_big_int; coq_lsl = None }, st)""")
EREALLOC_SIZE = re.compile(r"\(ELoad\s*\(TI32,\s*\(LGlob\s*\(Uint63\.of_int\s*\(\d+\)\)\)\)\)")


def branch(src, header):
    """the text of the match case starting with `header` (at two spaces' indent) up to the
    next case at the same indent"""
    i = src.find("\n" + header)
    if i < 0 or src.count("\n" + header) != 1:
        return None
    j = src.find("\n  | ", i + 1)
    return src[i:j if j > 0 else len(src)]


def check_erealloc(ctx, key):
    """ERealloc's zero-offset branch holds st1 across `evale f n st1`. That call evaluates the
    size expression n. (Its other non-tail calls, copy_cells and new_block, are LOOP calls:
    bounded by the cells copied, see b2cmt.ml.) Checked here: (a) the only non-tail RUN call
    the closure makes is that one;
    (b) every ERealloc of the program has n = ELoad (TI32, LGlob _); (c) evaluating such an n
    is evall on an LGlob (no call at all) and read_loc, which is write-free: no Parray.set
    happens while st1 is held, so it retains nothing that the current state does not."""
    d = ctx["dir"]
    hold = [s for s in ctx["holds"] if (s["file"], s["top"], s["kind"], s["i"]) == key]
    calls = sorted({c.strip() for s in hold for c in
                    re.search(r"across non-tail calls \[(.*)\]$", s["detail"]).group(1).split(";")})
    runs = [c for c in calls if c.startswith("RUN ")]
    if runs != ["RUN evale (a local function or parameter)"]:
        return False, f"(a) the closure's non-tail RUN calls are {runs}, not only evale"
    interp = (d / "Interp.ml").read_text()
    er = branch(interp, "  | ERealloc (esz, _, p, n) ->")
    if er is None or er.count("evale f n st1") != 1:
        return False, "(a) ERealloc's branch does not bind n or call `evale f n st1` exactly once"
    sites, bad = 0, []
    for f in sorted(d.glob("*.ml")):
        if f.name in ("Interp.ml", "Syntax.ml"):
            continue
        s = f.read_text()
        for m in re.finditer(r"\bERealloc\b", s):
            sites += 1
            # ERealloc (Uint63, ct, expr, expr): skip to the 4th component
            i = s.index("(", m.end())
            depth, k, commas = 0, i, []
            while True:
                c = s[k]
                if c == "(":
                    depth += 1
                elif c == ")":
                    depth -= 1
                    if depth == 0:
                        break
                elif c == "," and depth == 1:
                    commas.append(k)
                k += 1
            if len(commas) != 3:
                bad.append(f"{f.name}:{s.count(chr(10), 0, m.start()) + 1} (not 4 components)")
                continue
            fourth = s[commas[2] + 1:k].strip()
            if not EREALLOC_SIZE.fullmatch(fourth):
                bad.append(f"{f.name}:{s.count(chr(10), 0, m.start()) + 1}: {norm(fourth)[:60]}")
    if sites == 0 or bad:
        return False, f"(b) {sites} ERealloc in the program; size expressions that are not ELoad (TI32, LGlob _): {bad}"
    if norm(branch(interp, "  | ELoad (t, l) ->") or "") != ELOAD_BRANCH:
        return False, "(c) evale_body's ELoad branch is not the one this argument was made for"
    if norm(branch(interp, "  | LGlob g ->") or "") != LGLOB_BRANCH:
        return False, "(c) evall_body's LGlob branch is not the one this argument was made for"
    if ctx["callgraph"].get("Interp.read_loc") != "leaf (write-free)":
        return False, f"(c) Interp.read_loc is {ctx['callgraph'].get('Interp.read_loc')}"
    return True, (f"the only RUN call held is evale on the size expression; {sites} ERealloc sites, every size "
                  "expression ELoad (TI32, LGlob _); the ELoad and LGlob branches as pinned; read_loc write-free")


def check_callback(ctx, key):
    """The interpreter's callback to the C boundary, `ext (fun p cs st' -> callp0 f p cs st') ...`
    in evale_body (EExt) and exec_body (SExt): Boundary.ext may keep it while it runs. Its
    environment is (callp0, f), which the types cannot clear: callp0 is a function and f has a
    type variable (the bodies are polymorphic in the fuel). Checked here: (a) its free variables
    are exactly those two; (b) the bodies are applied only by Interp.callp's members, with callp0
    and f identifiers (B2's structure, checked above: f is the successor closure's fuel, an int,
    and callp0 is a member of callp's `let rec`, whose environment is callp's parameters);
    (c) callp is applied once, in Main0, to the program's constants
    (`callp procs_array nglobals ext fuel`). So the callback holds no state."""
    d = ctx["dir"]
    hold = [s for s in ctx["holds"] if (s["file"], s["top"], s["kind"], s["i"]) == key]
    fv = sorted({m for s in hold for m in re.findall(r"(\w+):", re.search(r"free variables \[(.*?)\]", s["detail"]).group(1))})
    if fv != ["callp0", "f"]:
        return False, f"(a) the closure's free variables are {fv}, not callp0 and f"
    if ctx["struct_ok"] != 10:
        return False, "(b) B2's structure does not hold, so callp0 and f are not known to be the members' own"
    interp = (d / "Interp.ml").read_text()
    if interp.count("\nlet callp procs strings_base ext =\n  let rec evale fuel e st =") != 1:
        return False, "(b) Interp.callp is not the `let rec` of the members over (procs, strings_base, ext)"
    uses = [u for u in ctx["uses"] if u[0] == key[1]]
    if len(uses) != 1 or not uses[0][1].startswith("Interp.ml:"):
        return False, f"(b) {key[1]} is used {len(uses)} times outside its definition ({uses}), not once, by its member"
    main0 = (d / "Main0.ml").read_text()
    if len(re.findall(r"\bcallp\b", main0)) != 1 or main0.count("callp procs_array nglobals ext fuel") != 1:
        return False, "(c) Main0 does not apply callp exactly once, to procs_array nglobals ext fuel"
    return True, "free variables callp0 and f only; the bodies applied only by callp's members; callp applied once, in Main0, to constants"


# (file, top-level function, realizer, closure index) -> (count, reason, check)
ALLOW = {
    ("BinPos.ml", "BinPos.Pos.iter", "positive", 0): (1, "Coq library, polymorphic", check_instances),
    ("BinPos.ml", "BinPos.Pos.iter", "positive", 1): (1, "Coq library, polymorphic", check_instances),
    ("BinPos.ml", "BinPos.Pos.iter_op", "positive", 0): (1, "Coq library, polymorphic", check_instances),
    ("BinPos.ml", "BinPos.Pos.iter_op", "positive", 1): (1, "Coq library, polymorphic", check_instances),
    ("Interp.ml", "Interp.evale_body", "Z", 0): (1, "ERealloc: the size expression calls nothing", check_erealloc),
    ("Interp.ml", "Interp.evale_body", "lambda", 0): (1, "EExt's callback to the boundary", check_callback),
    ("Interp.ml", "Interp.exec_body", "lambda", 0): (1, "SExt's callback to the boundary", check_callback),
}


def main():
    d = Path(sys.argv[1]).resolve()
    fails = []
    texts = realizer_texts()
    known = {t: KINDS.get(text_params(t)) for t in texts}
    textual = Counter()
    for f in sorted(d.glob("*.ml")):
        s = f.read_text()
        for t, k in known.items():
            n = s.count(t)
            if n and k is None:
                fails.append(f"{f.name}: {n} uses of a realizer this check does not know ({texts[t]})")
            elif n:
                textual[(f.name, k[0])] += n
    # typed half: .cmt files of a copy of the tree, and b2cmt.exe
    with tempfile.TemporaryDirectory(prefix="b2static.") as tmp:
        w = Path(tmp)
        for f in list(d.glob("*.ml")) + list(d.glob("*.mli")):
            shutil.copy(f, w / f.name)
        shutil.copy(T / "b2cmt.ml", w / "b2cmt_tool.ml")
        rc, out, err = sh(f"ocamlfind ocamlopt -package compiler-libs.common -linkpkg b2cmt_tool.ml -o b2cmt.exe", w)
        if rc:
            print(err)
            print("b2static: COULD NOT RUN (b2cmt.ml did not compile)")
            sys.exit(2)
        for p in w.glob("b2cmt_tool.*"):
            p.unlink()
        rc, out, err = sh(f"for f in $(ocamlfind ocamldep -sort *.mli); do ocamlfind ocamlc -package {PKGS} -c $f || exit 1; done", w)
        if rc:
            print(err)
            print("b2static: COULD NOT RUN (an .mli did not compile)")
            sys.exit(2)
        rc, out, err = sh(f"for f in *.ml; do ocamlfind ocamlc -bin-annot -stop-after typing -w -a -package {PKGS} -c $f || exit 1; done", w)
        if rc:
            print(err)
            print("b2static: COULD NOT RUN (an .ml did not type)")
            sys.exit(2)
        rc, out, err = sh("ocamlfind ocamldep -modules *.ml", w)
        deps = {}
        for line in out.splitlines():
            f, rest = line.split(":", 1)
            deps[f.strip()[:-3]] = rest.split()
        tree = set(deps)

        def tdeps(m, seen):
            for x in deps.get(m, []):
                if x in tree and x not in seen:
                    seen.add(x)
                    tdeps(x, seen)
            return seen
        pure = sorted(m for m in tree if m != "Values" and "Values" not in tdeps(m, set()))
        cmts = " ".join(sorted(p.name for p in w.glob("*.cmt")))
        rc, out, err = sh(f"./b2cmt.exe {','.join(pure)} {','.join(sorted(tree))} {cmts}", w)
        if rc:
            print(err)
            print("b2static: COULD NOT RUN (b2cmt.exe failed)")
            sys.exit(2)
    sites, callgraph, uses = [], {}, []
    for line in out.splitlines():
        p = line.split(" ", 8)
        if p[0] == "SITE":
            sites.append(dict(file=p[1], line=int(p[2]), col=int(p[3]), kind=p[4], top=p[5], i=int(p[6]),
                              verdict=p[7], detail=p[8] if len(p) > 8 else ""))
        elif p[0] == "CALLGRAPH":
            callgraph[p[1]] = line.split(" ", 2)[2]
        elif p[0] == "USE":
            q = line.split(" ", 3)
            uses.append((q[1], q[2], q[3]))
    # 2. coverage
    typed = Counter()
    for (f, ln, col, k), group in _group_sites(sites).items():
        if k != "lambda":
            typed[(f, k)] += 1
    for key in sorted(set(textual) | set(typed)):
        if textual[key] != typed[key]:
            fails.append(f"coverage: {key[0]} {key[1]}: {textual[key]} realizer texts, {typed[key]} typed sites")
    # 3. B2's structure
    interp = (d / "Interp.ml").read_text() if (d / "Interp.ml").exists() else ""
    members = [s for s in sites if s["file"] == "Interp.ml" and s["top"] == "Interp.callp" and s["kind"] == "nat"]
    succ = [s for s in members if s["i"] == 1]
    struct_ok = 0
    for m in MEMBERS:
        pat = (r"\n  (?:let rec|and) " + m + r" fuel[^\n]*=\n\s*\(fun fO fS n -> if n=0 then fO \(\) else fS \(n-1\)\)"
               r"\n\s*\(fun _ -> [^\n]*\)\n\s*\(fun f ->\s*(" + m.rstrip("0") + r"_body(?:\s+" + IDENT + r")*)\)\n\s*fuel\n")
        mm = re.search(pat, interp)
        if mm and len(re.findall(r"\n  (?:let rec|and) " + m + r" fuel", interp)) == 1:
            struct_ok += 1
        else:
            fails.append(f"B2 structure: member {m}'s successor closure is not a single call of {m.rstrip('0')}_body on identifiers")
    if len(succ) != 10 or any(s["verdict"] != "DEAD" for s in members):
        fails.append(f"B2 structure: Interp.callp's {len(succ)} fuel realizers (10 expected) must all be DEAD; "
                     f"verdicts of their closures: {dict(Counter(s['verdict'] for s in members))}")
    # 4. HOLDS closures and the allow list
    holds = [s for s in sites if s["verdict"] == "HOLDS"]
    ctx = dict(dir=d, holds=holds, callgraph=callgraph, uses=uses, struct_ok=struct_ok)
    by_key = Counter((s["file"], s["top"], s["kind"], s["i"]) for s in holds)
    n_allowed = 0
    for key in sorted(by_key):
        if key not in ALLOW:
            for s in holds:
                if (s["file"], s["top"], s["kind"], s["i"]) == key:
                    fails.append(f"HOLDS {s['file']}:{s['line']} {s['top']} {s['kind']} closure {s['i']}: {s['detail']}")
            continue
        count, reason, check = ALLOW[key]
        if by_key[key] != count:
            fails.append(f"allow {key}: {by_key[key]} HOLDS closures, the entry allows exactly {count}")
            continue
        ok, why = check(ctx, key)
        if not ok:
            fails.append(f"allow {key} ({reason}): its check FAILED: {why}")
        else:
            n_allowed += by_key[key]
            print(f"allow  {key[0]} {key[1]} {key[2]} closure {key[3]} x{count}: {reason}; checked: {why}")
    for key in sorted(set(ALLOW) - set(by_key)):
        print(f"note   allow entry {key} matches no HOLDS closure")
    v = Counter(s["verdict"] for s in sites if s["kind"] != "lambda")
    vl = Counter(s["verdict"] for s in sites if s["kind"] == "lambda")
    for s in sites:
        if s["file"] == "Interp.ml" or s["verdict"] != "DEAD":
            print(f"{s['verdict']:9} {s['file']}:{s['line']} {s['top']} {s['kind']} closure {s['i']} {s['detail'][:300]}")
    for f in fails:
        print("FAIL   " + f)
    nsites = len([k for k in _group_sites(sites) if k[3] != "lambda"])
    nl = sum(vl.values())
    print(f"b2static: {sum(v.values())} closures at {nsites} realizer sites: {v['DEAD']} DEAD, {v['STATEFREE']} STATEFREE, "
          f"{v['LOOP']} LOOP, {v['HOLDS']} HOLDS; {nl} source lambdas passed as arguments: {vl['DEAD']} DEAD, "
          f"{vl['STATEFREE']} STATEFREE, {vl['LOOP']} LOOP, {vl['HOLDS']} HOLDS; {n_allowed} HOLDS allowed by a checked argument; "
          f"B2 members {struct_ok}/10; "
          f"{len(fails)} failing")
    sys.exit(1 if fails else 0)


def _group_sites(sites):
    g = defaultdict(list)
    for s in sites:
        g[(s["file"], s["line"], s["col"], s["kind"])].append(s)
    return g


if __name__ == "__main__":
    main()
