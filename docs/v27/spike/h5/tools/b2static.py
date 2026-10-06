#!/usr/bin/env python3
"""b2static.py ML_DIR: the static half of B2's standing check (spike H.5 stage 2).

Every use of ExtrOcamlNatInt's realizer of `match` on a nat in the extracted tree,

    (fun fO fS n -> if n=0 then fO () else fS (n-1)) (fun _ -> A) (fun f -> B) N

makes B a heap closure. If B makes a non-tail call and then reads its environment, whatever the
environment holds (a state, before B2) stays alive for the whole call (H5-heap-design.md §2.2).
A site passes when B is a single application whose function and arguments are all plain
identifiers (B2's NAME_body call: the closure's environment is dead once the call starts).
Any other site must be listed in ALLOW below with the reason it cannot retain a state; a new
site of any other shape FAILS. The dynamic half is retention_probe.sh.
Exit 0 when every site passes or is allowed, 1 otherwise."""
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from b2sim import REAL, group_end, skip_ws  # noqa: E402

# (file, enclosing function) -> why its successor closure cannot hold a state across a call
ALLOW = {
    ("Interp.ml", "copy_cells"): "tail-recursive: B's only call after put_cell is the tail call",
    ("Interp.ml", "read_cells"): "reads one state, writes none: the state held is the current one",
    ("Interp.ml", "digits_rev"): "no state",
    ("Interp.ml", "cstring"): "reads one state, writes none: the state held is the current one",
    ("Boundary.ml", "c_strtoull10"): "no state (take_digits' result)",
    ("Boundary.ml", "c_atoi"): "no state (take_digits' result)",
    ("Boundary.ml", "read_into"): "tail-recursive: B's only call after put_cell is the tail call",
    ("Boundary.ml", "trim_spaces"): "tail-recursive, reads one state",
    ("Boundary.ml", "map_xord"): "tail-recursive: B's only call after put_cell is the tail call",
    ("Boundary.ml", "dec_digits"): "no state",
    ("Boundary.ml", "be_bytes"): "no state",
    ("Boundary.ml", "take"): "no state",
    ("Boundary.ml", "undump_cells"): "no state",
    ("Boundary.ml", "parse_tounicode"): "no state",
    ("Values.ml", "fill_chunks"): "no state (builds one block, tail-recursive)",
    ("Main0.ml", "fill_run"): "no state (builds one block, tail-recursive)",
    ("List.ml", "nth"): "Coq library, no state",
    ("Nat.ml", "tail_add"): "Coq library, no state",
    ("Nat.ml", "tail_addmul"): "Coq library, no state",
    ("BinPos.ml", "of_succ_nat"): "Coq library, no state",
    ("BinInt.ml", "of_nat"): "Coq library, no state",
    ("Uint0.ml", "to_Z_rec"): "Coq library, no state",
    ("Uint0.ml", "of_pos_rec"): "Coq library, no state",
}
IDENT = r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"


def enclosing(s, k):
    """the name of the nearest `let [rec] NAME` or `and NAME` before offset k"""
    m = None
    for m in re.finditer(r"(?m)^\s*(?:let(?: rec)?|and)\s+([a-z_][A-Za-z0-9_']*)", s[:k]):
        pass
    return m.group(1) if m else "?"


def sites(s):
    pos = 0
    while True:
        k = s.find(REAL, pos)
        if k < 0:
            return
        i = skip_ws(s, k + len(REAL))
        j0 = group_end(s, i)              # (fun _ -> A)
        i = skip_ws(s, j0)
        j1 = group_end(s, i)              # (fun f -> B)
        m = re.match(r"\(fun\s+(" + IDENT + r")\s*->\s*", s[i:j1])
        assert m, s[i:i + 80]
        yield k, m.group(1), s[i + m.end():j1 - 1].strip()
        pos = k + len(REAL)


def main():
    d = Path(sys.argv[1])
    bad, n_ok, n_allow, seen = [], 0, 0, set()
    for f in sorted(d.glob("*.ml")):
        s = f.read_text()
        for k, var, body in sites(s):
            fn = enclosing(s, k)
            if re.fullmatch(rf"{IDENT}(?:\s+{IDENT})*", body):
                n_ok += 1
                print(f"ok     {f.name} {fn}: fun {var} -> {body[:90]}")
            elif (f.name, fn) in ALLOW:
                n_allow += 1
                seen.add((f.name, fn))
                print(f"allow  {f.name} {fn}: {ALLOW[(f.name, fn)]}")
            else:
                bad.append(f"{f.name} {fn}")
                print(f"FAIL   {f.name} {fn}: the successor closure is not a single call on identifiers")
    for f, fn in sorted(set(ALLOW) - seen):
        print(f"note   allowed site {f} {fn} not present")
    print(f"b2static: {n_ok} single-call sites, {n_allow} allowed sites, {len(bad)} failing")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
