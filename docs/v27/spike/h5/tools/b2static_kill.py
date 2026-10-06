#!/usr/bin/env python3
"""b2static_kill.py B2_ML_DIR PRE_B2_ML_DIR: kill-tests of b2static.py (spike H.5 stage 2, review
hardening). Each test copies the B2 tree, applies one mutation (every replacement asserted to
match exactly once), runs b2static.py, and checks its exit status and one line of its output.
Prints one line per test and `kill-tests: N/N` at the end; exit 0 only when every test behaves
as expected."""
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

T = Path(__file__).resolve().parent
# importable (evidence/stage2/retprobe/reverts/commands.sh uses member_revert)
B2, PRE = (Path(sys.argv[1]), Path(sys.argv[2])) if __name__ == "__main__" else (None, None)
MEMBERS = {  # member -> the successor closure's call, as extracted
    "evale": "evale_body procs strings_base ext evale evall evalargs evalx callp0 f e\n        st",
    "evall": "evall_body evale evall f l st",
    "evalargs": "evalargs_body evale evall evalargs f ks args st",
    "evalx": "evalx_body evale evall evalx f args st",
    "callp0": "callp_body procs exec f p cells st",
    "exec": "exec_body procs ext evale evall evalargs evalx callp0 exec for_loop\n        exec_list write_items f s st",
    "for_loop": "for_loop_body exec for_loop f lc c t up fe body st",
    "exec_list": "exec_list_body exec exec_list goto_in f all rest st",
    "goto_in": "goto_in_body exec exec_list goto_in f n all scan st",
    "write_items": "write_items_body evale write_items f h items nl st",
}
NAT = "(fun fO fS n -> if n=0 then fO () else fS (n-1))"


def rep(d, name, a, b):
    p = d / name
    s = p.read_text()
    c = s.count(a)
    assert c == 1, (name, a[:60], c)
    p.write_text(s.replace(a, b))


def append(d, name, text):
    p = d / name
    p.write_text(p.read_text() + "\n" + text + "\n")


def member_revert(m):
    call = MEMBERS[m]
    # the closure now reads its environment (st) after the call, so it holds the state across it,
    # as every member's did before B2. Sys.opaque_identity keeps the read: a plain `ignore st`
    # is removed by the compiler, and then nothing is held (measured: no member retained).
    return lambda d: rep(d, "Interp.ml", call + ")\n",
                         "let r__k = " + call + " in ignore (Sys.opaque_identity st); r__k)\n")


TESTS = [
    ("K00 the B2 tree, unchanged", B2, None, 0, r"^b2static: .* 0 failing$"),
    ("K01 the pre-B2 tree", PRE, None, 1, r"B2 members 0/10; 24 failing$"),
]
for m in MEMBERS:
    TESTS.append((f"K-{m}: the member {m} holds its state across its body's call", B2, member_revert(m), 1,
                  [rf"^FAIL   B2 structure: member {m}'s successor closure",
                   r"^FAIL   HOLDS Interp.ml:\d+ Interp.callp nat closure 1: state-bearing free variables \[.*st:Values.state"]))
TESTS += [
    ("K11 a second HOLDS closure under the allowed key (evale_body, Z, 0)", B2,
     lambda d: rep(d, "Interp.ml", "  | ENull -> EOk (VN, st)\n",
                   "  | ENull ->\n    ((fun fO fp fn z -> let s = Big_int_Z.sign_big_int z in\n"
                   "  if s = 0 then fO () else if s > 0 then fp z\n"
                   "  else fn (Big_int_Z.minus_big_int z))\n"
                   "      (fun _ -> match evale f e st with EOk (v, _) -> EOk (v, st) | x -> x)\n"
                   "      (fun _ -> EOk (VN, st)) (fun _ -> EOk (VN, st)) Big_int_Z.zero_big_int)\n"),
     1, r"allow \('Interp.ml', 'Interp.evale_body', 'Z', 0\): 2 HOLDS closures, the entry allows exactly 1"),
    ("K12 an ERealloc whose size expression is not ELoad (TI32, LGlob _)", B2,
     lambda d: rep(d, "Prog_7.ml", "CI32,\n    (ELoad (TPTR, (LGlob (Uint63.of_int (276))))), (ELoad (TI32, (LGlob\n    (Uint63.of_int (275)))))",
                   "CI32,\n    (ELoad (TPTR, (LGlob (Uint63.of_int (276))))), (EUnseq (ELoad (TI32, (LGlob\n    (Uint63.of_int (275))))))"),
     1, r"its check FAILED: \(b\)"),
    ("K13 evale_body's ELoad branch changed", B2,
     lambda d: rep(d, "Interp.ml", "  | ELoad (t, l) ->\n    (match evall f l st with",
                   "  | ELoad (t, l) ->\n    (match evall f l (ignore ext; st) with"),
     1, r"its check FAILED: \(c\) evale_body's ELoad branch"),
    ("K14 a new closure in Boundary holding a state across a parameter call", B2,
     lambda d: append(d, "Boundary.ml",
                      "let k14_holds (g : Values.state -> Values.state) fuel st =\n  " + NAT +
                      "\n    (fun _ -> st)\n    (fun _ -> let s2 = g st in if s2 == st then st else s2)\n    fuel"),
     1, r"^FAIL   HOLDS Boundary.ml:\d+ Boundary.k14_holds nat closure 1"),
    ("K15 Pos.iter_op instantiated at a state", B2,
     lambda d: append(d, "Boundary.ml",
                      "let k15_iter (st : Values.state) = BinPos.Pos.iter_op (fun a _ -> a) Big_int_Z.unit_big_int st"),
     1, r"BinPos.Pos.iter_op', 'positive', 0\) \(Coq library, polymorphic\): its check FAILED"),
    ("K16 a realizer text the typed half does not see (in a comment)", B2,
     lambda d: append(d, "Boundary.ml", "(* " + NAT + " *)"),
     1, r"^FAIL   coverage: Boundary.ml nat: (\d+) realizer texts, \d+ typed sites"),
    ("K17 a closure holding a state across a write loop (LOOP, passes)", B2,
     lambda d: append(d, "Boundary.ml",
                      "let k17_loop fuel cs st =\n  " + NAT +
                      "\n    (fun _ -> None)\n    (fun _ -> match Interp.put_cells cs Big_int_Z.zero_big_int Big_int_Z.zero_big_int st with"
                      " Some s2 -> Some (s2, st) | None -> None)\n    fuel"),
     0, r"^LOOP      Boundary.ml:\d+ Boundary.k17_loop nat closure 1"),
    ("K18 the boundary callback in evale_body also captures the state", B2,
     lambda d: rep(d, "Interp.ml", "| XOk (xs, st1) -> ext (fun p cs st' -> callp0 f p cs st') (zi x) xs st1",
                   "| XOk (xs, st1) -> ext (fun p cs st' -> ignore (Sys.opaque_identity st1); callp0 f p cs st') (zi x) xs st1"),
     1, r"EExt's callback to the boundary\): its check FAILED: \(a\)"),
    ("K19 a source lambda given to List.map that holds a state across a parameter call", B2,
     lambda d: append(d, "Boundary.ml",
                      "let k19_map (g : Values.state -> Values.state) st l = List.map (fun x -> (g st, x)) l"),
     1, r"^FAIL   HOLDS Boundary.ml:\d+ Boundary.k19_map lambda closure 0"),
]


def main():
    ok = 0
    for name, src, mut, want_rc, want in TESTS:
        with tempfile.TemporaryDirectory(prefix="b2kill.") as tmp:
            d = Path(tmp) / "ml"
            d.mkdir()
            for f in list(src.glob("*.ml")) + list(src.glob("*.mli")):
                shutil.copy(f, d / f.name)
            if mut:
                mut(d)
            r = subprocess.run([sys.executable, str(T / "b2static.py"), str(d)], capture_output=True, text=True)
            out = r.stdout + r.stderr
            wants = want if isinstance(want, list) else [want]
            hits = [re.search(w, out, re.M) for w in wants]
            hit = hits[-1] if all(hits) else None
            want = " AND ".join(wants)
            good = r.returncode == want_rc and hit
            ok += bool(good)
            print(f"{'ok  ' if good else 'BAD '} {name}: rc {r.returncode} (want {want_rc}); "
                  f"{'matched: ' + hit.group(0)[:160] if hit else 'NO LINE MATCHING ' + want}")
            if not good:
                print("     last lines: " + " | ".join(out.strip().splitlines()[-4:])[:600])
    print(f"kill-tests: {ok}/{len(TESTS)}")
    sys.exit(0 if ok == len(TESTS) else 1)


if __name__ == "__main__":
    main()
