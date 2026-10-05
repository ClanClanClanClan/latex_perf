#!/usr/bin/env python3
"""mkvariant.py ML_DIR OUT_DIR {prof|t1}: a PROFILING variant of an extracted PS tree (spike H.5
stage 1). Never a model build: these trees exist to measure where memory and time go.

prof: coq-core's Parray replaced by parrayc.ml (the same algorithm with counters, and
      PS_PARRAY=linear: in-place, fail-closed on a superseded version), and prof.ml's GC probe
      wrapped around the C boundary (PS_PROBE, PS_PROBE_DEEP).
t1:   prof, plus O(1) realizers of Uint63.to_Z, Uint63.of_Z and Sint63.to_Z (zr.ml), the
      extracted Coq definitions kept as *_coq; PS_T1CHECK=1 compares every call.
Every textual replacement is asserted to match exactly the expected number of times."""
import shutil, sys
from pathlib import Path

src, out, kind = Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3]
tools = Path(__file__).resolve().parent
if out.exists():
    shutil.rmtree(out)
out.mkdir(parents=True)
for f in src.iterdir():
    if f.suffix in (".ml", ".mli"):
        shutil.copy(f, out / f.name)
shutil.copy(tools / "parrayc.ml", out / "parrayc.ml")
shutil.copy(tools / "prof.ml", out / "prof.ml")


def rep(name, a, b, n=1):
    p = out / name
    s = p.read_text()
    c = s.count(a)
    assert c == n, (name, a[:60], c)
    p.write_text(s.replace(a, b))


rep("PArray0.ml", "Parray.", "Parrayc.", 4)
rep("PArray0.mli", "Parray.t", "Parrayc.t", 1)
rep("Main0.ml", "callp procs_array nglobals ext fuel", "callp procs_array nglobals Prof.ext fuel")
rep("driver.ml", "  let t0 = Unix.gettimeofday () in\n",
    "  if Prof.deep then Prof.static_words := Obj.reachable_words (Obj.repr Main0.procs_array);\n"
    "  let t0 = Unix.gettimeofday () in\n")
rep("driver.ml", '  Printf.printf "TIME: %.2f s\\n" (t1 -. t0)',
    "  (let st = match r with Interp.EOk (_, s) | Interp.EHalt (_, s) | Interp.EStk (_, s) -> s in Prof.probe st);\n"
    '  prerr_endline ("PARRAYC " ^ Parrayc.counters ());\n'
    '  Printf.printf "TIME: %.2f s\\n" (t1 -. t0)')
if kind in ("t1", "t2"):
    shutil.copy(tools / "zr.ml", out / "zr.ml")
    hdr = ("\n(* PROFILING EXPERIMENT (spike H.5 stage 1), not a model build: O(1) realizers of the\n"
           "   Coq library conversions; PS_T1CHECK=1 compares each result with the extracted Coq code *)\n"
           'let t1check = Sys.getenv_opt "PS_T1CHECK" <> None\n'
           'let t1fail what = prerr_endline ("T1CHECK mismatch in " ^ what); exit 5\n')
    rep("Uint0.ml", "let to_Z =\n  to_Z_rec size\n",
        hdr + "let to_Z_coq =\n  to_Z_rec size\nlet to_Z i =\n  let r = Zr.u63_to_z i in\n"
        '  if t1check && not (Zr.eq r (to_Z_coq i)) then t1fail "Uint63.to_Z"; r\n')
    rep("Uint0.ml", "let of_Z z =\n", "let of_Z_coq z =\n")
    p = out / "Uint0.ml"
    p.write_text(p.read_text() + "\nlet of_Z z =\n  let r = Zr.z_to_u63 z in\n"
                 '  if t1check && not (Uint63.equal r (of_Z_coq z)) then t1fail "Uint63.of_Z"; r\n')
    rep("Sint0.ml", "let to_Z i =\n", "let to_Z_coq i =\n")
    rep("Sint0.ml", "  if ltb i min_int then to_Z i else Z.opp (to_Z (opp i))",
        "  if ltb i min_int then Uint0.to_Z_coq i else Z.opp (Uint0.to_Z_coq (opp i))")
    p = out / "Sint0.ml"
    p.write_text(p.read_text() + "\nlet to_Z i =\n  let r = Zr.s63_to_z i in\n"
                 '  if Uint0.t1check && not (Zr.eq r (to_Z_coq i)) then Uint0.t1fail "Sint63.to_Z"; r\n')
    rep("Uint0.mli", "val to_Z : Uint63.t -> Big_int_Z.big_int\n",
        "val to_Z : Uint63.t -> Big_int_Z.big_int\nval to_Z_coq : Uint63.t -> Big_int_Z.big_int\n"
        "val of_Z_coq : Big_int_Z.big_int -> Uint63.t\nval t1check : bool\nval t1fail : string -> unit\n")
    rep("Sint0.mli", "val to_Z : Uint63.t -> Big_int_Z.big_int\n",
        "val to_Z : Uint63.t -> Big_int_Z.big_int\nval to_Z_coq : Uint63.t -> Big_int_Z.big_int\n")
elif kind != "prof":
    sys.exit("kind is prof, t1 or t2")
if kind == "t2":
    # inside BinInt.ml's module Z: rename the extracted definition, then add the realizer
    # (checked against it under PS_T1CHECK) just before the next definition
    b = out / "BinInt.ml"
    s = b.read_text()
    for name, args, impl, eq in [
            ("coq_land", "a b", "Zr.land_ a b", "Zr.eq"), ("coq_lor", "a b", "Zr.lor_ a b", "Zr.eq"),
            ("coq_lxor", "a b", "Zr.lxor_ a b", "Zr.eq"), ("testbit", "a n", "Zr.testbit a n", "Zr.eqb"),
            ("quotrem", "a b", "Zr.quotrem a b", "(fun x y -> Zr.eqp x y)"), ("of_nat", "n", "Zr.of_nat n", "Zr.eq")]:
        head = f"  let {name} {args} =\n"
        assert s.count(head) == 1, name
        i = s.index(head)
        j = s.index("\n  (** val ", i)
        new = (f"\n  let {name} {args} =\n    let r = {impl} in\n"
               f"    if Zr.check && not ({eq} r ({name}_coq {args})) then Zr.fail \"Z.{name}\"; r\n")
        s = s[:i] + f"  let {name}_coq {args} =\n" + s[i + len(head):j] + new + s[j:]
    b.write_text(s)
print(f"variant {kind}: {out}")
