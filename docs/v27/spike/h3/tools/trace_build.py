#!/usr/bin/env python3
"""A DIAGNOSTIC build of the model that records every write into one heap block (E6).

usage: trace_build.py BUILD_OUT TRACE_DIR

BUILD_OUT is a pipeline.sh output directory (BUILD_OUT/build/ml holds the extracted OCaml and
driver.ml as compiled into ps.exe). TRACE_DIR/ml receives a copy, patched in three places
(each patch is asserted to apply exactly once), and TRACE_DIR/ps-trace.exe is linked from it:
  Values.ml   put_cell (the one function every heap write goes through) calls a hook when
              tracing is on; a stack of the procedures being executed
  Interp.ml   callp0 (every procedure call) pushes and pops that stack; tracing switches on
              when procedure PS_TRACE_ON_AFTER returns and off when PS_TRACE_OFF_AT is entered
              (-1: never)
  driver.ml   with PS_TRACE=FILE, writes one line per write into a block of PS_TRACE_BSIZE
              cells: sequence number, block, block size, cell offset, the cell (W BITS MASK
              for a memory word, BITS its 64-bit little-endian value), and the innermost eight
              procedures (innermost first)
Nothing else changes: the program's semantics are the extracted program's. It is NOT the
measured ps.exe and backs no measurement but the write record; a run of it must still write
the same outputs as ps.exe (fmtexplain.py's evidence states the check).
Run (H.3's round trip; procedure numbers are lines of BUILD_OUT/procnames.txt, from 0):
  PS_TRACE=trace.txt PS_TRACE_ON_AFTER=596 PS_TRACE_OFF_AT=-1 PS_TRACE_BSIZE=5000001 \\
  PS_PROCNAMES=BUILD_OUT/procnames.txt PS_DUMPDIR=DIR ps-trace.exe 4000000000 SPEC STDIN"""
import os
import shutil
import subprocess
import sys
from pathlib import Path

src, dst = Path(sys.argv[1]) / "build" / "ml", Path(sys.argv[2])
ml = dst / "ml"
if ml.exists():
    shutil.rmtree(ml)
ml.mkdir(parents=True)
for f in src.iterdir():
    if f.suffix in (".ml", ".mli"):
        shutil.copy(f, ml / f.name)


def patch(name, old, new):
    p = ml / name
    s = p.read_text()
    assert s.count(old) == 1, (name, old[:60], s.count(old))
    p.write_text(s.replace(old, new))


patch("Values.ml", "let put_cell st b o c =\n", """let trace_on = ref false
let trace_fn : (state -> Big_int_Z.big_int -> Big_int_Z.big_int -> cell -> unit) ref = ref (fun _ _ _ _ -> ())
let pstack : int list ref = ref []
let trace_on_after = ref (-1)
let trace_off_at = ref (-1)

let put_cell st b o c =
  if !trace_on then !trace_fn st b o c;
""")
(ml / "Values.mli").write_text((ml / "Values.mli").read_text() + """
val trace_on : bool ref
val trace_fn : (state -> Big_int_Z.big_int -> Big_int_Z.big_int -> cell -> unit) ref
val pstack : int list ref
val trace_on_after : int ref
val trace_off_at : int ref
""")
patch("Interp.ml", "  and callp0 fuel p cells st =\n", """  and callp0 fuel p cells st =
    let pi = Big_int_Z.int_of_big_int p in
    if pi = !trace_off_at then trace_on := false;
    pstack := pi :: !pstack;
    let r__ = callp0_body fuel p cells st in
    pstack := Stdlib.List.tl !pstack;
    if pi = !trace_on_after then trace_on := true;
    r__
  and callp0_body fuel p cells st =
""")
patch("driver.ml", "  let t0 = Unix.gettimeofday () in\n", '''  (match Sys.getenv_opt "PS_TRACE" with
   | Some f ->
     let oc = open_out f in
     at_exit (fun () -> close_out oc);
     let names = (let ic = open_in (Sys.getenv "PS_PROCNAMES") in
       let rec go acc = match input_line ic with l -> go (l :: acc) | exception End_of_file -> Stdlib.List.rev acc in
       Stdlib.Array.of_list (go [])) in
     Values.trace_on_after := int_of_string (Sys.getenv "PS_TRACE_ON_AFTER");
     Values.trace_off_at := int_of_string (Sys.getenv "PS_TRACE_OFF_AT");
     let bsz = Big_int_Z.big_int_of_string (Sys.getenv "PS_TRACE_BSIZE") in
     let seq = ref 0 in
     let rec take n l = match n, l with 0, _ | _, [] -> [] | n, x :: r -> x :: take (n - 1) r in
     Values.trace_fn := (fun st b o c ->
       let blk = Values.hget st b in
       if Big_int_Z.eq_big_int blk.Values.bsize bsz then begin
         incr seq;
         let cs = match c with
           | Values.KWord (bits, m) -> Printf.sprintf "W %s %s" (Z.format "%x" bits) (Z.format "%x" m)
           | Values.KInt v -> "I " ^ Z.to_string v
           | Values.KUndef -> "U" | _ -> "O" in
         let chain = Stdlib.String.concat "<" (Stdlib.List.map (fun p -> names.(p)) (take 8 !Values.pstack)) in
         Printf.fprintf oc "%d %s %s %s %s %s\\n" !seq (Z.to_string b) (Z.to_string blk.Values.bsize)
           (Z.to_string o) cs chain end)
   | None -> ());
  let t0 = Unix.gettimeofday () in
''')
pk = ["-package", "zarith,coq-core.kernel,unix"]
os.chdir(ml)
order = subprocess.run(["ocamlfind", "ocamldep", "-sort"] + sorted(p.name for p in ml.iterdir()),
                       capture_output=True, text=True, check=True).stdout.split()
for f in order:
    subprocess.run(["ocamlfind", "ocamlopt"] + pk + ["-c", f], check=True)
subprocess.run(["ocamlfind", "ocamlopt"] + pk + ["-linkpkg"] + [f[:-3] + ".cmx" for f in order if f.endswith(".ml")]
               + ["-o", str(dst / "ps-trace.exe")], check=True)
print("linked", dst / "ps-trace.exe")
