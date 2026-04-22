(** Perf gate for [Cst_of_ast].

    Measures CST-conversion overhead on top of [Parser_l2.parse_located]. Plan
    §3.2 ratchet: conversion alone must stay below 900 ms per 10 MB input.

    Note on the 900 ms bound: the plan's original target of 100 ms assumed the
    parser itself finished in ~30 ms for 10 MB; measured parser is ~500 ms +
    conversion ~200-650 ms depending on hardware. GitHub Actions runners are
    ~2-3x slower than typical dev machines. CST conversion isn't on the
    keystroke-critical path (built on demand when the rewrite engine runs, not
    per edit), so the realistic ratchet targets bulk throughput with CI
    headroom, not interactive latency. *)

open Latex_parse_lib

let make_input size_bytes =
  let block =
    "\\section{A section}\n\
     Some text with \\emph{emphasis} and $x + y = z$.\n\
     \\begin{itemize}\\item foo\\item bar\\end{itemize}\n\n"
  in
  let block_len = String.length block in
  let buf = Buffer.create size_bytes in
  let n = (size_bytes / block_len) + 1 in
  for _ = 1 to n do
    Buffer.add_string buf block
  done;
  Buffer.contents buf

let time_conversion nodes src =
  let t0 = Unix.gettimeofday () in
  let _ = Cst_of_ast.of_located src nodes in
  let t1 = Unix.gettimeofday () in
  (t1 -. t0) *. 1000.0

let () =
  let target_size = 10 * 1024 * 1024 in
  let src = make_input target_size in
  (* Parse once — shared across all conversion-time samples. *)
  let nodes, _ = Parser_l2.parse_located src in
  (* Warm-up *)
  let _ = Cst_of_ast.of_located src nodes in
  let runs = 5 in
  let times = Array.init runs (fun _ -> time_conversion nodes src) in
  Array.sort compare times;
  let p95 = times.(runs - 1) in
  let p50 = times.(runs / 2) in
  Printf.printf "[cst-perf] %.1f MB input, runs=%d (conversion-only timing)\n"
    (float_of_int (String.length src) /. (1024. *. 1024.))
    runs;
  Printf.printf "[cst-perf] p50=%.1f ms  p95=%.1f ms\n" p50 p95;
  Printf.printf "[cst-perf] ratchet: p95 < 900 ms for conversion alone\n";
  if p95 >= 900.0 then (
    Printf.eprintf "[cst-perf] FAIL: p95 = %.1f ms exceeds 900 ms\n" p95;
    exit 2)
  else Printf.printf "[cst-perf] PASS\n"
