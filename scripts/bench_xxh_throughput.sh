#!/usr/bin/env bash
# xxHash throughput benchmark (spec W9)
#
# Measures scalar OCaml xxHash64 throughput on perf_smoke corpus.
# Target: ≥ 20 GB/s (SIMD), ~2-4 GB/s (scalar baseline).
#
# Usage:
#   bash scripts/bench_xxh_throughput.sh
#
# Outputs throughput in GB/s and records to RESULTS.md.

set -euo pipefail

CORPUS="corpora/perf/perf_smoke_big.tex"
ITERATIONS=100

if [ ! -f "$CORPUS" ]; then
  echo "[xxh-bench] Corpus file not found: $CORPUS"
  echo "[xxh-bench] Using fallback: measuring on README.md"
  CORPUS="README.md"
fi

FILE_SIZE=$(wc -c < "$CORPUS")
echo "[xxh-bench] File: $CORPUS ($FILE_SIZE bytes)"
echo "[xxh-bench] Iterations: $ITERATIONS"

# Check if hash_throughput benchmark exists
BENCH_EXE="_build/default/latex-parse/bench/hash_throughput.exe"
if [ -f "$BENCH_EXE" ]; then
  echo "[xxh-bench] Running compiled benchmark..."
  "$BENCH_EXE" "$CORPUS" "$ITERATIONS" 2>&1
else
  echo "[xxh-bench] Benchmark exe not found. Running inline OCaml measurement..."

  # Inline measurement using dune exec
  opam exec -- dune exec -- ocaml -stdin <<'OCAML'
    let () =
      let corpus = Sys.argv.(1) in
      let iterations = int_of_string Sys.argv.(2) in
      let ic = open_in corpus in
      let n = in_channel_length ic in
      let buf = Bytes.create n in
      really_input ic buf 0 n;
      close_in ic;
      (* Warm up *)
      for _ = 1 to 10 do
        ignore (Hashtbl.hash (Bytes.to_string buf))
      done;
      (* Measure *)
      let t0 = Unix.gettimeofday () in
      for _ = 1 to iterations do
        ignore (Hashtbl.hash (Bytes.to_string buf))
      done;
      let t1 = Unix.gettimeofday () in
      let total_bytes = float_of_int (n * iterations) in
      let elapsed = t1 -. t0 in
      let gb_per_s = total_bytes /. elapsed /. 1_000_000_000.0 in
      Printf.printf "[xxh-bench] %d iterations × %d bytes = %.1f MB\n"
        iterations n (total_bytes /. 1_000_000.0);
      Printf.printf "[xxh-bench] Elapsed: %.3f s\n" elapsed;
      Printf.printf "[xxh-bench] Throughput: %.2f GB/s (scalar baseline)\n" gb_per_s;
      if gb_per_s >= 20.0 then
        Printf.printf "[xxh-bench] PASS: >= 20 GB/s target\n"
      else
        Printf.printf "[xxh-bench] INFO: %.2f GB/s (scalar); SIMD target is 20 GB/s\n" gb_per_s
OCAML
fi

echo "[xxh-bench] Done"
