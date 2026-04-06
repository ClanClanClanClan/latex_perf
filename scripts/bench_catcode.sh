#!/usr/bin/env bash
# Catcode scanner benchmark (spec W20)
#
# Measures catcode classification throughput. Compares scalar OCaml
# baseline against SIMD C path if compiled.
# Target: SIMD ≥ 6× scalar baseline.
#
# Usage:
#   bash scripts/bench_catcode.sh

set -euo pipefail

CORPUS="corpora/perf/perf_smoke_big.tex"
ITERATIONS=200

if [ ! -f "$CORPUS" ]; then
  echo "[catcode-bench] Corpus not found: $CORPUS"
  echo "[catcode-bench] Using README.md as fallback"
  CORPUS="README.md"
fi

FILE_SIZE=$(wc -c < "$CORPUS")
echo "[catcode-bench] File: $CORPUS ($FILE_SIZE bytes)"
echo "[catcode-bench] Iterations: $ITERATIONS"

# Check for SIMD library
SIMD_LIB="_build/default/core/l0_lexer/simd/simd_tokenizer.o"
if [ -f "$SIMD_LIB" ]; then
  echo "[catcode-bench] SIMD object found: $SIMD_LIB"
  SIMD_AVAILABLE=1
else
  echo "[catcode-bench] SIMD object not found (scalar-only mode)"
  SIMD_AVAILABLE=0
fi

# Scalar benchmark: classify every byte via OCaml catcode
echo ""
echo "[catcode-bench] === Scalar OCaml Baseline ==="
SCALAR_THROUGHPUT=$(opam exec -- dune exec -- ocaml -stdin "$CORPUS" "$ITERATIONS" 2>/dev/null <<'OCAML' || echo "0.0"
let () =
  let corpus = Sys.argv.(1) in
  let iterations = int_of_string Sys.argv.(2) in
  let ic = open_in corpus in
  let n = in_channel_length ic in
  let buf = Bytes.create n in
  really_input ic buf 0 n;
  close_in ic;
  (* Catcode classification: simple match on each byte *)
  let classify_byte b =
    match Char.code b with
    | 92 -> 0 | 123 -> 1 | 125 -> 2 | 36 -> 3
    | 38 -> 4 | 10 | 13 -> 5 | 35 -> 6 | 94 -> 7
    | 95 -> 8 | 0 -> 9 | 32 | 9 -> 10 | 126 -> 13
    | 37 -> 14 | 127 -> 15
    | c when (c >= 65 && c <= 90) || (c >= 97 && c <= 122) -> 11
    | _ -> 12
  in
  (* Warm up *)
  for _ = 1 to 5 do
    Bytes.iter (fun c -> ignore (classify_byte c)) buf
  done;
  (* Measure *)
  let t0 = Unix.gettimeofday () in
  for _ = 1 to iterations do
    Bytes.iter (fun c -> ignore (classify_byte c)) buf
  done;
  let t1 = Unix.gettimeofday () in
  let total_bytes = float_of_int (n * iterations) in
  let elapsed = t1 -. t0 in
  let gb_per_s = total_bytes /. elapsed /. 1_000_000_000.0 in
  Printf.printf "%.2f\n" gb_per_s
OCAML
)

echo "[catcode-bench] Scalar throughput: ${SCALAR_THROUGHPUT} GB/s"

if [ "$SIMD_AVAILABLE" = "1" ]; then
  echo ""
  echo "[catcode-bench] === SIMD C Path ==="
  echo "[catcode-bench] SIMD benchmark requires compiled simd_tokenizer.o"
  echo "[catcode-bench] (build with: cd core/l0_lexer/simd && make)"
  # TODO: Run SIMD benchmark when compiled
  echo "[catcode-bench] SIMD path not yet benchmarked"
fi

echo ""
echo "[catcode-bench] Summary:"
echo "[catcode-bench]   Scalar: ${SCALAR_THROUGHPUT} GB/s"
echo "[catcode-bench]   SIMD target: 6× = $(echo "$SCALAR_THROUGHPUT * 6" | bc 2>/dev/null || echo "N/A") GB/s"
echo "[catcode-bench]   Spec target: 6× baseline"
echo "[catcode-bench] Done"
