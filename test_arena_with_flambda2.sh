#!/bin/bash
# TEST ARENA WITH FLAMBDA2 - CRITICAL FOR MEETING PERFORMANCE TARGET

echo "=== TESTING WITH FLAMBDA2 COMPILER ==="
echo "THIS IS THE CRITICAL TEST THAT SHOWS REAL PERFORMANCE"
echo ""
echo "Using switch: flambda-opt (OCaml 5.1.1+flambda2)"
echo "Checking Flambda2 status:"
OPAMSWITCH=flambda-opt opam exec -- ocamlopt -config | grep flambda
echo ""

# Compile with Flambda2
echo "🔧 COMPILING WITH FLAMBDA2 OPTIMIZATIONS..."
OPAMSWITCH=flambda-opt opam exec -- ocamlopt \
  -O3 \
  -inline 100 \
  -inline-max-unroll 5 \
  -unbox-closures \
  -unbox-closures-factor 20 \
  -rounds 4 \
  -unsafe \
  -I src/data \
  -I src/core \
  -o test_arena_flambda2 \
  unix.cmxa \
  src/data/location.ml \
  src/data/catcode.ml \
  src/data/chunk.ml \
  src/data/dlist.ml \
  src/data/data.ml \
  src/core/l0_lexer_track_a_arena_standalone.ml \
  test_arena_optimized_packed.ml

if [ $? -eq 0 ]; then
  echo "✅ Compilation successful"
  echo ""
  echo "🚀 RUNNING PERFORMANCE TEST WITH FLAMBDA2..."
  ./test_arena_flambda2
else
  echo "❌ Compilation failed"
  exit 1
fi