#!/bin/bash
# BUILD THE REAL OPTIMIZED LEXER - No bullshit, just the working implementation
set -e

echo "🔥 BUILDING THE REAL OPTIMIZED LEXER"
echo "===================================="

# Check Flambda
eval $(opam env)
FLAMBDA_CHECK=$(ocamlopt -config | grep "flambda:" | awk '{print $2}')
echo "OCaml: $(ocamlopt -version)"
echo "Flambda: $FLAMBDA_CHECK"

if [ "$FLAMBDA_CHECK" != "true" ]; then
    echo "⚠️  WARNING: No Flambda detected - performance will be suboptimal"
fi

# Clean build
rm -f real_optimized_lexer*

echo ""
echo "🚀 Compiling the ACTUAL working implementation..."

# Use the EXACT same flags as the working version
OPTFLAGS="-O3 -inline 100 -unbox-closures -rounds 4 -unsafe"

# Compile directly from the working source
ocamlopt $OPTFLAGS -I +unix -o real_optimized_lexer unix.cmxa \
  test/performance/test_arena_flambda2_direct.ml

echo "✅ Real optimized lexer built"
echo ""
echo "🎯 Testing the REAL implementation..."
echo ""

./real_optimized_lexer