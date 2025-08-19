#!/bin/bash
# LaTeX Perfectionist v25 - UNIFIED BUILD SCRIPT
# Intelligent build selection with automatic fallback
set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo "🏗️  LaTeX Perfectionist v25 - Unified Build System"
echo "=================================================="

# Parse arguments
BUILD_METHOD=""
BUILD_TYPE="dev"
CLEAN_ONLY=false

while [[ $# -gt 0 ]]; do
    case $1 in
        --release|--perf)
            BUILD_TYPE="release"
            shift
            ;;
        --dune)
            BUILD_METHOD="dune"
            shift
            ;;
        --manual|--alt)
            BUILD_METHOD="manual"
            shift
            ;;
        --clean)
            CLEAN_ONLY=true
            shift
            ;;
        --help|-h)
            cat << EOF
Usage: ./build.sh [OPTIONS]

Options:
  --release, --perf    Build with optimizations
  --dune              Force Dune build
  --manual, --alt     Force manual build
  --clean             Clean all artifacts
  --help              Show this help

Examples:
  ./build.sh           # Auto-select build method
  ./build.sh --release # Optimized build
  ./build.sh --dune    # Force Dune
  ./build.sh --clean   # Clean everything
EOF
            exit 0
            ;;
        *)
            echo -e "${RED}Unknown option: $1${NC}"
            exit 1
            ;;
    esac
done

# Clean if requested
if [ "$CLEAN_ONLY" = true ]; then
    echo "🧹 Cleaning all build artifacts..."
    rm -rf _build _build_robust _manual_build
    rm -f *.cm* core/*.cm* data/*.cm* 
    rm -f lexer_v25 test_*
    dune clean 2>/dev/null || true
    echo -e "${GREEN}✅ Clean complete${NC}"
    exit 0
fi

# Check environment
echo "📍 Checking build environment..."
eval $(opam env)

OCAML_VERSION=$(ocamlopt -version 2>&1 | head -1)
FLAMBDA_CHECK=$(ocamlopt -config | grep "flambda:" | awk '{print $2}')
FLAMBDA2_CHECK=$(ocamlopt -config | grep "flambda2:" | awk '{print $2}' 2>/dev/null || echo "false")

echo "   OCaml: $OCAML_VERSION"
echo "   Flambda: $FLAMBDA_CHECK"
echo "   Flambda2: $FLAMBDA2_CHECK"

# Performance warning for release builds
if [ "$BUILD_TYPE" = "release" ]; then
    if [ "$FLAMBDA2_CHECK" != "true" ]; then
        echo ""
        echo -e "${YELLOW}⚠️  WARNING: Flambda2 not detected!${NC}"
        echo "   L0 performance will be ~26ms (exceeds ≤20ms target)"
        echo "   For 17-18ms performance, install Flambda2:"
        echo "   opam switch create v25-perf ocaml-variants.5.1.1+flambda2"
        echo ""
        read -p "Continue anyway? (y/n) " -n 1 -r
        echo
        if [[ ! $REPLY =~ ^[Yy]$ ]]; then
            exit 1
        fi
    fi
fi

# Function to try Dune build
try_dune_build() {
    if command -v dune &> /dev/null; then
        echo "🔧 Attempting Dune build..."
        if [ "$BUILD_TYPE" = "release" ]; then
            dune build --profile release && return 0
        else
            dune build && return 0
        fi
    fi
    return 1
}

# Function to do manual build
try_manual_build() {
    echo "🔧 Performing manual build..."
    
    # Determine paths
    if [ -d "src/data" ]; then
        DATA_DIR="src/data"
        CORE_DIR="src/core"
    else
        DATA_DIR="data"
        CORE_DIR="core"
    fi
    
    # Set optimization flags
    if [ "$BUILD_TYPE" = "release" ]; then
        OPTFLAGS="-O3 -inline 100"
        if [ "$FLAMBDA2_CHECK" = "true" ]; then
            OPTFLAGS="$OPTFLAGS -unbox-closures -rounds 4"
        fi
    else
        OPTFLAGS="-O2"
    fi
    
    mkdir -p _manual_build
    
    # Build data library
    echo "  Building data library..."
    cd "$DATA_DIR"
    for f in location catcode chunk dlist; do
        [ -f "$f.mli" ] && ocamlopt $OPTFLAGS -c "$f.mli"
        ocamlopt $OPTFLAGS -c "$f.ml"
    done
    ocamlopt $OPTFLAGS -c data.ml
    
    # Return to root
    cd - > /dev/null
    
    # Build core
    echo "  Building core library..."
    cd "$CORE_DIR"
    
    # Check for lexer_v25.mli in different locations
    if [ -f "lexer_v25.mli" ]; then
        ocamlopt $OPTFLAGS -I "../$DATA_DIR" -c lexer_v25.mli
    elif [ -f "l0_lexer/lexer_v25.mli" ]; then
        ocamlopt $OPTFLAGS -I "../$DATA_DIR" -c l0_lexer/lexer_v25.mli
    fi
    
    # Compile lexer implementations
    for impl in lexer_v25.ml l0_lexer_track_a_arena.ml; do
        if [ -f "$impl" ]; then
            ocamlopt $OPTFLAGS -I "../$DATA_DIR" -c "$impl"
        elif [ -f "l0_lexer/$impl" ]; then
            ocamlopt $OPTFLAGS -I "../$DATA_DIR" -c "l0_lexer/$impl"
        fi
    done
    
    cd - > /dev/null
    
    echo -e "${GREEN}✅ Manual build complete${NC}"
    return 0
}

# Main build logic
echo ""
if [ -n "$BUILD_METHOD" ]; then
    # User specified method
    case $BUILD_METHOD in
        dune)
            try_dune_build || {
                echo -e "${RED}Dune build failed${NC}"
                exit 1
            }
            ;;
        manual)
            try_manual_build || {
                echo -e "${RED}Manual build failed${NC}"
                exit 1
            }
            ;;
    esac
else
    # Auto-select: try Dune first, then manual
    echo "🔄 Auto-selecting build method..."
    if try_dune_build; then
        echo -e "${GREEN}✅ Dune build successful${NC}"
    elif try_manual_build; then
        echo -e "${GREEN}✅ Manual build successful${NC}"
    else
        echo -e "${RED}❌ All build methods failed${NC}"
        echo "Try: ./build.sh --clean && ./build.sh"
        exit 1
    fi
fi

# Report success
echo ""
echo "=================================================="
echo -e "${GREEN}✅ BUILD SUCCESSFUL${NC}"
echo ""
echo "Build type: $BUILD_TYPE"
if [ "$FLAMBDA2_CHECK" = "true" ]; then
    echo "Compiler: Flambda2 ✅ (optimal performance)"
else
    echo "Compiler: Standard (use Flambda2 for ≤20ms target)"
fi
echo ""
echo "To test performance:"
echo "  ./test/performance/test_true_arena_implementation"
echo ""
echo "For more info: see BUILD_GUIDE.md"