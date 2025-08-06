#!/bin/bash
# Bootstrap Compliance Verification Script
# Implements the verification checklist from BOOTSTRAP_COMPLIANCE_SPECIFICATION.md

set -e

echo "🔍 Bootstrap Compliance Verification - LaTeX Perfectionist v25"
echo "================================================================"

COMPLIANCE_PASS=true

# Color codes for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

pass() {
    echo -e "${GREEN}✓${NC} $1"
}

fail() {
    echo -e "${RED}✗${NC} $1"
    COMPLIANCE_PASS=false
}

warn() {
    echo -e "${YELLOW}⚠${NC} $1"
}

echo "1. SIZE COMPLIANCE CHECKS"
echo "========================"

# Repository size check
repo_size_mb=$(du -sm . 2>/dev/null | cut -f1)
if [ $repo_size_mb -lt 1000 ]; then
    pass "Repository size: ${repo_size_mb}MB (limit: 1000MB)"
else
    fail "Repository size: ${repo_size_mb}MB exceeds 1GB limit"
fi

# Corpus size check
if [ -d "corpus" ]; then
    corpus_size_mb=$(du -sm corpus 2>/dev/null | cut -f1)
    if [ $corpus_size_mb -lt 200 ]; then
        pass "Corpus size: ${corpus_size_mb}MB (limit: 200MB)"
    else
        fail "Corpus size: ${corpus_size_mb}MB exceeds 200MB limit"
    fi
else
    warn "Corpus directory not found"
fi

# Large file check
large_files=$(find . -size +20M -type f 2>/dev/null | grep -v '.git' | wc -l)
if [ $large_files -eq 0 ]; then
    pass "No files >20MB found"
else
    fail "Found $large_files files >20MB:"
    find . -size +20M -type f 2>/dev/null | grep -v '.git' | head -5
fi

echo ""
echo "2. CONTENT COMPLIANCE CHECKS"
echo "============================"

# .vscode directories
vscode_count=$(find . -name '.vscode' -type d 2>/dev/null | wc -l)
if [ $vscode_count -eq 0 ]; then
    pass "No .vscode directories found"
else
    fail "Found $vscode_count .vscode directories"
    find . -name '.vscode' -type d 2>/dev/null | head -3
fi

# Python cache
pycache_count=$(find . -name '__pycache__' -type d 2>/dev/null | wc -l)
if [ $pycache_count -eq 0 ]; then
    pass "No Python cache directories found"
else
    fail "Found $pycache_count __pycache__ directories"
fi

# Compiled artifacts
compiled_count=$(find . -path ./_build -prune -o \( -name '*.o' -o -name '*.cm[iox]' \) -type f -print 2>/dev/null | wc -l)
if [ $compiled_count -eq 0 ]; then
    pass "No compiled artifacts found"
else
    fail "Found $compiled_count compiled artifacts"
fi

# Scripts in corpus root
if [ -d "corpus" ]; then
    script_count=$(find corpus -maxdepth 1 -type f \( -name '*.py' -o -name '*.sh' -o -name '*.ml' \) 2>/dev/null | wc -l)
    if [ $script_count -eq 0 ]; then
        pass "No development scripts in corpus root"
    else
        fail "Found $script_count development scripts in corpus root"
        find corpus -maxdepth 1 -type f \( -name '*.py' -o -name '*.sh' -o -name '*.ml' \) 2>/dev/null
    fi
fi

echo ""
echo "3. FUNCTIONALITY COMPLIANCE CHECKS"
echo "=================================="

# Opam environment
if command -v opam >/dev/null 2>&1; then
    if eval $(opam env) 2>/dev/null; then
        pass "opam environment available"
    else
        warn "opam environment not activated"
    fi
else
    warn "opam not found in PATH"
fi

# Build system check
if [ -f "Makefile" ] && [ -f "dune-project" ]; then
    pass "Build system files present"
    
    # Test make quick
    if make clean >/dev/null 2>&1 && make quick >/dev/null 2>&1; then
        pass "make quick succeeds"
    else
        fail "make quick fails"
    fi
    
    # Test dune build
    if dune build >/dev/null 2>&1; then
        pass "dune build succeeds"
    else
        fail "dune build fails"
    fi
    
    # Test dune runtest
    if dune runtest >/dev/null 2>&1; then
        pass "dune runtest succeeds"
    else
        fail "dune runtest fails"
    fi
else
    fail "Build system files missing (Makefile, dune-project)"
fi

echo ""
echo "4. STRUCTURE COMPLIANCE CHECKS"
echo "=============================="

# Essential directories
essential_dirs=("src" "proofs" "rules_src" "test")
for dir in "${essential_dirs[@]}"; do
    if [ -d "$dir" ]; then
        pass "Essential directory present: $dir/"
    else
        fail "Essential directory missing: $dir/"
    fi
done

# Corpus structure (if present)
if [ -d "corpus" ]; then
    corpus_dirs=("minimal" "standard" "categories" "ground_truth")
    for dir in "${corpus_dirs[@]}"; do
        if [ -d "corpus/$dir" ]; then
            pass "Corpus directory present: corpus/$dir/"
        else
            warn "Corpus directory missing: corpus/$dir/"
        fi
    done
    
    # Check for external corpus registry
    if [ -f "corpus/corpora.lock" ]; then
        pass "External corpus registry present: corpus/corpora.lock"
    else
        warn "External corpus registry missing: corpus/corpora.lock"
    fi
fi

echo ""
echo "5. BOOTSTRAP SKELETON VERIFICATION"
echo "=================================="

# Check README
if [ -f "README.md" ]; then
    if grep -q "Bootstrap Skeleton" README.md; then
        pass "README.md identifies as Bootstrap Skeleton"
    else
        warn "README.md does not identify as Bootstrap Skeleton"
    fi
else
    fail "README.md missing"
fi

# Check CoreProofs
if [ -d "proofs/CoreProofs" ]; then
    coq_files=$(find proofs/CoreProofs -name "*.v" | wc -l)
    if [ $coq_files -ge 7 ]; then
        pass "CoreProofs library present ($coq_files .v files)"
    else
        warn "CoreProofs library incomplete ($coq_files .v files, expected ≥7)"
    fi
else
    fail "CoreProofs library missing"
fi

# Check for admits/axioms in Coq files
if [ -d "proofs" ]; then
    admit_count=$(find proofs -name "*.v" -exec grep -l "^[[:space:]]*\(admit\|Admit\|axiom\|Axiom\)[[:space:]]*\." {} \; 2>/dev/null | wc -l)
    if [ $admit_count -eq 0 ]; then
        pass "No admits or axioms found in Coq proofs"
    else
        fail "Found admits or axioms in $admit_count Coq files"
    fi
fi

echo ""
echo "6. SUMMARY"
echo "=========="

if $COMPLIANCE_PASS; then
    echo -e "${GREEN}🎉 BOOTSTRAP COMPLIANCE: PASSED${NC}"
    echo "Repository meets all Bootstrap Skeleton requirements"
    exit 0
else
    echo -e "${RED}❌ BOOTSTRAP COMPLIANCE: FAILED${NC}"
    echo "Repository has compliance violations that must be addressed"
    echo ""
    echo "To fix violations, run:"
    echo "  ./scripts/bootstrap_cleanup.sh"
    echo ""
    echo "Then re-run this verification:"
    echo "  ./scripts/verify_compliance.sh"
    exit 1
fi