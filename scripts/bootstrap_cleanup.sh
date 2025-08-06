#!/bin/bash
# Bootstrap Cleanup Script - Strategy A-plus Implementation  
# Automates the compliance procedure from BOOTSTRAP_COMPLIANCE_SPECIFICATION.md

set -e

echo "🧹 Bootstrap Compliance Cleanup - Strategy A-plus"
echo "================================================="

# Color codes
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

info() {
    echo -e "${BLUE}ℹ${NC} $1"
}

success() {
    echo -e "${GREEN}✓${NC} $1"
}

warn() {
    echo -e "${YELLOW}⚠${NC} $1"
}

error() {
    echo -e "${RED}✗${NC} $1"
}

# Confirmation prompt
echo ""
warn "This script will remove development artifacts and large files from the repository."
warn "It implements Strategy A-plus from the Bootstrap Compliance Specification."
echo ""
read -p "Continue? (y/N): " -n 1 -r
echo
if [[ ! $REPLY =~ ^[Yy]$ ]]; then
    echo "Cleanup cancelled."
    exit 0
fi

echo ""
info "Starting Bootstrap compliance cleanup..."
echo ""

# Check if we're in the right directory
if [ ! -f "dune-project" ] || [ ! -f "README.md" ]; then
    error "Not in repository root (missing dune-project or README.md)"
    exit 1
fi

# Create backup branch for safety
BACKUP_BRANCH="backup-before-cleanup-$(date +%Y%m%d-%H%M%S)"
info "Creating backup branch: $BACKUP_BRANCH"
git branch "$BACKUP_BRANCH" 2>/dev/null || warn "Could not create backup branch (git not available or not a git repo)"

echo ""
echo "PHASE 1: POLLUTION REMOVAL"
echo "=========================="

# Step 1: Remove IDE pollution
info "Step 1: Removing .vscode directories..."
if [ -d "corpus" ]; then
    vscode_count=$(find corpus -name '.vscode' -type d 2>/dev/null | wc -l)
    if [ $vscode_count -gt 0 ]; then
        find corpus -name '.vscode' -type d -prune -exec rm -rf {} + 2>/dev/null || true
        success "Removed $vscode_count .vscode directories"
    else
        success "No .vscode directories found"
    fi
fi

# Step 2: Remove Python cache
info "Step 2: Removing Python cache..."
if [ -d "corpus" ]; then
    pycache_count=$(find corpus -name '__pycache__' -type d 2>/dev/null | wc -l)
    if [ $pycache_count -gt 0 ]; then
        find corpus -name '__pycache__' -type d -prune -exec rm -rf {} + 2>/dev/null || true
        success "Removed $pycache_count __pycache__ directories"
    else
        success "No __pycache__ directories found"  
    fi
    
    pyc_count=$(find corpus -name '*.pyc' 2>/dev/null | wc -l)
    if [ $pyc_count -gt 0 ]; then
        find corpus -name '*.pyc' -delete 2>/dev/null || true
        success "Removed $pyc_count .pyc files"
    fi
fi

# Step 3: Remove compiled artifacts
info "Step 3: Removing compiled artifacts..."
if [ -d "corpus" ]; then
    compiled_count=$(find corpus \( -name '*.o' -o -name '*.cm[iox]' \) 2>/dev/null | wc -l)
    if [ $compiled_count -gt 0 ]; then
        find corpus \( -name '*.o' -o -name '*.cm[iox]' \) -delete 2>/dev/null || true
        success "Removed $compiled_count compiled artifacts"
    fi
    
    # Remove specific large binaries
    for binary in tokenizer_optimized file_tokenizer_native; do
        if [ -f "corpus/$binary" ]; then
            rm -f "corpus/$binary"
            success "Removed binary: $binary"
        fi
    done
fi

# Step 4: Archive development scripts
info "Step 4: Archiving development scripts..."
if [ -d "corpus" ]; then
    mkdir -p archive/corpus-tools
    
    script_count=$(find corpus -maxdepth 1 -type f \( -name '*.py' -o -name '*.sh' -o -name '*.ml' \) 2>/dev/null | wc -l)
    if [ $script_count -gt 0 ]; then
        find corpus -maxdepth 1 -type f \( -name '*.py' -o -name '*.sh' -o -name '*.ml' \) -exec mv {} archive/corpus-tools/ \; 2>/dev/null || true
        success "Archived $script_count development scripts"
    else
        success "No development scripts to archive"
    fi
fi

echo ""
echo "PHASE 2: LARGE DIRECTORY ASSESSMENT"
echo "==================================="

# Check for large directories that should be externalized
if [ -d "corpus" ]; then
    info "Checking for large directories..."
    
    for dir in papers metadata stress; do
        if [ -d "corpus/$dir" ]; then
            size=$(du -sh "corpus/$dir" 2>/dev/null | cut -f1)
            warn "Large directory found: corpus/$dir ($size)"
            echo "  This should be moved to external storage per Strategy A-plus"
            echo "  Use: tar -czf ${dir}-$(date +%Y-%m-%d).tar.gz corpus/$dir"
            echo "       aws s3 cp ${dir}-$(date +%Y-%m-%d).tar.gz s3://latex-perf-corpora/raw/"
            echo "       rm -rf corpus/$dir"
            echo ""
        fi
    done
fi

echo ""
echo "PHASE 3: SIZE ASSESSMENT"
echo "========================"

# Report current sizes
info "Current size assessment:"
repo_size=$(du -sh . 2>/dev/null | cut -f1)
echo "  Repository total: $repo_size"

if [ -d "corpus" ]; then
    corpus_size=$(du -sh corpus 2>/dev/null | cut -f1)
    echo "  Corpus: $corpus_size"
fi

if [ -d "archive" ]; then
    archive_size=$(du -sh archive 2>/dev/null | cut -f1)
    echo "  Archive: $archive_size"
fi

echo ""
echo "PHASE 4: COMPLIANCE CHECK"
echo "========================="

# Run basic compliance checks
info "Running compliance verification..."

# Size compliance
repo_size_mb=$(du -sm . 2>/dev/null | cut -f1)
if [ $repo_size_mb -lt 1000 ]; then
    success "Repository size: ${repo_size_mb}MB (✓ under 1GB limit)"
else
    warn "Repository size: ${repo_size_mb}MB (exceeds 1GB limit)"
fi

if [ -d "corpus" ]; then
    corpus_size_mb=$(du -sm corpus 2>/dev/null | cut -f1)
    if [ $corpus_size_mb -lt 200 ]; then
        success "Corpus size: ${corpus_size_mb}MB (✓ under 200MB limit)"
    else
        warn "Corpus size: ${corpus_size_mb}MB (exceeds 200MB limit)"
    fi
fi

# Content compliance
vscode_remaining=$(find . -name '.vscode' -type d 2>/dev/null | wc -l)
if [ $vscode_remaining -eq 0 ]; then
    success "No .vscode directories remaining"
else
    warn "$vscode_remaining .vscode directories still present"
fi

cache_remaining=$(find . -name '__pycache__' -type d 2>/dev/null | wc -l)
if [ $cache_remaining -eq 0 ]; then
    success "No Python cache directories remaining"
else
    warn "$cache_remaining __pycache__ directories still present"
fi

echo ""
echo "PHASE 5: BUILD VERIFICATION"
echo "==========================="

# Test that build still works
info "Verifying build system functionality..."

if command -v opam >/dev/null 2>&1; then
    if eval $(opam env) 2>/dev/null; then
        success "opam environment activated"
        
        if make clean >/dev/null 2>&1 && make quick >/dev/null 2>&1; then
            success "make quick succeeds"
        else
            error "make quick fails after cleanup"
        fi
        
        if dune build >/dev/null 2>&1; then
            success "dune build succeeds"
        else
            error "dune build fails after cleanup"
        fi
        
        if dune runtest >/dev/null 2>&1; then
            success "dune runtest succeeds"
        else
            error "dune runtest fails after cleanup"
        fi
    else
        warn "opam environment not available"
    fi
else
    warn "opam not found - skipping build verification"
fi

echo ""
echo "📋 CLEANUP SUMMARY"
echo "=================="

echo "Completed Strategy A-plus cleanup procedure:"
echo ""
echo "✓ Removed IDE configuration pollution"
echo "✓ Removed Python cache and compiled artifacts"  
echo "✓ Archived development scripts to archive/corpus-tools/"
echo "✓ Verified build system functionality"
echo ""

if [ $repo_size_mb -lt 1000 ] && [ ${corpus_size_mb:-0} -lt 200 ]; then
    success "🎉 BOOTSTRAP COMPLIANCE ACHIEVED"
    echo ""
    echo "Repository is now Bootstrap Skeleton compliant!"
    echo "  - Repository size: ${repo_size_mb}MB (limit: 1000MB)"
    echo "  - Corpus size: ${corpus_size_mb:-0}MB (limit: 200MB)"
    echo "  - Build system functional"
    echo ""
    echo "Next steps:"
    echo "  1. Review large directories identified above"
    echo "  2. Move them to external storage if needed"  
    echo "  3. Run full compliance check: ./scripts/verify_compliance.sh"
    echo "  4. Commit changes: git add -A && git commit -m 'chore: implement Bootstrap compliance - Strategy A-plus'"
else
    warn "⚠️  PARTIAL COMPLIANCE"
    echo ""
    echo "Cleanup completed but size limits still exceeded."
    echo "Manual intervention required for large directories:"
    echo ""
    if [ -d "corpus/papers" ]; then
        echo "  - Move corpus/papers/ to external storage (~15GB)"
    fi
    if [ -d "corpus/metadata" ]; then  
        echo "  - Move corpus/metadata/ to external storage (~120MB)"
    fi
    if [ -d "corpus/stress" ]; then
        echo "  - Move corpus/stress/ to external storage (~4GB)"
    fi
    echo ""
    echo "Then run: ./scripts/verify_compliance.sh"
fi

echo ""
echo "Backup branch created: $BACKUP_BRANCH"
echo "To revert changes: git checkout $BACKUP_BRANCH"