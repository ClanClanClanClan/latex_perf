#!/bin/bash
# Organization Health Check Script
# Run before commits to ensure pristine organization

set -e

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

ERRORS=0
WARNINGS=0

echo "🔍 LaTeX Perfectionist v25 - Organization Health Check"
echo "======================================================"
echo ""

# Check 1: Root directory files
echo "📁 Checking root directory..."
ALLOWED_ROOT_FILES="README.md CLAUDE.md DOCUMENTATION_INDEX.md LICENSE Makefile Makefile.coq.conf Makefile.robust _CoqProject dune dune-project dune-workspace latex-perfectionist.opam .gitignore .github .ocamlformat .gitmessage"
EXTRA_FILES=""

for file in $(ls -a | grep -v "^\.$" | grep -v "^\.\.$" | grep -v "^\.git$" | grep -v "^\(src\|test\|docs\|build\|specs\|proofs\|scripts\|bench\|cli\|config\|corpora\|grammar\|rules_src\)$"); do
    if ! echo "$ALLOWED_ROOT_FILES" | grep -q "$file"; then
        EXTRA_FILES="$EXTRA_FILES $file"
        ((ERRORS++))
    fi
done

if [ -z "$EXTRA_FILES" ]; then
    echo -e "${GREEN}✅ Root directory clean${NC}"
else
    echo -e "${RED}❌ Unexpected files in root:${EXTRA_FILES}${NC}"
fi
echo ""

# Check 2: Build artifacts in source tree
echo "🔨 Checking for build artifacts in source..."
BUILD_ARTIFACTS=$(find src/ -name "*.cmo" -o -name "*.cmx" -o -name "*.o" -o -name "*.cmi" -o -name "*.cmxa" 2>/dev/null || true)

if [ -z "$BUILD_ARTIFACTS" ]; then
    echo -e "${GREEN}✅ No build artifacts in source tree${NC}"
else
    echo -e "${RED}❌ Build artifacts found:${NC}"
    echo "$BUILD_ARTIFACTS"
    ((ERRORS++))
fi
echo ""

# Check 3: Backup and temporary files
echo "🗑️  Checking for backup/temp files..."
BACKUP_FILES=$(find . -name "*.bak" -o -name "*.backup" -o -name "*.old" -o -name "*.tmp" -o -name "*.temp" -o -name "*.disabled" 2>/dev/null | grep -v ".git/" || true)

if [ -z "$BACKUP_FILES" ]; then
    echo -e "${GREEN}✅ No backup/temp files found${NC}"
else
    echo -e "${YELLOW}⚠️  Backup/temp files found:${NC}"
    echo "$BACKUP_FILES"
    ((WARNINGS++))
fi
echo ""

# Check 4: Layer separation
echo "🏗️  Checking layer separation..."
LAYER_VIOLATIONS=""

# Check for L1 references in L0
if grep -r "L1_expander\|l1_expander" src/core/l0_lexer/ 2>/dev/null | grep -v "^Binary file"; then
    LAYER_VIOLATIONS="${LAYER_VIOLATIONS}\n  L0 depends on L1"
    ((ERRORS++))
fi

# Check for L2 references in L1
if grep -r "L2_parser\|l2_parser" src/core/l1_expander/ 2>/dev/null | grep -v "^Binary file"; then
    LAYER_VIOLATIONS="${LAYER_VIOLATIONS}\n  L1 depends on L2"
    ((ERRORS++))
fi

if [ -z "$LAYER_VIOLATIONS" ]; then
    echo -e "${GREEN}✅ Layer separation maintained${NC}"
else
    echo -e "${RED}❌ Layer violations found:${LAYER_VIOLATIONS}${NC}"
fi
echo ""

# Check 5: Documentation index freshness
echo "📚 Checking documentation index..."
MISSING_DOCS=""

# Check if major docs are in index
for doc in README.md CLAUDE.md; do
    if ! grep -q "$doc" DOCUMENTATION_INDEX.md 2>/dev/null; then
        MISSING_DOCS="${MISSING_DOCS} $doc"
        ((WARNINGS++))
    fi
done

if [ -z "$MISSING_DOCS" ]; then
    echo -e "${GREEN}✅ Documentation index up to date${NC}"
else
    echo -e "${YELLOW}⚠️  Missing from documentation index:${MISSING_DOCS}${NC}"
fi
echo ""

# Check 6: File naming conventions
echo "📝 Checking naming conventions..."
BAD_NAMES=""

# Check for spaces in filenames
SPACE_FILES=$(find src/ test/ -name "* *" 2>/dev/null || true)
if [ ! -z "$SPACE_FILES" ]; then
    BAD_NAMES="${BAD_NAMES}\n  Files with spaces: ${SPACE_FILES}"
    ((ERRORS++))
fi

# Check for uppercase in ML files (should be lowercase)
UPPER_ML=$(find src/ -name "*.ml" | grep -E "[A-Z]" | grep -v "README" || true)
if [ ! -z "$UPPER_ML" ]; then
    echo -e "${YELLOW}⚠️  ML files with uppercase (consider renaming):${NC}"
    echo "$UPPER_ML"
    ((WARNINGS++))
fi

if [ -z "$BAD_NAMES" ]; then
    echo -e "${GREEN}✅ File naming conventions followed${NC}"
else
    echo -e "${RED}❌ Naming violations:${BAD_NAMES}${NC}"
fi
echo ""

# Check 7: Size of directories (early warning for clutter)
echo "📊 Checking directory sizes..."
# Count only files, not directories
ROOT_FILE_COUNT=$(find . -maxdepth 1 -type f ! -name ".*" | wc -l)
ROOT_TOTAL=$(ls -1 | wc -l)
if [ $ROOT_FILE_COUNT -gt 15 ]; then
    echo -e "${YELLOW}⚠️  Root directory has $ROOT_FILE_COUNT files (target: ≤15)${NC}"
    ((WARNINGS++))
else
    echo -e "${GREEN}✅ Root directory size OK ($ROOT_FILE_COUNT files, $ROOT_TOTAL total items)${NC}"
fi
echo ""

# Check 8: Coq proof admits (accuracy check)
echo "🔬 Checking formal verification status..."
ADMIT_COUNT=$(grep "^Admitted\." proofs/ src/core/l1_expander/expander/ -r --include="*.v" 2>/dev/null | grep -v "\.broken" | wc -l || echo 0)
if [ $ADMIT_COUNT -eq 3 ]; then
    echo -e "${GREEN}✅ Expected 3 admits (tactical helpers only)${NC}"
elif [ $ADMIT_COUNT -lt 3 ]; then
    echo -e "${GREEN}✅ Fewer than expected admits ($ADMIT_COUNT)${NC}"
else
    echo -e "${YELLOW}⚠️  More admits than expected: $ADMIT_COUNT (expected: 3)${NC}"
    ((WARNINGS++))
fi
echo ""

# Summary
echo "======================================================"
echo "📋 SUMMARY"
echo ""

if [ $ERRORS -eq 0 ] && [ $WARNINGS -eq 0 ]; then
    echo -e "${GREEN}🎉 PERFECT! Organization is pristine.${NC}"
    exit 0
elif [ $ERRORS -eq 0 ]; then
    echo -e "${YELLOW}✅ GOOD: No errors, but $WARNINGS warning(s) to review.${NC}"
    exit 0
else
    echo -e "${RED}❌ FAILED: $ERRORS error(s) and $WARNINGS warning(s) found.${NC}"
    echo ""
    echo "Please fix errors before committing:"
    echo "1. Run 'make clean' to remove build artifacts"
    echo "2. Move unexpected root files to appropriate directories"
    echo "3. Delete or archive backup/temp files"
    echo "4. Fix any layer separation violations"
    echo ""
    echo "See docs/developer/ORGANIZATION_GUIDELINES.md for details."
    exit 1
fi