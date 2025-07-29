#!/bin/bash
# AUTOMATED VERIFICATION SCRIPT
# Purpose: Prevent factual errors and ensure documentation consistency
# Usage: ./automated_verification.sh
# Standard: All verifications must pass before proceeding with development

set -e  # Exit on any error

echo "=== AUTOMATED VERIFICATION SUITE ==="
echo "Purpose: Ensure foundation reliability before Week 4"
echo "Date: $(date)"
echo

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

error_count=0

# Function to report errors
report_error() {
    echo -e "${RED}ERROR: $1${NC}"
    error_count=$((error_count + 1))
}

report_success() {
    echo -e "${GREEN}✓ $1${NC}"
}

report_warning() {
    echo -e "${YELLOW}⚠ WARNING: $1${NC}"
}

# 1. VERIFY LINE COUNTS
echo "1. VERIFYING LINE COUNTS..."
if [ -f "src/coq/vsna/UVSNA.v" ]; then
    UVSNA_LINES=$(wc -l src/coq/vsna/UVSNA.v | awk '{print $1}')
    echo "   UVSNA.v actual lines: $UVSNA_LINES"
    
    # Check for incorrect line count claims (look for specific patterns that indicate current UVSNA claims)
    CURRENT_254_CLAIMS=$(grep -l "UVSNA.*254\|254.*UVSNA" *.md 2>/dev/null | grep -v "HONEST_ORGANIZATIONAL_ASSESSMENT" | grep -v "FOUNDATION_STRENGTHENING_PLAN" | wc -l)
    if [ "$CURRENT_254_CLAIMS" -gt 0 ]; then
        report_error "Documents still claim UVSNA.v has 254 lines, but actual: $UVSNA_LINES lines"
    else
        # Check for correct line count
        if grep -q "${UVSNA_LINES} lines" *.md 2>/dev/null; then
            report_success "Line count documentation matches actual ($UVSNA_LINES lines)"
        else
            report_warning "Line count not found in documentation (expected: $UVSNA_LINES lines)"
        fi
    fi
else
    report_error "UVSNA.v file not found at src/coq/vsna/UVSNA.v"
fi

# 2. VERIFY COMPILATION
echo
echo "2. VERIFYING COMPILATION..."
if [ -d "src/coq/vsna" ]; then
    cd src/coq/vsna
    if coqc UVSNA.v >/dev/null 2>&1; then
        report_success "UVSNA.v compiles successfully"
    else
        report_error "UVSNA.v compilation failed"
    fi
    cd - >/dev/null
else
    report_error "VSNA source directory not found"
fi

# 3. VERIFY ADMITTED PROOF COUNT
echo
echo "3. VERIFYING ADMITTED PROOF COUNT..."
if [ -d "src/coq/vsna" ]; then
    ACTUAL_ADMITS=$(find src/coq/vsna -name "*.v" -exec grep -c "Admitted" {} \; 2>/dev/null | awk '{sum += $1} END {print sum}')
    echo "   Actual admits in VSNA: $ACTUAL_ADMITS"
    
    # Check documentation claims
    if grep -q "38.*admits" *.md 2>/dev/null; then
        if [ "$ACTUAL_ADMITS" = "38" ]; then
            report_success "Admitted proof count matches documentation (38)"
        else
            report_error "Admit count mismatch. Documentation claims 38, actual: $ACTUAL_ADMITS"
        fi
    else
        report_warning "Admitted proof count not found in documentation"
    fi
else
    report_error "VSNA source directory not found for admit counting"
fi

# 4. VERIFY TIMELINE CONSISTENCY
echo
echo "4. VERIFYING TIMELINE CONSISTENCY..."
TIMELINE_ERRORS=0

# Check for conflicting timeline information (excluding appropriate historical/comparative references)
CURRENT_15MONTH_REFS=$(grep -l "15.month" *.md 2>/dev/null | grep -v "HONEST_ORGANIZATIONAL_ASSESSMENT\|DOCUMENTATION_CLEANUP_PLAN\|archive\|vs.*15.*month\|15.*month.*vs" | wc -l)
if [ "$CURRENT_15MONTH_REFS" -gt 0 ]; then
    report_error "Documents still reference 15-month timeline"
    TIMELINE_ERRORS=$((TIMELINE_ERRORS + 1))
fi

if grep -q "26.week" *.md 2>/dev/null || grep -q "26 week" *.md 2>/dev/null; then
    report_success "26-week timeline referenced in documentation"
else
    report_warning "26-week timeline not clearly stated in documentation"
    TIMELINE_ERRORS=$((TIMELINE_ERRORS + 1))
fi

if [ $TIMELINE_ERRORS -eq 0 ]; then
    report_success "Timeline consistency verified"
fi

# 5. VERIFY STATUS INDICATORS
echo
echo "5. VERIFYING STATUS INDICATORS..."
STATUS_ERRORS=0

# Check for false completion claims (excluding appropriate contextual references)
FALSE_COMPLETION_CLAIMS=$(grep -l "100%.*complete\|all.*complete" *.md 2>/dev/null | grep -v "DOCUMENTATION_CLEANUP_PLAN\|HONEST_ORGANIZATIONAL_ASSESSMENT\|FOUNDATION_STRENGTHENING_PLAN" | wc -l)
if [ "$FALSE_COMPLETION_CLAIMS" -gt 0 ]; then
    report_error "Documents contain false completion claims"
    STATUS_ERRORS=$((STATUS_ERRORS + 1))
fi

# Check for proper status indicators
if grep -q "✅.*COMPLETE" *.md 2>/dev/null && grep -q "📅.*PENDING" *.md 2>/dev/null; then
    report_success "Proper status indicators found"
else
    report_warning "Status indicator usage inconsistent"
    STATUS_ERRORS=$((STATUS_ERRORS + 1))
fi

if [ $STATUS_ERRORS -eq 0 ]; then
    report_success "Status indicator consistency verified"
fi

# 6. VERIFY BUILD SYSTEM
echo
echo "6. VERIFYING BUILD SYSTEM..."
if [ -f "Makefile" ] || [ -f "build_ocaml.sh" ]; then
    if [ -f "build_ocaml.sh" ] && [ -x "build_ocaml.sh" ]; then
        report_success "Build script found and executable"
    else
        report_warning "Build script exists but may not be executable"
    fi
else
    report_error "No build system found (Makefile or build_ocaml.sh)"
fi

# 7. VERIFY MASTER PLAN EXISTENCE
echo
echo "7. VERIFYING MASTER CONTROL DOCUMENTS..."
REQUIRED_DOCS=(
    "PROJECT_MASTER_PLAN.md"
    "CURRENT_STATUS_VERIFIED.md"
    "DOCUMENTATION_CLEANUP_PLAN.md"
    "PROJECT_ORGANIZATION_STRUCTURE.md"
)

for doc in "${REQUIRED_DOCS[@]}"; do
    if [ -f "$doc" ]; then
        report_success "Master control document exists: $doc"
    else
        report_error "Missing master control document: $doc"
    fi
done

# 8. VERIFY NO CONTRADICTORY CLAIMS
echo
echo "8. VERIFYING NO CONTRADICTORY CLAIMS..."
CONTRADICTION_ERRORS=0

# Check for performance claims without benchmarks (excluding targets, requirements, and appropriate contextual references)
UNVERIFIED_PERF_CLAIMS=$(grep -l "<1ms\|sub-millisecond" *.md 2>/dev/null | xargs grep -L "Target\|to be measured\|requirement" 2>/dev/null | grep -v "DOCUMENTATION_CLEANUP_PLAN\|docs/organized/performance\|archive" | wc -l)
if [ "$UNVERIFIED_PERF_CLAIMS" -gt 0 ]; then
    report_error "Performance claims found without benchmark verification"
    CONTRADICTION_ERRORS=$((CONTRADICTION_ERRORS + 1))
fi

# Check for foolproof claims (excluding appropriate contextual references)
OVERCONFIDENT_CLAIMS=$(grep -l "foolproof\|bulletproof" *.md 2>/dev/null | grep -v "HONEST_ORGANIZATIONAL_ASSESSMENT\|docs/reports\|docs/archive\|tools/validation/refactoring_plan" | wc -l)
if [ "$OVERCONFIDENT_CLAIMS" -gt 0 ]; then
    report_error "Overconfident claims found (foolproof/bulletproof)"
    CONTRADICTION_ERRORS=$((CONTRADICTION_ERRORS + 1))
fi

if [ $CONTRADICTION_ERRORS -eq 0 ]; then
    report_success "No contradictory claims detected"
fi

# FINAL REPORT
echo
echo "=== VERIFICATION SUMMARY ==="
if [ $error_count -eq 0 ]; then
    echo -e "${GREEN}✓ ALL VERIFICATIONS PASSED${NC}"
    echo "Foundation reliability: ACCEPTABLE for Week 4 progression"
    exit 0
else
    echo -e "${RED}✗ $error_count ERRORS DETECTED${NC}"
    echo "Foundation reliability: INSUFFICIENT for Week 4 progression"
    echo
    echo "REQUIRED ACTIONS:"
    echo "1. Fix all detected errors"
    echo "2. Re-run verification script"
    echo "3. Do not proceed with Week 4 until all verifications pass"
    exit 1
fi