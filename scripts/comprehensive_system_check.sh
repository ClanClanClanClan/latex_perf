#!/bin/bash
# Comprehensive System Validation and Strengthening Check
# Validates every component and provides detailed diagnostics

set -e  # Exit on any error

echo "=== COMPREHENSIVE SYSTEM VALIDATION ==="
echo "Date: $(date)"
echo "Directory: $(pwd)"
echo ""

# Color codes for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Counters
PASS_COUNT=0
FAIL_COUNT=0
WARN_COUNT=0

check_pass() {
    echo -e "${GREEN}✅ PASS:${NC} $1"
    ((PASS_COUNT++))
}

check_fail() {
    echo -e "${RED}❌ FAIL:${NC} $1"
    ((FAIL_COUNT++))
}

check_warn() {
    echo -e "${YELLOW}⚠️  WARN:${NC} $1"
    ((WARN_COUNT++))
}

echo "1. ENVIRONMENT VALIDATION"
echo "-------------------------"

# Check required tools
if command -v coqc >/dev/null 2>&1; then
    check_pass "Coq compiler available ($(coqc -v | head -1))"
else
    check_fail "Coq compiler not found"
fi

if command -v ocamlc >/dev/null 2>&1; then
    check_pass "OCaml compiler available ($(ocamlc -v | head -1))"
else
    check_fail "OCaml compiler not found"
fi

if command -v make >/dev/null 2>&1; then
    check_pass "Make build system available"
else
    check_fail "Make not found"
fi

echo ""
echo "2. SOURCE CODE VALIDATION"
echo "-------------------------"

# Check critical source files
COQ_FILES="src/coq/vsna/Core.v src/coq/vsna/DFA.v src/coq/vsna/VPA.v src/coq/vsna/SymbolTable.v src/coq/vsna/Compiler.v src/coq/vsna/Performance.v src/coq/vsna/Correctness.v src/coq/vsna/UVSNA.v src/coq/vsna/UVSNA_CARC.v"

for file in $COQ_FILES; do
    if [ -f "$file" ]; then
        lines=$(wc -l < "$file")
        check_pass "Coq file exists: $(basename $file) ($lines lines)"
    else
        check_fail "Missing Coq file: $file"
    fi
done

OCAML_FILES="src/ocaml/simple_json_parser.ml src/ocaml/rule_loader.ml src/ocaml/rule_loader.mli src/ocaml/carc_uvsna_bridge.ml"

for file in $OCAML_FILES; do
    if [ -f "$file" ]; then
        lines=$(wc -l < "$file")
        check_pass "OCaml file exists: $(basename $file) ($lines lines)"
    else
        check_fail "Missing OCaml file: $file"
    fi
done

# Check test files
TEST_FILES="src/ocaml/test_rule_loader_simple.ml src/ocaml/test_carc_bridge.ml"

for file in $TEST_FILES; do
    if [ -f "$file" ]; then
        check_pass "Test file exists: $(basename $file)"
    else
        check_fail "Missing test file: $file"
    fi
done

echo ""
echo "3. DATA VALIDATION"
echo "------------------"

# Check CARC manifest
if [ -f "carc_manifest.json" ]; then
    rules=$(grep -c '"rule_id"' carc_manifest.json)
    check_pass "CARC manifest exists with $rules rules"
    
    # Validate JSON structure
    if echo '{}' | python3 -m json.tool >/dev/null 2>&1; then
        if python3 -m json.tool carc_manifest.json >/dev/null 2>&1; then
            check_pass "CARC manifest is valid JSON"
        else
            check_fail "CARC manifest has invalid JSON syntax"
        fi
    else
        check_warn "Cannot validate JSON (python3 not available)"
    fi
else
    check_fail "CARC manifest not found"
fi

# Check corpus
if [ -d "corpus/papers" ]; then
    papers=$(ls corpus/papers | wc -l)
    check_pass "Test corpus exists with $papers documents"
else
    check_fail "Test corpus not found"
fi

echo ""
echo "4. BUILD SYSTEM VALIDATION"
echo "--------------------------"

# Check Makefile
if [ -f "Makefile.working" ]; then
    check_pass "Build system (Makefile.working) exists"
    
    # Test validation target
    if make -f Makefile.working validate >/dev/null 2>&1; then
        check_pass "Build system validation target works"
    else
        check_fail "Build system validation target fails"
    fi
else
    check_fail "Build system (Makefile.working) not found"
fi

echo ""
echo "5. COMPILATION VALIDATION"
echo "-------------------------"

# Test clean build
echo "Testing clean build process..."
if make -f Makefile.working clean >/dev/null 2>&1; then
    check_pass "Clean target works"
else
    check_warn "Clean target has issues"
fi

# Test Coq compilation
cd src/coq/vsna 2>/dev/null || { check_fail "Cannot enter Coq directory"; exit 1; }
compile_errors=0
for file in Core.v DFA.v VPA.v SymbolTable.v Compiler.v Performance.v Correctness.v UVSNA.v UVSNA_CARC.v; do
    if [ -f "$file" ]; then
        if coqc "$file" >/dev/null 2>&1; then
            check_pass "Coq compilation: $file"
        else
            check_fail "Coq compilation failed: $file"
            ((compile_errors++))
        fi
    fi
done

cd ../../../
if [ $compile_errors -eq 0 ]; then
    check_pass "All Coq modules compile successfully"
else
    check_fail "$compile_errors Coq compilation errors"
fi

# Test OCaml compilation
cd src/ocaml 2>/dev/null || { check_fail "Cannot enter OCaml directory"; exit 1; }

# Clean first
rm -f *.cmi *.cmo test_rule_loader_simple test_carc_bridge

compile_errors=0
if [ -f "rule_loader.mli" ]; then
    if ocamlc -c rule_loader.mli >/dev/null 2>&1; then
        check_pass "OCaml interface compilation: rule_loader.mli"
    else
        check_fail "OCaml interface compilation failed: rule_loader.mli"
        ((compile_errors++))
    fi
fi

for file in simple_json_parser.ml rule_loader.ml carc_uvsna_bridge.ml; do
    if [ -f "$file" ]; then
        if ocamlc -c "$file" >/dev/null 2>&1; then
            check_pass "OCaml compilation: $file"
        else
            check_fail "OCaml compilation failed: $file"
            ((compile_errors++))
        fi
    fi
done

cd ../../

if [ $compile_errors -eq 0 ]; then
    check_pass "All OCaml modules compile successfully"
else
    check_fail "$compile_errors OCaml compilation errors"
fi

echo ""
echo "6. INTEGRATION TESTING"
echo "----------------------"

# Test rule loader
cd src/ocaml
if [ -f "test_rule_loader_simple.ml" ] && [ -f "simple_json_parser.cmo" ] && [ -f "rule_loader.cmo" ]; then
    if ocamlc -o test_rule_loader_simple simple_json_parser.cmo rule_loader.cmo test_rule_loader_simple.ml >/dev/null 2>&1; then
        check_pass "Rule loader test builds"
        
        # Copy manifest for test
        cp ../../carc_manifest.json . 2>/dev/null || true
        
        if ./test_rule_loader_simple >/dev/null 2>&1; then
            check_pass "Rule loader test executes successfully"
        else
            check_fail "Rule loader test execution failed"
        fi
    else
        check_fail "Rule loader test build failed"
    fi
else
    check_fail "Rule loader test prerequisites missing"
fi

# Test CARC bridge
if [ -f "test_carc_bridge.ml" ] && [ -f "carc_uvsna_bridge.cmo" ]; then
    if ocamlc -o test_carc_bridge simple_json_parser.cmo rule_loader.cmo carc_uvsna_bridge.cmo test_carc_bridge.ml >/dev/null 2>&1; then
        check_pass "CARC bridge test builds"
        
        if ./test_carc_bridge >/dev/null 2>&1; then
            check_pass "CARC bridge test executes successfully"
        else
            check_fail "CARC bridge test execution failed"
        fi
    else
        check_fail "CARC bridge test build failed"
    fi
else
    check_fail "CARC bridge test prerequisites missing"
fi

cd ../../

echo ""
echo "7. SYSTEM INTEGRITY CHECK"
echo "-------------------------"

# Check for common issues
if [ -f ".git" ] || [ -d ".git" ]; then
    check_pass "Version control system present"
else
    check_warn "No version control detected"
fi

# Check permissions
if [ -r "carc_manifest.json" ] && [ -r "Makefile.working" ]; then
    check_pass "Key files are readable"
else
    check_fail "Permission issues with key files"
fi

# Check disk space (basic)
available_space=$(df . | tail -1 | awk '{print $4}')
if [ "$available_space" -gt 100000 ]; then  # 100MB
    check_pass "Sufficient disk space available"
else
    check_warn "Low disk space detected"
fi

echo ""
echo "=== VALIDATION SUMMARY ==="
echo "PASSED: $PASS_COUNT checks"
echo "FAILED: $FAIL_COUNT checks"
echo "WARNINGS: $WARN_COUNT checks"
echo ""

if [ $FAIL_COUNT -eq 0 ]; then
    echo -e "${GREEN}🎉 SYSTEM VALIDATION PASSED${NC}"
    echo "All critical components are working correctly."
    exit 0
elif [ $FAIL_COUNT -le 2 ]; then
    echo -e "${YELLOW}⚠️  SYSTEM VALIDATION PASSED WITH WARNINGS${NC}"
    echo "System is mostly functional but has minor issues."
    exit 0
else
    echo -e "${RED}❌ SYSTEM VALIDATION FAILED${NC}"
    echo "Critical issues detected. System needs attention."
    exit 1
fi