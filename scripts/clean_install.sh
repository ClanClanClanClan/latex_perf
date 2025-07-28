#!/bin/bash
# Clean Installation Script for LaTeX Perfectionist v24

echo "🧹 CLEAN INSTALL: LaTeX Perfectionist v24"
echo "=========================================="

# Step 1: Clean everything
echo "Step 1: Cleaning all build artifacts..."
find . -type f \( -name "*.vo" -o -name "*.vok" -o -name "*.vos" -o -name "*.glob" -o -name "*.aux" -o -name "Makefile*" \) -delete
rm -rf build/
echo "✅ Clean complete"

# Step 2: Verify Coq installation
echo "Step 2: Verifying Coq installation..."
if ! command -v coqc &> /dev/null; then
    echo "❌ ERROR: coqc not found. Please install Coq first."
    echo "   macOS: brew install coq"
    echo "   Ubuntu: apt-get install coq"
    exit 1
fi

COQ_VERSION=$(coqc --version | head -1)
echo "✅ Found: $COQ_VERSION"

# Step 3: Create proper _CoqProject
echo "Step 3: Creating _CoqProject with correct paths..."
cat > _CoqProject << 'EOF'
-R . Top
-arg -w -arg -notation-overridden
-arg -w -arg -redundant-canonical-projection

# Core layer (must be built first)
core/LatexCatcodes.v
core/LatexLexer.v

# Validation framework  
ValidationTypes.v

# Enhanced expander (depends on above)
core/LatexExpanderEnhanced.v

# Tests (minimal set for verification)
test_clean_install.v
EOF
echo "✅ _CoqProject created"

# Step 4: Create minimal verification test
echo "Step 4: Creating verification test..."
cat > test_clean_install.v << 'EOF'
Require Import String.
Require Import List.
Import ListNotations.
Require Import LatexLexer.
Require Import LatexExpanderEnhanced.
Open Scope string_scope.

(** CLEAN INSTALL VERIFICATION TEST **)

(** Test 1: Built-in macro works **)
Example builtin_test : 
  fst (expand_document_with_def [TCommand "LaTeX"]) = [TText "LaTeX"].
Proof. vm_compute. reflexivity. Qed.

(** Test 2: \def parsing and substitution works **)
Example def_test :
  fst (expand_document_with_def [
    TCommand "def"; TCommand "test"; TText "#"; TText "1"; 
    TBeginGroup; TText "Result:"; TText "#"; TText "1"; TEndGroup;
    TCommand "test"; TBeginGroup; TText "hello"; TEndGroup
  ]) = [TText "Result:"; TText "hello"].
Proof. vm_compute. reflexivity. Qed.

(** Test 3: Multiple parameters work **)
Example multi_param_test :
  fst (expand_document_with_def [
    TCommand "def"; TCommand "add"; TText "#"; TText "1"; TText "#"; TText "2"; 
    TBeginGroup; TText "#"; TText "1"; TText "+"; TText "#"; TText "2"; TEndGroup;
    TCommand "add"; TBeginGroup; TText "x"; TEndGroup; TBeginGroup; TText "y"; TEndGroup
  ]) = [TText "x"; TText "+"; TText "y"].
Proof. vm_compute. reflexivity. Qed.

(** SUCCESS: Clean install verification passed **)
Definition CLEAN_INSTALL_SUCCESS : string := 
  "✅ VERIFIED: Core L1 expander functionality working correctly".
EOF
echo "✅ Verification test created"

# Step 5: Build everything
echo "Step 5: Building with proper dependencies..."
coq_makefile -f _CoqProject -o Makefile
if [ $? -ne 0 ]; then
    echo "❌ ERROR: Failed to generate Makefile"
    exit 1
fi

echo "Building core components..."
make core/LatexCatcodes.vo || { echo "❌ Failed to build LatexCatcodes"; exit 1; }
make core/LatexLexer.vo || { echo "❌ Failed to build LatexLexer"; exit 1; }
make ValidationTypes.vo || { echo "❌ Failed to build ValidationTypes"; exit 1; }
make core/LatexExpanderEnhanced.vo || { echo "❌ Failed to build LatexExpanderEnhanced"; exit 1; }

echo "Building verification test..."
make test_clean_install.vo || { echo "❌ Failed to build verification test"; exit 1; }

# Step 6: Verification
echo "Step 6: Running verification..."
echo "✅ All components built successfully!"
echo "✅ Verification test passed!"

echo ""
echo "🎉 CLEAN INSTALL COMPLETE!"
echo "=========================="
echo "Core functionality verified:"
echo "  ✅ Built-in macros"
echo "  ✅ \\def parsing"  
echo "  ✅ Parameter substitution"
echo "  ✅ Multiple parameters"
echo ""
echo "Next steps:"
echo "  1. Run comprehensive tests: make all"
echo "  2. Add more test files to _CoqProject as needed"
echo "  3. Build additional features"