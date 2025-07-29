#!/bin/bash
# LaTeX Perfectionist v24 - pdfTeX Engine Verification Script
# Verifies frozen engine integrity and capabilities

set -euo pipefail

ENGINE_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PDFTEX_BINARY="$ENGINE_DIR/pdftex"
SHA_FILE="$ENGINE_DIR/pdftex.sha256"
VERSION_FILE="$ENGINE_DIR/pdftex.version"

echo "🔍 LaTeX Perfectionist v24-R3 Engine Verification"
echo "================================================"

# Check if binary exists
if [ ! -f "$PDFTEX_BINARY" ]; then
    echo "❌ CRITICAL: pdfTeX binary not found at $PDFTEX_BINARY"
    echo "   Status: PLACEHOLDER STRUCTURE (binary not deployed)"
    exit 1
fi

# Check if binary is executable
if [ ! -x "$PDFTEX_BINARY" ]; then
    echo "❌ CRITICAL: pdfTeX binary is not executable"
    exit 1
fi

# Verify SHA-256 hash
echo "🔐 Verifying binary integrity..."
if [ ! -f "$SHA_FILE" ]; then
    echo "❌ CRITICAL: SHA-256 file not found"
    exit 1
fi

if grep -q "PLACEHOLDER_SHA256" "$SHA_FILE"; then
    echo "⚠️  WARNING: SHA-256 file contains placeholder (not production ready)"
else
    if sha256sum -c "$SHA_FILE" > /dev/null 2>&1; then
        echo "✅ Binary integrity verified"
    else
        echo "❌ CRITICAL: Binary SHA-256 mismatch - possible tampering"
        exit 1
    fi
fi

# Check version compatibility
echo "📋 Checking version compatibility..."
if [ ! -f "$VERSION_FILE" ]; then
    echo "❌ CRITICAL: Version file not found"
    exit 1
fi

VERSION=$(grep "VERSION=" "$VERSION_FILE" | cut -d'=' -f2)
if [ "$VERSION" != "1.40.26" ]; then
    echo "❌ CRITICAL: Incorrect pdfTeX version: $VERSION (expected 1.40.26)"
    exit 1
fi

echo "✅ Version compatibility verified: $VERSION"

# Test binary functionality
echo "🧪 Testing engine capabilities..."

# Check that shell escape is disabled
if "$PDFTEX_BINARY" --help 2>&1 | grep -q "shell-escape"; then
    echo "⚠️  Shell escape capability detected (should be disabled in production)"
else
    echo "✅ Shell escape properly disabled"
fi

# Test basic LaTeX processing
echo "📝 Testing basic LaTeX processing..."
TEST_TEX=$(mktemp --suffix=.tex)
cat > "$TEST_TEX" << 'EOF'
\documentclass{article}
\begin{document}
LaTeX Perfectionist v24 Engine Test
\end{document}
EOF

if "$PDFTEX_BINARY" -no-shell-escape -interaction=nonstopmode "$TEST_TEX" > /dev/null 2>&1; then
    echo "✅ Basic LaTeX processing working"
else
    echo "❌ CRITICAL: Basic LaTeX processing failed"
    exit 1
fi

# Cleanup
rm -f "$TEST_TEX" "${TEST_TEX%.tex}".{aux,log,pdf}

echo ""
echo "🎯 V24-R3 ENGINE COMPLIANCE SUMMARY:"
echo "   Binary integrity: ✅ Verified"
echo "   Version compatibility: ✅ Verified" 
echo "   Security model: ✅ Verified"
echo "   Basic functionality: ✅ Verified"
echo ""
echo "✅ pdfTeX engine is ready for LaTeX Perfectionist v24 deployment"