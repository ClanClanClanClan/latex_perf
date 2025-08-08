#!/bin/bash
# Performance test runner for LaTeX Perfectionist v25
set -e

echo "🚀 Running Performance Tests"
echo "============================"

eval $(opam env)

cd test/performance/

echo "📊 Running bulletproof 1MB test..."
ocamlopt -o BULLETPROOF_1MB_TEST BULLETPROOF_1MB_TEST.ml && ./BULLETPROOF_1MB_TEST

echo "📈 Running comprehensive performance test..."
ocamlopt -o COMPREHENSIVE_PERFORMANCE_TEST COMPREHENSIVE_PERFORMANCE_TEST.ml && ./COMPREHENSIVE_PERFORMANCE_TEST

echo "✅ Performance tests complete!"
