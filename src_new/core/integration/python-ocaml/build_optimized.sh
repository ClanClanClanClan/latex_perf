#!/bin/bash
# Build optimized native tokenizer for LaTeX Perfectionist v24-R3

echo "🚀 Building optimized native tokenizer..."

# Clean previous builds
rm -f file_tokenizer_native *.cmx *.cmi *.o

# Compile with maximum optimizations
echo "Compiling lexer_extracted.ml..."
ocamlopt -O3 -c lexer_extracted.ml

echo "Compiling file_tokenizer_optimized.ml..."
ocamlopt -O3 -o file_tokenizer_native lexer_extracted.cmx file_tokenizer_optimized.ml

echo "✅ Native tokenizer built: file_tokenizer_native"

# Make it executable
chmod +x file_tokenizer_native

# Test it exists and works
if [ -f file_tokenizer_native ]; then
    echo "Build successful!"
    ls -la file_tokenizer_native
else
    echo "❌ Build failed!"
    exit 1
fi