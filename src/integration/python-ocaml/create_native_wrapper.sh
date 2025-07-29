#!/bin/bash
# Create a simple native tokenizer by compiling the existing file_tokenizer.ml

echo "🚀 Creating native tokenizer wrapper..."

# Method 1: Just compile the whole thing as a single unit
echo "Creating combined tokenizer file..."

# Combine lexer_extracted.ml and file_tokenizer.ml (without the #use directive)
cat > file_tokenizer_combined.ml << 'EOF'
(* Combined lexer and tokenizer for native compilation *)
EOF

# Add the lexer_extracted.ml content
cat lexer_extracted.ml >> file_tokenizer_combined.ml

# Add the tokenizer logic without the #use directive
echo "" >> file_tokenizer_combined.ml
tail -n +4 file_tokenizer.ml >> file_tokenizer_combined.ml

# Compile to native
echo "Compiling combined tokenizer..."
ocamlopt -O3 -o file_tokenizer_native file_tokenizer_combined.ml

if [ -f file_tokenizer_native ]; then
    echo "✅ Native tokenizer built successfully!"
    ls -la file_tokenizer_native
    echo "File size: $(stat -f%z file_tokenizer_native) bytes"
else
    echo "❌ Build failed!"
    exit 1
fi